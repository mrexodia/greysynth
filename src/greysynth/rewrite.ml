(* A single acceptance policy for every speculative rewrite, including cache
   hits. Always measure and check the expression in its original context. *)

open Greysynth_utils.Utils
open Config

let checked = ref 0
let proved = ref 0
let sample_rejections = ref 0
let disproved = ref 0
let inconclusive = ref 0
let last_rejection = ref "none"

(* Explicit original-variable assignments learned from concrete SMT
   refutations. Synthesis turns them into contextual cut-label samples. *)
let counterexamples : (string * int * Z.t) list list ref = ref []

let remember_counterexample original model =
  let widths = Hashtbl.create 16 in
  List.iter (fun (name, width) -> Hashtbl.replace widths name width)
    (Sample_evaluator.variables_of_expr original);
  let environment =
    List.filter_map
      (fun (name, value) ->
        Option.map (fun width -> (name, width, value)) (Hashtbl.find_opt widths name))
      model
    |> List.sort compare
  in
  if environment <> [] && not (List.mem environment !counterexamples) then
    counterexamples := environment :: !counterexamples

(* The journal contains obligations, never trusted verdicts. Independent replay
   binds its endpoints and proves enough recorded equalities to connect them. *)
let journal : Rewrite_proof.builder option ref = ref None
let start_recording original = journal := Some (Rewrite_proof.create original)
let record ~pass original candidate =
  Option.iter (fun proof -> Rewrite_proof.record proof ~pass original candidate) !journal
let write_certificate filename result =
  match !journal with
  | None -> failwith "Proof recording was not started"
  | Some proof ->
      let certificate = Rewrite_proof.finish proof result in
      Yojson.Basic.to_file filename certificate;
      let open Yojson.Basic.Util in
      `Assoc [
        "status", `String "recorded_not_replayed";
        "path", `String filename;
        "format", member "format" certificate;
        "nodes", `Int (List.length (to_list (member "nodes" certificate)));
        "equalities", `Int (List.length (to_list (member "equalities" certificate)));
      ]

(* Keep validation inputs independent of the synthesis/OES sample bank. *)
let holdout = ref (Sample_evaluator.make 32)
module ExprPairTbl = Hashtbl.Make (struct
  type t = Sexpr.Expr.t * Sexpr.Expr.t
  let equal (a, b) (c, d) =
    (Sexpr.Expr.is_equal a c && Sexpr.Expr.is_equal b d)
    || (Sexpr.Expr.is_equal a d && Sexpr.Expr.is_equal b c)
  let hash (a, b) = Sexpr.Expr.hash a lxor Sexpr.Expr.hash b
end)

module ExprPairPassTbl = Hashtbl.Make (struct
  type t = Sexpr.Expr.t * Sexpr.Expr.t * string
  let equal (a, b, pass) (c, d, other_pass) =
    String.equal pass other_pass
    && ((Sexpr.Expr.is_equal a c && Sexpr.Expr.is_equal b d)
        || (Sexpr.Expr.is_equal a d && Sexpr.Expr.is_equal b c))
  let hash (a, b, pass) =
    (Sexpr.Expr.hash a lxor Sexpr.Expr.hash b) lxor Hashtbl.hash pass
end)

let proof_key left right = left, right

let proofs : equiv_t ExprPairTbl.t = ExprPairTbl.create 128

(* Unknown and timeout results are reusable only for an equal or smaller
   budget. A larger budget is a meaningful retry; repeating the same query is
   just lost simplification time. Entries inserted directly by tests or API
   users without a budget remain authoritative. *)
let proof_budgets : float ExprPairTbl.t = ExprPairTbl.create 128
let compositional_budgets : float ExprPairPassTbl.t = ExprPairPassTbl.create 128

type cache_checkpoint = {
  cached_proofs : equiv_t ExprPairTbl.t;
  cached_budgets : float ExprPairTbl.t;
  cached_compositional : float ExprPairPassTbl.t;
}

let checkpoint_caches () =
  {
    cached_proofs = ExprPairTbl.copy proofs;
    cached_budgets = ExprPairTbl.copy proof_budgets;
    cached_compositional = ExprPairPassTbl.copy compositional_budgets;
  }

let restore_pair_table target source =
  ExprPairTbl.clear target;
  ExprPairTbl.iter (ExprPairTbl.replace target) source

let restore_pass_table target source =
  ExprPairPassTbl.clear target;
  ExprPairPassTbl.iter (ExprPairPassTbl.replace target) source

let restore_caches checkpoint =
  restore_pair_table proofs checkpoint.cached_proofs;
  restore_pair_table proof_budgets checkpoint.cached_budgets;
  restore_pass_table compositional_budgets checkpoint.cached_compositional

let reset ?original () =
  List.iter (fun counter -> counter := 0)
    [ checked; proved; sample_rejections; disproved; inconclusive ];
  last_rejection := "none";
  holdout :=
    (match original with
    | None -> Sample_evaluator.make ~seed:1 32
    | Some expression ->
        Sample_evaluator.make ~variables:(Sample_evaluator.variables_of_expr expression)
          ~seed:1 32);
  ExprPairTbl.clear proofs;
  ExprPairTbl.clear proof_budgets;
  ExprPairPassTbl.clear compositional_budgets;
  counterexamples := [];
  journal := None

let samples_agree original candidate =
  let agrees bank =
    bank.Sample_evaluator.node_to_outhash original
    = bank.Sample_evaluator.node_to_outhash candidate
  in
  try agrees !evaluator && agrees !holdout
  with
  | Timeout_exception -> raise Timeout_exception
  | _ -> false

let accepts_compositional ?(ring_equalities = []) ?(poly_equalities = [])
    ?(linear_mba_equalities = []) ?(semilinear_mba_equalities = [])
    ?(timeout = float_of_int !c_equiv_timeout) ~pass ~equalities original candidate =
  let record_equalities () =
    Option.iter
      (fun journal ->
        List.iter
          (fun (left, right) -> Rewrite_proof.record journal ~pass left right)
          equalities;
        List.iter
          (fun (left, right) -> Rewrite_proof.record_ring journal ~pass left right)
          ring_equalities;
        List.iter
          (fun (left, right) -> Rewrite_proof.record_poly journal ~pass left right)
          poly_equalities;
        List.iter
          (fun (left, right) -> Rewrite_proof.record_linear_mba journal ~pass left right)
          linear_mba_equalities;
        List.iter
          (fun (left, right) ->
            Rewrite_proof.record_semilinear_mba journal ~pass left right)
          semilinear_mba_equalities)
      !journal
  in
  if Sexpr.Expr.sizeof original <> Sexpr.Expr.sizeof candidate then (
    last_rejection := "width_mismatch";
    false)
  else if size_of_expr candidate >= size_of_expr original then (
    last_rejection := "not_smaller";
    false)
  else (
    check_timeout ();
    incr checked;
    if not (samples_agree original candidate) then (
      incr sample_rejections;
      last_rejection := "sample_refuted";
      false)
    else if not !c_reject_non_equiv_simplifications then (
      last_rejection := "none";
      record_equalities ();
      true)
    else
      let key = proof_key original candidate in
      let remaining =
        if !g_total_timeout <= 0. then infinity
        else !g_total_timeout -. (Unix.gettimeofday () -. !g_start_time)
      in
      let budget = min timeout (max 0.001 remaining) in
      let cached = ExprPairTbl.find_opt proofs key in
      let compositional_key =
        let left, right = key in
        (left, right, pass)
      in
      let attempted =
        Option.value (ExprPairPassTbl.find_opt compositional_budgets compositional_key)
          ~default:0.
      in
      if cached = Some Yes then (
        (* The earlier successful acceptance already recorded its derivation.
           Never attach a new, unchecked set of obligations merely because the
           endpoint equality is cached. *)
        last_rejection := "none";
        incr proved;
        true)
      else if Option.is_some cached && not (ExprPairTbl.mem proof_budgets key) then (
        last_rejection := "smt_inconclusive";
        incr inconclusive;
        false)
      else if ExprPairPassTbl.mem compositional_budgets compositional_key
              && attempted >= budget then (
        last_rejection := "smt_inconclusive";
        incr inconclusive;
        false)
      else
      let proof = Rewrite_proof.create original in
      List.iter (fun (left, right) -> Rewrite_proof.record proof ~pass left right) equalities;
      List.iter
        (fun (left, right) -> Rewrite_proof.record_ring proof ~pass left right)
        ring_equalities;
      List.iter
        (fun (left, right) -> Rewrite_proof.record_poly proof ~pass left right)
        poly_equalities;
      List.iter
        (fun (left, right) -> Rewrite_proof.record_linear_mba proof ~pass left right)
        linear_mba_equalities;
      List.iter
        (fun (left, right) ->
          Rewrite_proof.record_semilinear_mba proof ~pass left right)
        semilinear_mba_equalities;
      let certificate = Rewrite_proof.finish proof candidate in
      let report =
        Rewrite_proof.verify ~timeouts:[ timeout ]
          ~original ~candidate certificate
      in
      let open Yojson.Basic.Util in
      check_timeout ();
      match member "verification" report |> to_string_option with
      | Some "proved_compositional" ->
          incr proved;
          last_rejection := "none";
          ExprPairTbl.replace proofs key Yes;
          ExprPairTbl.replace proof_budgets key budget;
          record_equalities ();
          true
      | _ ->
          (match member "equiv" report |> to_string_option with
          | Some "no" ->
              incr disproved;
              last_rejection := "smt_refuted"
          | _ ->
              incr inconclusive;
              last_rejection := "smt_inconclusive");
          ExprPairPassTbl.replace compositional_budgets compositional_key budget;
          false)

let accepts ?timeout ?(allow_equal_cost = false) ~pass original candidate =
  if Sexpr.Expr.sizeof original <> Sexpr.Expr.sizeof candidate then (
    last_rejection := "width_mismatch";
    false)
  else if size_of_expr candidate > size_of_expr original
          || (not allow_equal_cost
              && size_of_expr candidate = size_of_expr original) then (
    last_rejection := "not_smaller";
    false)
  else (
    check_timeout ();
    incr checked;
    if not (samples_agree original candidate) then (
      incr sample_rejections;
      last_rejection := "sample_refuted";
      Logging._log_warn pass "discarding a rewrite that fails validation samples";
      false)
    else if not !c_reject_non_equiv_simplifications then (
      last_rejection := "none";
      record ~pass original candidate;
      true)
    else
      let key = proof_key original candidate in
      let requested =
        match timeout with
        | None -> float_of_int !c_equiv_timeout
        | Some timeout -> min timeout (float_of_int !c_equiv_timeout)
      in
      let remaining =
        if !g_total_timeout <= 0. then infinity
        else !g_total_timeout -. (Unix.gettimeofday () -. !g_start_time)
      in
      let budget = min requested remaining in
      if budget <= 0.1 then (
        if !g_total_timeout > 0. then g_has_timedout := true;
        incr inconclusive;
        last_rejection := "smt_inconclusive";
        false)
      else
      let cached =
        match ExprPairTbl.find_opt proofs key with
        | Some (Yes | No as verdict) -> Some verdict
        | Some (Unknown | Timeout | Disabled as verdict) ->
            let attempted =
              Option.value (ExprPairTbl.find_opt proof_budgets key) ~default:Float.infinity
            in
            if attempted >= budget then Some verdict else None
        | None -> None
      in
      let cached_success = cached = Some Yes in
      let verdict, model =
        match cached with
        | Some verdict -> (verdict, None)
        | None ->
            let verdict, _, model =
              Rewrite_proof.prove_equality_with_model ~timeout:budget original candidate
            in
            ExprPairTbl.replace proofs key verdict;
            ExprPairTbl.replace proof_budgets key budget;
            (verdict, model)
      in
      check_timeout ();
      match verdict with
      | Yes ->
          incr proved;
          last_rejection := "none";
          if not cached_success then record ~pass original candidate;
          true
      | No ->
          incr disproved;
          last_rejection := "smt_refuted";
          Option.iter (remember_counterexample original) model;
          Logging._log_warn pass "discarding a non-equivalent rewrite";
          false
      | Unknown | Timeout | Disabled ->
          incr inconclusive;
          last_rejection := "smt_inconclusive";
          false)
