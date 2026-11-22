(* A single acceptance policy for every speculative rewrite, including cache
   hits. Always measure and check the expression in its original context. *)

open Greysynth_utils.Utils
open Config

let checked = ref 0
let proved = ref 0
let sample_rejections = ref 0
let disproved = ref 0
let inconclusive = ref 0

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
let proofs : (Sexpr.Expr.t * Sexpr.Expr.t, equiv_t) Hashtbl.t =
  Hashtbl.create 128

(* Unknown and timeout results are reusable only for an equal or smaller
   budget. A larger budget is a meaningful retry; repeating the same query is
   just lost simplification time. Entries inserted directly by tests or API
   users without a budget remain authoritative. *)
let proof_budgets : (Sexpr.Expr.t * Sexpr.Expr.t, float) Hashtbl.t =
  Hashtbl.create 128

let reset () =
  List.iter (fun counter -> counter := 0)
    [ checked; proved; sample_rejections; disproved; inconclusive ];
  holdout := Sample_evaluator.make 32;
  Hashtbl.clear proofs;
  Hashtbl.clear proof_budgets;
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

let accepts_compositional ~pass ~equalities original candidate =
  if
    Sexpr.Expr.sizeof original <> Sexpr.Expr.sizeof candidate
    || size_of_expr candidate >= size_of_expr original
  then false
  else (
    check_timeout ();
    incr checked;
    if not (samples_agree original candidate) then (
      incr sample_rejections;
      false)
    else
      let proof = Rewrite_proof.create original in
      List.iter (fun (left, right) -> Rewrite_proof.record proof ~pass left right) equalities;
      let certificate = Rewrite_proof.finish proof candidate in
      let report =
        Rewrite_proof.verify ~timeouts:[ float_of_int !c_equiv_timeout ]
          ~original ~candidate certificate
      in
      let open Yojson.Basic.Util in
      match member "verification" report |> to_string_option with
      | Some "proved_compositional" ->
          incr proved;
          Option.iter
            (fun journal ->
              List.iter
                (fun (left, right) -> Rewrite_proof.record journal ~pass left right)
                equalities)
            !journal;
          true
      | _ ->
          (match member "equiv" report |> to_string_option with
          | Some "no" -> incr disproved
          | _ -> incr inconclusive);
          false)

let accepts ~pass original candidate =
  if
    Sexpr.Expr.sizeof original <> Sexpr.Expr.sizeof candidate
    || size_of_expr candidate >= size_of_expr original
  then false
  else (
    check_timeout ();
    incr checked;
    if not (samples_agree original candidate) then (
      incr sample_rejections;
      Logging._log_warn pass "discarding a rewrite that fails validation samples";
      false)
    else if not !c_reject_non_equiv_simplifications then (
      record ~pass original candidate;
      true)
    else
      let key = (original, candidate) in
      let budget = float_of_int !c_equiv_timeout in
      let cached =
        match Hashtbl.find_opt proofs key with
        | Some (Yes | No as verdict) -> Some verdict
        | Some (Unknown | Timeout | Disabled as verdict) ->
            let attempted =
              Option.value (Hashtbl.find_opt proof_budgets key) ~default:Float.infinity
            in
            if attempted >= budget then Some verdict else None
        | None -> None
      in
      let verdict =
        match cached with
        | Some verdict -> verdict
        | None ->
            let verdict, _ = Rewrite_proof.prove_equality ~timeout:budget original candidate in
            Hashtbl.replace proofs key verdict;
            Hashtbl.replace proof_budgets key budget;
            verdict
      in
      check_timeout ();
      match verdict with
      | Yes ->
          incr proved;
          record ~pass original candidate;
          true
      | No ->
          incr disproved;
          Logging._log_warn pass "discarding a non-equivalent rewrite";
          false
      | Unknown | Timeout | Disabled ->
          incr inconclusive;
          false)
