(* A single acceptance policy for every speculative rewrite, including cache
   hits. Always measure and check the expression in its original context. *)

open Greysynth_utils.Utils
open Config

let checked = ref 0
let proved = ref 0
let sample_rejections = ref 0
let disproved = ref 0
let inconclusive = ref 0

(* Keep validation inputs independent of the synthesis/OES sample bank. *)
let holdout = ref (Sample_evaluator.make 32)
let proofs : (Sexpr.Expr.t * Sexpr.Expr.t, equiv_t) Hashtbl.t =
  Hashtbl.create 128

let reset () =
  List.iter (fun counter -> counter := 0)
    [ checked; proved; sample_rejections; disproved; inconclusive ];
  holdout := Sample_evaluator.make 32;
  Hashtbl.clear proofs

let accepts ~pass original candidate =
  if
    Sexpr.Expr.sizeof original <> Sexpr.Expr.sizeof candidate
    || size_of_expr candidate >= size_of_expr original
  then false
  else (
    check_timeout ();
    incr checked;
    let agrees bank =
      bank.Sample_evaluator.node_to_outhash original
      = bank.Sample_evaluator.node_to_outhash candidate
    in
    let samples_match =
      try agrees !evaluator && agrees !holdout
      with
      | Timeout_exception -> raise Timeout_exception
      | _ -> false
    in
    if not samples_match then (
      incr sample_rejections;
      Logging._log_warn pass "discarding a rewrite that fails validation samples";
      false)
    else if not !c_reject_non_equiv_simplifications then true
    else
      let verdict =
        match Hashtbl.find_opt proofs (original, candidate) with
        | Some verdict -> verdict
        | None ->
            let verdict, _, _ =
              are_equivalent original candidate (Some !c_equiv_timeout)
            in
            (match verdict with
            | Yes | No -> Hashtbl.replace proofs (original, candidate) verdict
            | Unknown | Timeout | Disabled -> ());
            verdict
      in
      check_timeout ();
      match verdict with
      | Yes ->
          incr proved;
          true
      | No ->
          incr disproved;
          Logging._log_warn pass "discarding a non-equivalent rewrite";
          false
      | Unknown | Timeout | Disabled ->
          incr inconclusive;
          false)
