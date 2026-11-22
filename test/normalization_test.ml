(* Candidate generation is deterministic; every accepted replacement still
   has to satisfy the common sampling and SMT policy. *)
module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var width name = E.var name width name
let plus = E.binary E.Plus
let minus = E.binary E.Minus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor

let reset ?(strict = true) () =
  Random.init 42;
  C.evaluator := Sample_evaluator.make 100;
  C.c_nb_samples := 100;
  C.c_reject_non_equiv_simplifications := strict;
  C.c_equiv_timeout := 5;
  C.g_total_timeout := 0.;
  C.g_has_timedout := false;
  R.reset ()

let test_fail_closed () =
  reset ();
  let x = var 32 "x" in
  let original = plus x (c 32 0) in
  Hashtbl.replace R.proofs (original, x) U.Unknown;
  let result = N.run original in
  require (E.is_equal result original) "normalizer accepted an unknown proof";
  require (!(R.inconclusive) > 0) "normalizer bypassed the proof boundary"

let test_metric_minimum () =
  reset ();
  let original = E.unary (E.Sext 24) (E.restrict ~lo:8 ~hi:15 (var 32 "x")) in
  let result = N.run original in
  require (U.size_of_expr original = 1) "cast/extract metric changed";
  require (E.is_equal original result) "normalizer rewrote a metric-minimum input";
  require (!(R.checked) = 0) "minimum input triggered a speculative rewrite"

let test_partial_timeout () =
  reset ~strict:false ();
  let x = var 32 "x" and y = var 32 "y" in
  let left = plus x (c 32 0) and right = plus y (c 32 0) in
  let original = plus left right in
  let bank = !(C.evaluator) in
  C.evaluator :=
    { bank with node_to_outhash = (fun node ->
        if E.is_equal node right then raise C.Timeout_exception;
        bank.node_to_outhash node) };
  let result = N.run original in
  require !(C.g_has_timedout) "normalizer did not record its timeout";
  require (E.is_equal result (plus x right))
    "normalizer timeout discarded a completed child rewrite"

let prove_shrinks name original maximum =
  reset ();
  let result = N.run original in
  require (U.size_of_expr result <= maximum)
    (Printf.sprintf "%s: expected size <= %d, got %d from %d" name maximum
       (U.size_of_expr result) (U.size_of_expr original));
  require (!(R.proved) > 0) (name ^ ": no replacement was proved");
  let verdict, _, _ = U.are_equivalent original result (Some 5) in
  require (verdict = U.Yes) (name ^ ": independent whole-expression proof failed")

let test_peepholes () =
  let x = var 8 "x" and y = var 8 "y" in
  List.iter (fun (name, original, maximum) -> prove_shrinks name original maximum)
    [ "low mask", band x (c 8 31), 1;
      "logical shift", E.binary E.Lsr x (c 8 3), 1;
      "arithmetic overshift", E.binary E.Asr x (c 8 255), 1;
      "unsigned power-of-two quotient", E.binary E.Udiv x (c 8 8), 1;
      "unsigned power-of-two remainder", E.binary E.Umod x (c 8 8), 1;
      "zero divisor", E.binary E.Udiv x (c 8 0), 1;
      "zero remainder divisor", E.binary E.Umod x (c 8 0), 1;
      "shifted divisor", E.binary E.Udiv x (E.binary E.Lsl y (c 8 2)), 3;
      "shifted constant numerator", E.binary E.Udiv (c 8 64)
          (E.binary E.Lsl x (c 8 1)), 3;
      "divisor shift overflow", E.binary E.Udiv x (E.binary E.Lsl y (c 8 8)), 1;
      "adjacent slices", E.binary E.Concat (E.restrict ~lo:4 ~hi:7 x)
          (E.restrict ~lo:0 ~hi:3 x), 1 ]

let test_linear_mba () =
  let x = var 32 "x" and y = var 32 "y" in
  List.iter (fun (name, original, maximum) -> prove_shrinks name original maximum)
    [ "sum of union and intersection", plus (bor x y) (band x y), 3;
      "carry decomposition", plus (bxor x y) (mul (c 32 2) (band x y)), 3;
      "double union", minus (mul (c 32 2) (bor x y)) (bxor x y), 3;
      "negation and offset", minus (E.unary E.Minus x) (c 32 1), 2;
      "scaled MBA", plus (mul (c 32 3) (bor x y))
          (mul (c 32 3) (band x y)), 5;
      "complemented arithmetic", plus (plus (E.unary E.Not (plus x y)) x)
          (plus y (c 32 1)), 1 ]

let test_associative_canonicalization () =
  let x = var 16 "x" and y = var 16 "y" in
  List.iter (fun (name, original, maximum) -> prove_shrinks name original maximum)
    [ "xor cancellation", bxor (bxor x y) x, 1;
      "coefficient collection", plus (plus x x) x, 3;
      "idempotent conjunction", band (band x y) x, 3 ]

let test_nonlinear_is_opaque () =
  reset ();
  let x = var 8 "x" and y = var 8 "y" in
  (* x*x=x for one-bit assignments, but not for arbitrary words. A
     truth-table normalizer must not expand the nonlinear operations. *)
  let original = minus (plus (mul x x) (mul y y)) (plus x y) in
  let result = N.run original in
  let labels = Hashtbl.create 2 in
  Hashtbl.add labels x (c 8 2);
  Hashtbl.add labels y (c 8 0);
  let value = (Sample_evaluator.make 1).eval_label result 0 labels in
  require (Bitvector.equal value (Bitvector.of_int ~size:8 2))
    "one-bit nonlinear coincidence became a word identity";
  let verdict, _, _ = U.are_equivalent original result (Some 5) in
  require (verdict = U.Yes) "opaque nonlinear normalization changed semantics"

let solver_available =
  Option.is_some Libsolver.bitwuzla_cxx
  || Option.is_some Libsolver.bitwuzla_c
  || Option.is_some Libsolver.z3

let () =
  test_fail_closed ();
  test_metric_minimum ();
  test_partial_timeout ();
  print_endline "normalization_test: fail-closed, metric-minimum and partial-timeout checks passed";
  if solver_available then (
    test_peepholes ();
    test_linear_mba ();
    test_associative_canonicalization ();
    test_nonlinear_is_opaque ();
    print_endline "normalization_test: 21 solver-backed normalization regressions passed")
  else if Sys.getenv_opt "GREYSYNTH_REQUIRE_SOLVER" = Some "1" then
    failwith "normalization_test requires an installed SMT solver"
  else print_endline "normalization_test: proof regressions skipped (no solver installed)"
