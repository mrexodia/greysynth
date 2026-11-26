module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var width name = E.var name width name
let add = E.binary E.Plus
let mul = E.binary E.Mul
let bor = E.binary E.Or

let simplify original expected =
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original ();
  let result = N.run (N.dag_bottom_up_simplify original) in
  let verdict, _, _ = U.are_equivalent result expected (Some 2) in
  require (verdict = U.Yes && U.size_of_expr result <= U.size_of_expr expected)
    "Round-32 simplification failed"

let () =
  let x = var 64 "r32_x" in
  simplify (E.binary E.Minus (E.unary E.Minus x) (c 64 1)) (E.unary E.Not x);
  simplify (add (E.unary E.Minus x) (c 64 (-1))) (E.unary E.Not x);
  simplify (E.binary E.Minus (c 64 (-1)) x) (E.unary E.Not x);
  simplify (E.unary E.Minus (add x (c 64 1))) (E.unary E.Not x);

  let a = var 16 "r32_a" and b = var 16 "r32_b" and d = var 16 "r32_d" in
  let expanded_or =
    E.unary E.Not
      (E.binary E.And (E.unary E.Not a) (E.unary E.Not (bor b d)))
  in
  let shifted_or = add (mul (c 16 5) expanded_or) (c 16 (-1)) in
  let compact_or = add (mul (c 16 5) (bor a (bor b d))) (c 16 (-1)) in
  let verdict, _, _ = U.are_equivalent shifted_or compact_or (Some 2) in
  require (verdict = U.Yes) "dual-polarity Boolean identity failed";

  let wide = var 64 "slice_x" in
  let sliced_not = E.unary (E.Uext 63)
      (E.restrict ~lo:0 ~hi:0 (E.unary E.Not wide)) in
  let sliced = E.unary (E.Uext 63) (E.restrict ~lo:0 ~hi:0 wide) in
  let expected = E.binary E.Minus (c 64 1) sliced in
  let verdict, _, _ = U.are_equivalent sliced_not expected (Some 2) in
  require (verdict = U.Yes) "complementary low-slice identity failed";
  Printf.printf "round32_test: complement, polarity and slice identities passed\n"
