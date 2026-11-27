module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var width name = E.var name width name
let add = E.binary E.Plus
let mul = E.binary E.Mul
let band = E.binary E.And
let bxor = E.binary E.Xor

let check label original expected =
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original (); R.start_recording original;
  let result = N.dag_bottom_up_simplify ~minimal:true original |> N.run in
  let verdict, _, _ = U.are_equivalent result expected (Some 2) in
  require (verdict = U.Yes && U.size_of_expr result <= U.size_of_expr expected)
    (label ^ ": unexpected result");
  let certificate = P.finish (Option.get !(R.journal)) result in
  require
    (J.member "verification" (P.verify ~original ~candidate:result certificate)
     = `String "proved_compositional")
    (label ^ ": certificate did not replay")

let check_semilinear label original expected =
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original (); R.start_recording original;
  require
    (R.accepts_compositional ~pass:label ~equalities:[]
       ~semilinear_mba_equalities:[ original, expected ] original expected)
    (label ^ ": semi-linear kernel rejected identity");
  let certificate = P.finish (Option.get !(R.journal)) expected in
  require
    (J.member "verification" (P.verify ~original ~candidate:expected certificate)
     = `String "proved_compositional")
    (label ^ ": certificate did not replay")

let () =
  let a0 = var 64 "oa0" and a1 = var 64 "oa1" and a2 = var 64 "oa2"
  and b0 = var 64 "ob0" and b1 = var 64 "ob1" and b2 = var 64 "ob2" in
  let a = add (mul a0 a1) a2 and b = add (E.binary E.Udiv b0 (c 64 3)) (mul b1 b2) in
  check "opaque carry decomposition"
    (add (E.binary E.Lsl (band a b) (c 64 1)) (bxor a b))
    (add a b);

  let x = var 64 "slice36" in
  let low = E.unary (E.Uext 63) (E.restrict ~lo:0 ~hi:0 x) in
  check_semilinear "semi-linear low slice"
    (add (E.binary E.Lsl low (c 64 1)) (bxor (c 64 1) x))
    (add x (c 64 1));

  check "abstract low shifted slice"
    (E.restrict ~lo:0 ~hi:3 (E.binary E.Lsl x (c 64 5)))
    (c 4 0);

  let scaled = mul (c 64 7) x in
  check "complemented scaled term"
    (add (c 64 (-1)) (mul (c 64 (-7)) x))
    (E.unary E.Not scaled);
  Printf.printf "round36_test: opaque shifts, slices and complements passed\n"
