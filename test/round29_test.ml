module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module K = Greysynth__Known_bits
module S = Greysynth__Synthesis

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var width name = E.var name width name
let add = E.binary E.Plus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor

let () =
  List.iter
    (fun width ->
      let x = var width ("kb_x" ^ string_of_int width)
      and y = var width ("kb_y" ^ string_of_int width) in
      let amount = c width 3 in
      let condition = E.binary E.Ult x (c width 17) in
      let expressions =
        [ E.unary E.Not x; band x y; bor x y; bxor x y; add x y; mul x y;
          E.binary E.Lsl x amount; E.binary E.Lsr x amount;
          E.binary E.Asr x amount; E.unary (E.Uext width) x;
          E.restrict ~lo:1 ~hi:(width - 1) x; E.ite condition x y ]
      in
      List.iteri
        (fun index expression ->
          let known = K.analyze expression in
          let zeros = E.constant (Bitvector.create known.zeros known.width)
          and ones = E.constant (Bitvector.create known.ones known.width) in
          let zero_check = band expression zeros
          and one_check = band expression ones in
          let zero_verdict, _, _ = U.are_equivalent zero_check (c known.width 0) (Some 2)
          and one_verdict, _, _ = U.are_equivalent one_check ones (Some 2) in
          require (zero_verdict = U.Yes && one_verdict = U.Yes)
            (Printf.sprintf "known-bits soundness failed width=%d case=%d" width index))
        expressions)
    [ 8; 16 ];

  let simplify label original expected =
    C.evaluator := Sample_evaluator.make
        ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
    C.g_total_timeout := 0.; C.g_has_timedout := false;
    C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
    R.reset ~original ();
    let result = N.run (N.dag_bottom_up_simplify original) in
    let verdict, _, _ = U.are_equivalent result expected (Some 2) in
    require (verdict = U.Yes && U.size_of_expr result <= U.size_of_expr expected)
      (label ^ ": known-bits simplification failed")
  in
  let x = var 16 "ks_x" and y = var 16 "ks_y" in
  simplify "redundant mask" (band (band x (c 16 0xff)) (c 16 0xfff))
    (band x (c 16 0xff));
  simplify "shift low zeros" (band (E.binary E.Lsl x (c 16 2)) (c 16 3))
    (c 16 0);
  simplify "disjoint addition"
    (add (band x (c 16 0x0f)) (band y (c 16 0xf0)))
    (bor (band x (c 16 0x0f)) (band y (c 16 0xf0)));
  let yes = var 16 "ks_yes" and no = var 16 "ks_no" in
  simplify "known unsigned branch"
    (E.ite (E.binary E.Ult (band x (c 16 0xff)) (c 16 256)) yes no) yes;
  simplify "impossible equality branch"
    (E.ite (E.binary E.Eq (bor x (c 16 1)) (c 16 0)) yes no) no;

  let gx = var 32 "gx" and gy = var 32 "gy" and gz = var 32 "gz" in
  let leaves = Hashtbl.create 3 in
  Hashtbl.add leaves gx gx; Hashtbl.add leaves gy gy; Hashtbl.add leaves gz gz;
  let filtered, filtered_leaves =
    S.filter_dead_stubs (add (mul (bxor gx gx) gy) (add gz (c 32 1))) leaves
  in
  require (Hashtbl.length filtered_leaves <= 1)
    "dead-stub perturbation did not remove cancelled inputs";
  let verdict, _, _ = U.are_equivalent filtered (add gz (c 32 1)) (Some 2) in
  require (verdict = U.Yes) "dead-stub filtering changed semantics";

  C.evaluator := Sample_evaluator.make ~variables:[ "a", 32; "b", 32; "c", 32;
                                                     "d", 32; "e", 32; "f", 32 ] 32;
  let wide = add (add (var 32 "a") (var 32 "b"))
      (add (add (var 32 "c") (var 32 "d")) (add (var 32 "e") (var 32 "f"))) in
  let _, stubs = S.truncate wide 4 in
  require (Hashtbl.length stubs <= 4) "arity-budgeted truncation exceeded four stubs";

  let x8 = var 8 "anf_x" in
  let polynomial = add (mul (c 8 7) x8) (c 8 3) in
  let noisy = add polynomial (E.binary E.Minus (mul x8 x8) (mul x8 x8)) in
  C.evaluator := Sample_evaluator.make ~variables:[ "anf_x", 8 ] ~seed:0 64;
  R.reset ~original:noisy ();
  let recognized = N.probe_low_width_exact U.size_of_expr noisy in
  require (Option.is_some recognized) "8-bit exhaustive recognizer failed";
  let verdict, _, _ = U.are_equivalent (Option.get recognized) polynomial (Some 2) in
  require (verdict = U.Yes) "8-bit recognizer returned wrong candidate";
  Printf.printf "round29_test: known bits, dead stubs, arity budget and low-width recognition passed\n"
