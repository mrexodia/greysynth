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
let sub = E.binary E.Minus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor

let () =
  let x = var 64 "mask_x" in
  let sliced = E.unary (E.Uext 63) (E.restrict ~lo:0 ~hi:0 x) in
  (match N.mask_lift_candidate (U.cost_of_expr U.PaperAst) sliced with
  | Some candidate ->
      let verdict, _, _ = U.are_equivalent sliced candidate (Some 2) in
      require (verdict = U.Yes) "uext/restrict mask bridge is unsound"
  | None ->
      let expected = band x (c 64 1) in
      let verdict, _, _ = U.are_equivalent sliced expected (Some 2) in
      require (verdict = U.Yes) "uext/restrict mask identity failed");

  let x = var 32 "factor_x" and y = var 32 "factor_y" and z = var 32 "factor_z" in
  let boolean = E.unary E.Not (bxor x (bxor y z)) in
  let original = add (add (mul (sub y (c 32 7)) x) (mul (c 32 7) x))
      (mul (c 32 7) boolean) in
  (match N.partial_linear_sum_candidate U.size_of_expr original with
  | Some (candidate, ring_edges, linear_edges) ->
      let builder = P.create original in
      List.iter (fun (l, r) -> P.record_ring builder ~pass:"partial" l r) ring_edges;
      List.iter (fun (l, r) -> P.record_linear_mba builder ~pass:"partial" l r) linear_edges;
      let report = P.verify ~original ~candidate (P.finish builder candidate) in
      require (J.member "verification" report = `String "proved_compositional")
        "partial linear-sum certificate failed"
  | None -> failwith "partial linear-sum extraction found no candidate");

  let a = var 16 "prod_a" and b = var 16 "prod_b" in
  let nonlinear = add
      (mul (band a (E.unary E.Not b)) (band b (E.unary E.Not a)))
      (mul (band a b) (bor a b)) in
  C.evaluator := Sample_evaluator.make ~variables:[ "prod_a", 16; "prod_b", 16 ] 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original:nonlinear ();
  let result = N.run (N.dag_bottom_up_simplify nonlinear) in
  let expected = mul a b in
  let verdict, _, _ = U.are_equivalent result expected (Some 2) in
  require (verdict = U.Yes && U.size_of_expr result <= U.size_of_expr expected)
    "two-atom nonlinear product peeling failed";
  Printf.printf "round31_test: mask bridge, partial linear extraction and peeling passed\n"
