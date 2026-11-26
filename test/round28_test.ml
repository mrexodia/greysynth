module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module O = Greysynth__Oes
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.create value width)
let var width name = E.var name width name
let add = E.binary E.Plus
let sub = E.binary E.Minus
let mul = E.binary E.Mul
let bxor = E.binary E.Xor
let band = E.binary E.And
let bor = E.binary E.Or

let setup original =
  let variables = Sample_evaluator.variables_of_expr original in
  C.evaluator := Sample_evaluator.make ~variables ~seed:0 64;
  C.g_total_timeout := 0.;
  C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 2;
  R.reset ~original ();
  R.start_recording original

let replay original candidate =
  let certificate = P.finish (Option.get !(R.journal)) candidate in
  let report = P.verify ~timeouts:[ 1.; 3. ] ~original ~candidate certificate in
  require (J.member "verification" report = `String "proved_compositional")
    "semantic probe certificate did not replay"

let () =
  let x = var 64 "probe_x" and y = var 64 "probe_y" in
  let noise = let p = mul x y in sub p p in
  let wrapped = add (add x y) noise in
  setup wrapped;
  let linear = N.probe_semantic_linear_mba U.size_of_expr wrapped in
  require (Option.is_some linear) "black-box Boolean-corner linear probe failed";
  let linear = Option.get linear in
  require (R.accepts ~pass:"test-semantic-linear" wrapped linear)
    "linear probe failed strict proof gate";
  replay wrapped linear;

  let cubic_core =
    add (add (mul (c 64 (Z.of_int 7)) (mul (mul x x) x))
           (mul (c 64 (Z.of_int 5)) (mul x x)))
      (add (mul (c 64 (Z.of_int 3)) x) (c 64 (Z.of_int 42)))
  in
  let cubic_noise =
    let p = mul x (add x (c 64 Z.one)) in sub p p
  in
  let cubic = add cubic_core cubic_noise in
  setup cubic;
  let cubic_candidate = N.probe_semantic_poly U.size_of_expr cubic in
  require (Option.is_some cubic_candidate) "univariate cubic probe failed";
  let cubic_candidate = Option.get cubic_candidate in
  require (R.accepts ~pass:"test-semantic-cubic" cubic cubic_candidate)
    "cubic probe failed strict proof gate";
  replay cubic cubic_candidate;

  let bivariate_core =
    add (add (mul (c 64 (Z.of_int 3)) (mul x y))
           (mul (c 64 (Z.of_int 5)) (mul x x)))
      (add (mul (c 64 (Z.of_int (-7))) y) (c 64 (Z.of_int 42)))
  in
  let bivariate = add bivariate_core noise in
  setup bivariate;
  let bivariate_candidate = N.probe_semantic_poly U.size_of_expr bivariate in
  require (Option.is_some bivariate_candidate) "bivariate quadratic probe failed";
  let bivariate_candidate = Option.get bivariate_candidate in
  require (R.accepts ~pass:"test-semantic-bivariate" bivariate bivariate_candidate)
    "bivariate probe failed strict proof gate";
  replay bivariate bivariate_candidate;

  let non_polynomial = band x y in
  setup non_polynomial;
  require (Option.is_none (N.probe_semantic_poly U.size_of_expr non_polynomial))
    "non-polynomial function passed full-width probe filter";

  let sum = add x y in
  let carry = add (bxor x y) (mul (c 64 (Z.of_int 2)) (band x y)) in
  let duplicated = add sum carry in
  setup duplicated;
  require (!(C.evaluator).node_to_outhash sum = !(C.evaluator).node_to_outhash carry)
    "CSE fixture fingerprints differ";
  require (R.accepts ~pass:"cse-fixture" carry sum)
    "CSE fixture equality was not proved";
  R.reset ~original:duplicated ();
  R.start_recording duplicated;
  let cse = O.semantic_dag_cse_pass duplicated in
  require (U.size_of_expr cse < U.size_of_expr duplicated)
    ("semantic DAG CSE did not merge differently obfuscated copies: " ^ U.pp cse);
  replay duplicated cse;

  let big = mul (add x (c 64 (Z.of_int 99))) (bor y (c 64 (Z.of_int 17))) in
  let dead = add (mul (bxor x x) big) y in
  setup dead;
  let pruned = N.run (O.semantic_dag_cse_pass dead) in
  require (E.is_equal pruned y) "semantic dead-branch pruning did not reach y";
  replay dead pruned;
  Printf.printf "round28_test: semantic linear/poly probes and DAG CSE passed\n"
