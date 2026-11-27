module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let add = E.binary E.Plus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bnot = E.unary E.Not

let setup original =
  C.reset_defaults ();
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original (); R.start_recording original

let product_identity a b =
  add (mul (band (bnot a) b) (band (bnot b) a))
    (mul (bor b a) (band b a))

let replay original candidate =
  let certificate = P.finish (Option.get !(R.journal)) candidate in
  require
    (J.member "verification" (P.verify ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent compositional replay failed"

let () =
  let x0 = E.var "r39_x0" 64 "r39_x0"
  and x1 = E.var "r39_x1" 64 "r39_x1" in
  let leaf = product_identity x0 x1 in
  let giant = ref leaf in
  for _ = 1 to 20 do giant := add !giant !giant done;
  require (U.size_of_expr !giant > 1_000_000)
    "synthetic giant AST is too small";
  require (U.dag_size_bounded ~limit:100 !giant < 100)
    "synthetic giant AST does not have a small DAG";
  setup !giant;
  let started = Unix.gettimeofday () in
  let simplified = N.dag_bottom_up_simplify ~zero_smt:true
      ~deadline:(started +. 1.0) !giant in
  require (Unix.gettimeofday () -. started < 1.0)
    "zero-SMT DAG traversal exceeded one second";
  require (U.size_of_expr simplified < U.size_of_expr !giant)
    "zero-SMT DAG traversal made no progress";
  replay !giant simplified;

  let partial = ref leaf in
  for index = 1 to 600 do partial := add !partial (c 64 index) done;
  setup !partial;
  let partial_result = N.dag_bottom_up_simplify ~zero_smt:false
      ~deadline:(Unix.gettimeofday () +. 0.05) !partial in
  require (U.size_of_expr partial_result <= U.size_of_expr !partial)
    "soft deadline discarded or enlarged the partial DAG result";
  require (not !(C.g_has_timedout))
    "local soft deadline was incorrectly promoted to a global timeout";

  let a = E.unary (E.Sext 24) (E.var "r39_a" 8 "r39_a")
  and b = E.unary (E.Sext 24) (E.var "r39_b" 8 "r39_b") in
  let target_2618 = product_identity a b in
  setup target_2618;
  let exact = N.run target_2618 in
  require (U.size_of_expr exact = 3)
    ("target-2618 cleanup did not reach size 3: " ^ U.pp exact);
  replay target_2618 exact;
  Printf.printf "round39_test: DAG memoization, soft stop and product cleanup passed\n"
