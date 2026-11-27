module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let cz width value = E.constant (Bitvector.create value width)
let add = E.binary E.Plus
let sub = E.binary E.Minus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor
let bnot = E.unary E.Not

let setup original =
  C.reset_defaults ();
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original (); R.start_recording original

let replay original candidate =
  let certificate = P.finish (Option.get !(R.journal)) candidate in
  require
    (J.member "verification"
       (P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent certificate replay failed"

let accept_linear label original =
  match
    N.linear_candidates_with_rings ~max_atoms:8 U.size_of_expr original
    |> List.sort (fun (left, _, _) (right, _, _) ->
           Int.compare (U.size_of_expr left) (U.size_of_expr right))
  with
  | (candidate, ring_equalities, rewritten_source) :: _ ->
      require
        (R.accepts_compositional ~pass:label ~equalities:[] ~ring_equalities
           ~linear_mba_equalities:[ rewritten_source, candidate ]
           original candidate)
        (label ^ ": linear/ring proof failed");
      candidate, ring_equalities
  | [] -> failwith (label ^ ": no candidate")

let rec encoded_sum depth left right =
  if depth = 0 then add left right
  else encoded_sum (depth - 1) (bxor left right)
      (mul (c (E.sizeof left) 2) (band left right))

let () =
  let x0 = E.var "r46_x0" 64 "r46_x0"
  and x1 = E.var "r46_x1" 64 "r46_x1"
  and x2 = E.var "r46_x2" 64 "r46_x2" in
  let a = sub x0 x1 and b = bor x1 x2 and k = c 64 (-36) in
  let nested = mul a (mul k b)
  and canonical = mul k (mul a b) in
  let scalar_source = sub nested canonical in
  setup scalar_source;
  let scalar_result, scalar_rings = accept_linear "associative-scalar" scalar_source in
  require (scalar_rings <> []) "associative scalar extraction recorded no ring edge";
  require (U.size_of_expr scalar_result = 1) "associative scalar cancellation missed zero";
  replay scalar_source scalar_result;

  let sum01 = add x0 x1 and sum10 = add x1 x0 in
  let ac_source = bor (band sum01 x2) (band sum10 (bnot x2)) in
  setup ac_source;
  let ac_result, ac_rings = accept_linear "ac-atom" ac_source in
  require (ac_rings <> []) "AC atom unification recorded no ring edge";
  require (U.size_of_expr ac_result <= U.size_of_expr sum01)
    "AC atom unification did not recover the shared sum";
  replay ac_source ac_result;

  let y0 = E.var "r46_y0" 64 "r46_y0"
  and y1 = E.var "r46_y1" 64 "r46_y1"
  and y2 = E.var "r46_y2" 64 "r46_y2"
  and y3 = E.var "r46_y3" 64 "r46_y3" in
  let f0 = ref (encoded_sum 1 y0 y1)
  and f1 = ref (encoded_sum 1 y2 y3) in
  for _ = 1 to 5 do
    f0 := add !f0 !f0;
    f1 := add !f1 !f1
  done;
  let f0 = !f0 and f1 = !f1 in
  let stress = add (mul f0 f1) (mul f0 (sub f1 y2)) in
  require (U.size_of_expr stress > 500) "stress expression is too small";
  setup f0;
  let f0_result, _ = accept_linear "stress-factor" f0 in
  require (U.size_of_expr f0_result < U.size_of_expr f0)
    "stress linear factor did not simplify directly";
  setup stress;
  let started = Unix.gettimeofday () in
  let stress_result = N.dag_bottom_up_simplify ~zero_smt:true stress in
  require (Unix.gettimeofday () -. started < 0.5)
    "linear-first DAG phase exceeded 0.5 seconds";
  require (U.size_of_expr stress_result < U.size_of_expr stress)
    "linear-first DAG phase made no progress";
  replay stress stress_result;

  let z0 = E.var "r46_z0" 64 "r46_z0"
  and z1 = E.var "r46_z1" 64 "r46_z1"
  and z2 = E.var "r46_z2" 64 "r46_z2" in
  let low_mask = c 64 127 and high_mask = cz 64 (Z.of_string "0xffffffffffffff80") in
  let masked = band
      (add (mul (add (bxor z0 z2) z1) (c 64 128)) z1)
      low_mask in
  let small_root = sub (band high_mask z0) masked in
  require (U.size_of_expr small_root <= 128) "small-root low-k test is too large";
  setup small_root;
  let small_result = N.run small_root in
  require (U.size_of_expr small_result < U.size_of_expr small_root)
    "Normalization.run did not apply low-k mask pushdown";
  replay small_root small_result;
  Printf.printf "round46_test: scalar/AC, phase order and low-k roots passed\n"
