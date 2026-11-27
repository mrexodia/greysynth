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
let sub = E.binary E.Minus
let mul = E.binary E.Mul
let band = E.binary E.And
let bxor = E.binary E.Xor

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
    (J.member "verification" (P.verify ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent certificate replay failed"

let rec encoded_sum depth left right =
  if depth = 0 then add left right
  else encoded_sum (depth - 1) (bxor left right)
      (mul (c (E.sizeof left) 2) (band left right))

let accept_probe original candidate =
  R.accepts_compositional ~pass:"r42-linear" ~equalities:[]
    ~linear_mba_equalities:[ original, candidate ] original candidate
  || R.accepts_compositional ~pass:"r42-semilinear" ~equalities:[]
       ~semilinear_mba_equalities:[ original, candidate ] original candidate
  || R.accepts ~timeout:0.80 ~pass:"r42-abstract" original candidate

let () =
  let x0 = E.var "r42_x0" 64 "r42_x0"
  and x1 = E.var "r42_x1" 64 "r42_x1"
  and x2 = E.var "r42_x2" 64 "r42_x2"
  and x3 = E.var "r42_x3" 64 "r42_x3" in
  let a = mul (sub x1 x2) x3 and b = x0 in
  let shell = encoded_sum 3 a b in
  require (U.size_of_expr shell >= 70 && U.size_of_expr shell <= 128)
    "64-bit shift/carry shell is outside the intended size window";
  setup shell;
  let started = Unix.gettimeofday () in
  (match N.probe_opaque_atoms ~max_cost:2048 U.size_of_expr shell with
  | Some candidate ->
      require (accept_probe shell candidate)
        "64-bit abstract carry proof did not fit its budget";
      require (U.size_of_expr candidate <= 7)
        ("64-bit carry shell did not reach size 7: " ^ U.pp candidate);
      require (Unix.gettimeofday () -. started < 1.0)
        "64-bit abstract carry proof exceeded one second";
      replay shell candidate
  | None -> failwith "64-bit carry shell produced no opaque candidate");

  let masked_terms =
    List.init 22 (fun index -> band x0 (c 64 (2 * index + 1)))
  in
  let junk =
    match masked_terms with
    | head :: tail -> List.fold_left add head tail
    | [] -> assert false
  in
  let opaque_atom = E.binary E.Udiv junk (c 64 3) in
  let starved = encoded_sum 1 opaque_atom x1 in
  require (U.size_of_expr starved >= 100 && U.size_of_expr starved <= 256)
    "probe-starvation expression is outside the DAG probe window";
  setup starved;
  let simplified = N.dag_bottom_up_simplify ~zero_smt:false ~smt_budget:1.5
      ~deadline:(Unix.gettimeofday () +. 1.0) starved in
  require (U.size_of_expr simplified < U.size_of_expr starved)
    "None-returning leaf probes starved the matching outer opaque shell";
  replay starved simplified;
  Printf.printf "round42_test: opaque-call accounting and proof budgets passed\n"
