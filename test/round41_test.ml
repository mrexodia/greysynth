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
    (J.member "verification" (P.verify ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent certificate replay failed"

let accept_probe label original candidate =
  R.accepts_compositional ~pass:(label ^ "-linear") ~equalities:[]
    ~linear_mba_equalities:[ original, candidate ] original candidate
  || R.accepts_compositional ~pass:(label ^ "-semilinear") ~equalities:[]
       ~semilinear_mba_equalities:[ original, candidate ] original candidate
  || R.accepts ~timeout:0.5 ~pass:label original candidate

let product_candidate label original =
  match N.nonlinear_product_identity_candidate original with
  | None -> failwith (label ^ ": no product candidate")
  | Some (candidate, equalities, linear, semilinear, ring) ->
      require
        (R.accepts_compositional ~pass:label ~equalities
           ~linear_mba_equalities:linear
           ~semilinear_mba_equalities:semilinear ~ring_equalities:ring
           original candidate)
        (label ^ ": product proof failed");
      candidate

let rec encoded_sum depth left right =
  if depth = 0 then add left right
  else encoded_sum (depth - 1) (bxor left right)
      (mul (c (E.sizeof left) 2) (band left right))

let () =
  let a = E.var "r41_a" 64 "r41_a" and b = E.var "r41_b" 64 "r41_b" in
  let cross = mul (band (bnot a) b) (band (bnot b) a)
  and regular = mul (bor a b) (band a b) in
  let large_shell = encoded_sum 5 cross regular in
  require (U.size_of_expr large_shell > 512 && U.size_of_expr large_shell <= 2048)
    "root opaque shell is outside the intended 513..2048 window";
  require (U.dag_size_bounded ~limit:256 large_shell <= 256)
    "root opaque shell has too many DAG nodes";
  setup large_shell;
  (match N.probe_opaque_atoms ~max_cost:2048 U.size_of_expr large_shell with
  | Some candidate ->
      require (accept_probe "large-root-probe" large_shell candidate)
        "large root probe did not certify";
      let peeled = product_candidate "large-root-product" candidate in
      require (U.size_of_expr peeled <= 5)
        "large root probe did not expose the product identity";
      replay large_shell peeled
  | None -> failwith "large root opaque probe found no candidate");

  List.iter (fun width ->
      let x = E.var (Printf.sprintf "r41_x%d" width) width
          (Printf.sprintf "r41_x%d" width)
      and y = E.var (Printf.sprintf "r41_y%d" width) width
          (Printf.sprintf "r41_y%d" width) in
      let wide = encoded_sum 2 x y in
      setup wide;
      match N.probe_opaque_atoms ~max_cost:2048 U.size_of_expr wide with
      | Some candidate ->
          require (accept_probe "wide-probe" wide candidate)
            "wide-bit probe did not certify";
          replay wide candidate
      | None -> failwith (Printf.sprintf "%d-bit opaque probe failed" width))
    [ 96; 224 ];

  let low = E.var "r41_low" 32 "r41_low" in
  let wide = E.unary (E.Uext 32) low in
  let base_low = cz 32 (Z.of_string "0x1db42")
  and complement_low = cz 32 (Z.of_string "0xfffe24bd")
  and base = cz 64 (Z.of_string "0x1db42") in
  let lifted = add
      (mul (E.unary (E.Uext 32) (band low complement_low))
         (band base (bnot wide)))
      (mul (E.unary (E.Uext 32) (band base_low low)) (bor base wide)) in
  setup lifted;
  let lifted_result = product_candidate "constant-mask-lift" lifted in
  require (U.size_of_expr lifted_result = 3)
    ("constant-mask lift did not reach size 3: " ^ U.pp lifted_result);
  replay lifted lifted_result;

  setup lifted;
  let inconclusive_before = !(R.inconclusive)
  and disproved_before = !(R.disproved) in
  ignore (N.dag_bottom_up_simplify ~zero_smt:true lifted);
  require
    (!(R.inconclusive) = inconclusive_before && !(R.disproved) = disproved_before)
    "zero-SMT DAG pass invoked an inconclusive or refuted SMT-backed check";
  Printf.printf "round41_test: budgets, wide probes and constant masks passed\n"
