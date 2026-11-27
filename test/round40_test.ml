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
    (J.member "verification" (P.verify ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent certificate replay failed"

let accept_product label original =
  match N.nonlinear_product_identity_candidate original with
  | None -> failwith (label ^ ": product candidate missing")
  | Some (candidate, equalities, linear, semilinear, ring) ->
      require
        (R.accepts_compositional ~pass:label ~equalities
           ~linear_mba_equalities:linear
           ~semilinear_mba_equalities:semilinear ~ring_equalities:ring
           original candidate)
        (label ^ ": compositional proof failed");
      candidate

let () =
  let x0 = E.var "r40_x0" 64 "r40_x0"
  and x1 = E.var "r40_x1" 64 "r40_x1"
  and x2 = E.var "r40_x2" 48 "r40_x2" in
  let a = add (mul x1 (E.unary (E.Uext 16) x2)) x0
  and b = E.unary (E.Uext 16) (E.var "r40_x3" 48 "r40_x3") in
  let carry left right = add (mul (c 64 2) (band left right)) (bxor left right) in
  let opaque = carry (bxor a b) (mul (c 64 2) (band a b)) in
  setup opaque;
  (match N.probe_opaque_atoms U.size_of_expr opaque with
  | Some candidate ->
      let accepted =
        R.accepts_compositional ~pass:"arithmetic-atoms" ~equalities:[]
          ~linear_mba_equalities:[ opaque, candidate ] opaque candidate
        || R.accepts_compositional ~pass:"arithmetic-atoms-semi" ~equalities:[]
             ~semilinear_mba_equalities:[ opaque, candidate ] opaque candidate
        || R.accepts ~timeout:0.5 ~pass:"arithmetic-atoms-abstract"
             opaque candidate
      in
      require accepted
        ("arithmetic-atom opaque probe did not certify: " ^ U.pp candidate);
      replay opaque candidate
  | None -> failwith "arithmetic-atom opaque probe found no candidate");

  let shared = add x0 x1 and offset = c 64 0x37 in
  let one_atom = add (sub shared shared) (sub shared offset) in
  setup one_atom;
  (match N.probe_opaque_atoms U.size_of_expr one_atom with
  | Some candidate ->
      require
        (R.accepts_compositional ~pass:"one-atom-xsmir" ~equalities:[]
           ~linear_mba_equalities:[ one_atom, candidate ] one_atom candidate)
        "one-atom XSMIR candidate did not certify";
      replay one_atom candidate
  | None -> failwith "one-atom XSMIR probe found no candidate");

  let lo = E.var "r40_lo" 32 "r40_lo" in
  let base = cz 32 (Z.of_string "0x1388") in
  let inner = add
      (mul (band lo (cz 32 (Z.of_string "0xffffec77")))
         (band (bnot lo) base))
      (mul (bor lo base) (band lo base)) in
  let ordered = E.unary (E.Uext 32) inner in
  setup ordered;
  let ordered_result = N.dag_bottom_up_simplify ~zero_smt:true ordered in
  require (U.size_of_expr ordered_result < U.size_of_expr ordered)
    "operand-order product peel made no progress";
  replay ordered ordered_result;

  let y = E.var "r40_y" 64 "r40_y" in
  let ax = add x0 (c 64 0x32) in
  let ax_complement = sub (cz 64 (Z.of_string "0xffffffffffffffcd")) x0 in
  let regular = mul (band ax y) (bor ax y)
  and cross = mul (band ax (bnot y)) (band y ax_complement) in
  let negated = sub (sub (c 64 0x1234) regular) cross in
  setup negated;
  let negated_result = accept_product "algebraic-complement" negated in
  require (U.size_of_expr negated_result < U.size_of_expr negated)
    "algebraic-complement peel did not reduce size";
  replay negated negated_result;

  let low0 = E.var "r40_low0" 32 "r40_low0"
  and low2 = E.var "r40_low2" 32 "r40_low2"
  and extra = E.var "r40_extra" 64 "r40_extra" in
  let wide0 = E.unary (E.Uext 32) low0 and wide2 = E.unary (E.Uext 32) low2 in
  let lifted_and = E.unary (E.Uext 32) (band low0 low2) in
  let lifted_regular = mul (bor wide0 wide2) lifted_and
  and lifted_cross = mul (band (bnot wide0) wide2) (band (bnot wide2) wide0) in
  let lifted = add lifted_regular (add lifted_cross extra) in
  setup lifted;
  let lifted_result = accept_product "uext-lifted-product" lifted in
  require (U.size_of_expr lifted_result < U.size_of_expr lifted)
    "uext-lifted product peel did not reduce size";
  replay lifted lifted_result;
  Printf.printf "round40_test: arithmetic atoms and generalized product peeling passed\n"
