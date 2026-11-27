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

let setup original =
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original (); R.start_recording original

let () =
  let folded = E.unary (E.Uext 32) (c 64 6) in
  setup folded;
  let folded_result = N.dag_bottom_up_simplify folded in
  require (match folded_result with E.Cst value -> E.sizeof folded_result = 96
                                      && Z.equal (Bitvector.value_of value) (Z.of_int 6)
                                | _ -> false)
    "constant zero-extension did not fold";
  let signed = E.unary (E.Sext 32) (c 64 6) in
  setup signed;
  require (match N.dag_bottom_up_simplify signed with E.Cst _ -> true | _ -> false)
    "constant sign-extension did not fold";

  let x = var 64 "semi37_x" and y = var 64 "semi37_y" in
  let opaque = sub (add x (c 64 0x2db)) y in
  let semilinear = sub (mul (c 64 2) (bor opaque (c 64 1)))
      (bxor opaque (c 64 1)) in
  setup semilinear;
  (match N.semilinear_mba_candidate U.size_of_expr semilinear with
  | Some candidate ->
      require (R.accepts_compositional ~pass:"opaque-semilinear" ~equalities:[]
          ~semilinear_mba_equalities:[semilinear,candidate] semilinear candidate)
        "opaque semi-linear candidate failed proof"
  | None -> failwith "opaque semi-linear candidate missing");

  let parity = bor (c 64 (-2)) (add opaque (c 64 1)) in
  setup parity;
  (match N.bit0_parity_candidate U.size_of_expr parity with
  | Some candidate ->
      let verdict,_,_ = U.are_equivalent parity candidate (Some 2) in
      require (verdict = U.Yes) "bit-zero parity candidate is unsound"
  | None -> failwith "bit-zero parity candidate missing");

  let a = var 32 "prod37_a" and b = var 32 "prod37_b" in
  let product = add
      (mul (band (E.unary E.Not a) b) (band (E.unary E.Not b) a))
      (mul (bor a b) (band a b)) in
  setup product;
  let constants = Sample_evaluator.make 8 in
  let proposals = N.local_candidates ~cost:U.size_of_expr ~constants ~ac:false product in
  require (List.exists (fun proposal -> proposal.N.expr = mul a b) proposals)
    "local zero-SMT product peeling candidate missing";

  let q0 = var 64 "q0" and q1 = var 64 "q1" and q2 = var 64 "q2" and q3 = var 64 "q3" in
  let complex = mul (E.binary E.Udiv q0 q1) (E.binary E.Udiv q2 q3) in
  let sliced = E.restrict ~lo:0 ~hi:31
      (bor (E.constant (Bitvector.create (Z.of_string "0xffffffff00000000") 64)) complex) in
  setup sliced;
  (match N.abstract_slice_candidate sliced with
  | Some candidate ->
      require (R.accepts ~timeout:0.2 ~pass:"abstract-slice" sliced candidate)
        "abstract slice candidate failed proof"
  | None -> failwith "abstract slice candidate missing");
  let certificate = P.finish (Option.get !(R.journal))
      (Option.get (N.abstract_slice_candidate sliced)) in
  require (J.member "verification"
      (P.verify ~original:sliced ~candidate:(Option.get (N.abstract_slice_candidate sliced)) certificate)
      = `String "proved_compositional")
    "abstract slice certificate did not replay";
  Printf.printf "round37_test: casts, opaque semi-linear, parity and local peeling passed\n"
