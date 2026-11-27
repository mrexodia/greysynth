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

let accept label original candidate =
  let accepted =
    R.accepts_compositional ~pass:label ~equalities:[]
      ~linear_mba_equalities:[ original, candidate ] original candidate
    || R.accepts ~timeout:2.0 ~pass:label original candidate
  in
  require accepted
    (label ^ ": candidate failed proof (" ^ !(R.last_rejection) ^ "): " ^ U.pp candidate);
  let certificate = P.finish (Option.get !(R.journal)) candidate in
  require
    (J.member "verification" (P.verify ~original ~candidate certificate)
     = `String "proved_compositional")
    (label ^ ": certificate did not replay")

let () =
  let x0 = var 64 "op_x0" and x1 = var 64 "op_x1" and x2 = var 64 "op_x2"
  and x3 = var 64 "op_x3" and x4 = var 64 "op_x4" in
  let a = add (mul x2 x4) x0 and b = mul x3 x1 in
  let wrapped = add (E.binary E.Lsl (band a b) (c 64 1)) (bxor a b) in
  setup wrapped;
  (match N.probe_opaque_atoms U.size_of_expr wrapped with
  | Some candidate ->
      accept "opaque-two-atom" wrapped candidate;
      let verdict,_,_ = U.are_equivalent candidate (add a b) (Some 2) in
      require (verdict = U.Yes) "opaque two-atom interpolation returned wrong result"
  | None -> failwith "opaque two-atom interpolation found no candidate");

  let shared = add x0 x1 and offset = c 64 0x1234 in
  let one_atom = add (sub shared shared) (sub shared offset) in
  setup one_atom;
  (match N.probe_opaque_atoms U.size_of_expr one_atom with
  | Some candidate -> accept "opaque-one-atom" one_atom candidate
  | None -> failwith "opaque one-atom interpolation found no candidate");

  let x = var 64 "const_product_x" in
  let base = E.constant (Bitvector.create (Z.of_int 0x3e) 64)
  and complement = E.constant (Bitvector.create (Z.lognot (Z.of_int 0x3e)) 64) in
  let product = add
      (mul (band x base) (bor x base))
      (mul (band x complement) (band (E.unary E.Not x) base)) in
  setup product;
  (match N.nonlinear_product_identity_candidate product with
  | Some (candidate, equalities, linear_edges, semi_edges, ring_edges) ->
      let accepted =
        R.accepts_compositional ~pass:"constant-product" ~equalities
          ~linear_mba_equalities:linear_edges
          ~semilinear_mba_equalities:semi_edges ~ring_equalities:ring_edges
          product candidate
      in
      require accepted
        ("complementary-constant product proof failed: " ^ !(R.last_rejection))
  | None -> failwith "complementary-constant product candidate missing");

  let d0 = var 64 "div0" and d1 = var 64 "div1" and d2 = var 64 "div2"
  and d3 = var 64 "div3" in
  let opaque = mul (E.binary E.Udiv d0 d1) (E.binary E.Udiv d2 d3) in
  let sliced = E.restrict ~lo:0 ~hi:31
      (bor (E.constant (Bitvector.create (Z.of_string "0xffffffff00000000") 64)) opaque) in
  setup sliced;
  let constants = Sample_evaluator.make 8 in
  require
    (N.local_candidates ~cost:U.size_of_expr ~constants ~ac:false sliced
     |> List.exists (fun proposal -> proposal.N.pass = "abstract-slice"))
    "local abstract-slice candidate missing";

  let left = E.restrict ~lo:0 ~hi:7 (band (E.unary E.Not a) b)
  and right = E.restrict ~lo:0 ~hi:7 a in
  let restricted = bor left right in
  (match N.restrict_factoring_candidate restricted with
  | Some candidate ->
      let verdict,_,_ = U.are_equivalent restricted candidate (Some 2) in
      require (verdict = U.Yes) "restrict factoring is unsound"
  | None -> failwith "restrict factoring candidate missing");
  Printf.printf "round38_test: opaque interpolation and local cleanup passed\n"
