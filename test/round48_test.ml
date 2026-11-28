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

let accept_product label original =
  match N.nonlinear_product_identity_candidate original with
  | Some (candidate, equalities, linear, semilinear, ring) ->
      require
        (R.accepts_compositional ~pass:label ~equalities
           ~linear_mba_equalities:linear ~semilinear_mba_equalities:semilinear
           ~ring_equalities:ring original candidate)
        (label ^ ": product proof failed");
      candidate
  | None -> failwith (label ^ ": product candidate missing")

let () =
  let x0 = E.var "r48_x0" 64 "r48_x0"
  and x1 = E.var "r48_x1" 64 "r48_x1"
  and x2 = E.var "r48_x2" 64 "r48_x2" in
  let a = add (band x0 x1) (bxor x0 x2)
  and b = mul (sub x0 x2) (bor x1 x2) in
  let boundary = sub (add a b) (mul (c 64 2) (band a b)) in
  setup boundary;
  let proposals =
    N.linear_candidates_with_rings ~max_atoms:8 U.size_of_expr boundary
  in
  require (List.length proposals >= 2)
    "dual-boundary producer did not merge both analyses";
  let accepted =
    proposals
    |> List.sort (fun (left, _, _) (right, _, _) ->
           Int.compare (U.size_of_expr left) (U.size_of_expr right))
    |> List.find_opt (fun (candidate, rings, source) ->
           R.accepts_compositional ~pass:"dual-boundary" ~equalities:[]
             ~ring_equalities:rings ~linear_mba_equalities:[ source, candidate ]
             boundary candidate)
  in
  (match accepted with
  | Some (candidate, _, _) ->
      require (U.size_of_expr candidate <= U.size_of_expr (bxor a b))
        "dual-boundary merge did not select the strongest candidate";
      replay boundary candidate
  | None -> failwith "no dual-boundary candidate certified");

  let low = E.var "r48_low" 32 "r48_low" in
  let sext = E.unary (E.Sext 32) low and uext = E.unary (E.Uext 32) low in
  let base_low = cz 32 (Z.of_string "0x1388")
  and base = cz 64 (Z.of_string "0x1388") in
  let sext_regular = mul (bor sext base)
      (E.unary (E.Uext 32) (band low base_low))
  and sext_cross = mul (band sext (bnot base)) (band (bnot sext) base) in
  let sext_source = add sext_cross sext_regular in
  setup sext_source;
  let sext_result = accept_product "sext-mask-lift" sext_source in
  require (U.size_of_expr sext_result = 3) "sext mask lift missed the product";
  replay sext_source sext_result;

  let complement_low = cz 32 (Z.of_string "0xfffe24bd")
  and complement_wide = cz 64 (Z.of_string "0xfffffffffffe24bd")
  and base2 = cz 64 (Z.of_string "0x1db42") in
  let uext_regular = mul (bor uext complement_wide)
      (E.unary (E.Uext 32) (band low complement_low))
  and uext_cross = mul (band uext (bnot complement_wide))
      (band (bnot uext) complement_wide) in
  let uext_source = add uext_cross uext_regular in
  setup uext_source;
  let uext_result = accept_product "uext-high-mask-lift" uext_source in
  require (U.size_of_expr uext_result <= U.size_of_expr (mul uext complement_wide))
    "uext high-mask lift missed the product";
  ignore base2;
  replay uext_source uext_result;

  let x3 = E.var "r48_x3" 64 "r48_x3"
  and x4 = E.var "r48_x4" 64 "r48_x4"
  and x5 = E.var "r48_x5" 64 "r48_x5"
  and x6 = E.var "r48_x6" 64 "r48_x6" in
  let p = mul x5 x6 in
  let m1 = band (bor p x3) (bor (band p x3) x4)
  and m2 = band (bor x3 p) (bor x4 (band x3 p)) in
  let majority = sub
      (add m1 (mul (add m1 x2) (add x1 x2)))
      (add (mul (add m2 (add x1 x2)) x2) (mul m2 x1)) in
  setup majority;
  (match N.recursive_bitwise_ac_candidate majority with
  | Some (canonical, ac_edges, ac_ring_edges) ->
      (match N.ring_polynomial_candidate U.size_of_expr canonical with
      | Some candidate ->
          require
            (R.accepts_compositional ~allow_equal_cost:true ~pass:"majority-ac"
               ~equalities:[] ~linear_mba_equalities:ac_edges
               ~ring_equalities:(ac_ring_edges @ [ canonical, candidate ])
               majority candidate)
            "majority AC/ring proof failed";
          require (U.size_of_expr candidate < U.size_of_expr majority)
            "majority polynomial did not collapse";
          replay majority candidate
      | None -> failwith "majority ring candidate missing")
  | None -> failwith "majority AC candidate missing");

  let repeated = bxor (mul x4 (bor x2 x3)) (sub x0 x1) in
  let two = c 64 2 in
  let semilinear_source =
    add (bxor repeated two) (mul (c 64 2) (band repeated two))
  in
  setup semilinear_source;
  (match N.semilinear_mba_candidate U.size_of_expr semilinear_source with
  | Some candidate ->
      require
        (R.accepts_compositional ~pass:"opaque-semilinear" ~equalities:[]
           ~semilinear_mba_equalities:[ semilinear_source, candidate ]
           semilinear_source candidate)
        "opaque semilinear proof failed";
      replay semilinear_source candidate
  | None -> failwith "opaque semilinear candidate missing");

  let bit_a = band (bxor x0 x1) x2 and bit_b = band x0 x1 in
  let plus_mask = add bit_a bit_b and xor_mask = bxor bit_a bit_b in
  let selector = cz 64 (Z.of_string "0x5555555555555555")
  and offset = c 64 7 in
  let context = sub
      (bor (band (add plus_mask offset) selector)
         (band (add offset xor_mask) (bnot selector)))
      offset in
  setup context;
  let context_result = N.dag_bottom_up_simplify ~zero_smt:false context in
  require (U.size_of_expr context_result < U.size_of_expr context)
    "disjoint-sum pure-bitwise canonicalization made no progress";
  replay context context_result;
  Printf.printf "round48_test: dual boundaries, casts, AC, opaque semi-linear passed\n"
