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
let bor = E.binary E.Or
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
    (J.member "verification"
       (P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent certificate replay failed"

let rec encoded_sum depth left right =
  if depth = 0 then add left right
  else encoded_sum (depth - 1) (bxor left right)
      (mul (c (E.sizeof left) 2) (band left right))

let () =
  let x0 = E.var "r45_x0" 64 "r45_x0"
  and x1 = E.var "r45_x1" 64 "r45_x1"
  and x2 = E.var "r45_x2" 64 "r45_x2"
  and x3 = E.var "r45_x3" 64 "r45_x3" in
  let inner = add
      (mul (add (bxor x0 x2) x1) (c 64 0x80))
      (add (mul (c 64 0x80) x3) x1) in
  let low7 = E.unary (E.Uext 57) (E.restrict ~lo:0 ~hi:6 inner) in
  setup low7;
  (match N.lowk_restrict_homomorphism_candidate U.size_of_expr low7 with
  | Some (candidate, equalities, linear_mba_equalities, ring_equalities) ->
      require
        (R.accepts_compositional ~pass:"round45-lowk" ~equalities
           ~linear_mba_equalities ~ring_equalities low7 candidate)
        "low-7-bit compositional proof failed";
      require (U.size_of_expr candidate < U.size_of_expr low7)
        "low-7-bit annihilation did not reduce size";
      replay low7 candidate
  | None -> failwith "low-7-bit homomorphism candidate missing");

  let opaque0 = mul x0 x1
  and opaque1 = E.binary E.Udiv x2 (c 64 5)
  and opaque2 = E.binary E.Umod x3 (c 64 3)
  and opaque3 = mul (sub x0 x2) (bor x1 x3) in
  let large_linear = ref (add (add opaque0 opaque1) (add opaque2 opaque3)) in
  for _ = 1 to 7 do large_linear := add !large_linear !large_linear done;
  let large_linear = !large_linear in
  require (U.size_of_expr large_linear > 1000)
    "opaque linear MBA is not large enough";
  setup large_linear;
  (match N.linear_candidates ~max_atoms:8 U.size_of_expr large_linear with
  | candidate :: _ ->
      require
        (R.accepts_compositional ~pass:"round45-opaque-linear" ~equalities:[]
           ~linear_mba_equalities:[ large_linear, candidate ]
           large_linear candidate)
        ("opaque root linear proof failed: " ^ U.pp candidate);
      replay large_linear candidate
  | [] -> failwith "opaque root linear candidate missing");

  let cross = mul (band (E.unary E.Not x0) x1)
      (band (E.unary E.Not x1) x0)
  and regular = mul (bor x0 x1) (band x0 x1) in
  let large_poly = ref (add cross regular) in
  for _ = 1 to 8 do large_poly := add !large_poly !large_poly done;
  let large_poly = !large_poly in
  require (U.size_of_expr large_poly > 2500)
    "nonlinear polynomial MBA is not large enough";
  setup large_poly;
  (match N.polysim_candidate U.size_of_expr large_poly with
  | Some (candidate, linear_mba_equalities, ring_equalities,
          final_linear_equalities) ->
      require
        (R.accepts_compositional ~pass:"round45-polysim" ~equalities:[]
           ~ring_equalities
           ~linear_mba_equalities:(linear_mba_equalities @ final_linear_equalities)
           large_poly candidate)
        "large PolySim proof failed";
      replay large_poly candidate
  | None -> failwith "large PolySim candidate missing");

  let x4 = E.var "r45_x4" 64 "r45_x4"
  and x5 = E.var "r45_x5" 64 "r45_x5"
  and x6 = E.var "r45_x6" 64 "r45_x6" in
  let repeated = bxor (mul x4 (bor x2 x3)) (sub x0 x1) in
  let correlated = bxor (band repeated x5) x6 in
  let opaque_shell = encoded_sum 2 repeated correlated in
  setup opaque_shell;
  (match N.probe_opaque_atoms U.size_of_expr opaque_shell with
  | Some candidate ->
      let accepted =
        R.accepts_compositional ~pass:"round45-maximal-linear" ~equalities:[]
          ~linear_mba_equalities:[ opaque_shell, candidate ]
          opaque_shell candidate
        || R.accepts ~timeout:0.8 ~pass:"round45-maximal-abstract"
             opaque_shell candidate
      in
      require accepted "maximal repeated opaque candidate failed proof";
      replay opaque_shell candidate
  | None -> failwith "maximal repeated opaque probe found no candidate");
  Printf.printf "round45_test: low-k, opaque linear, PolySim and repeats passed\n"
