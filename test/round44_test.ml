module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module G = Greysynth
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let add = E.binary E.Plus
let sub = E.binary E.Minus
let mul = E.binary E.Mul
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

let bit0_candidate original =
  match N.bit0_restrict_homomorphism_candidate U.size_of_expr original with
  | None -> failwith ("no bit-0 homomorphism candidate for " ^ U.pp original)
  | Some (candidate, equalities, linear_mba_equalities) ->
      require
        (R.accepts_compositional ~pass:"round44-bit0" ~equalities
           ~linear_mba_equalities original candidate)
        "bit-0 compositional proof failed";
      candidate

let () =
  let x0 = E.var "r44_x0" 32 "r44_x0"
  and x1 = E.var "r44_x1" 32 "r44_x1" in
  let source = E.restrict ~lo:0 ~hi:0
      (bnot (sub (E.binary E.Lsl (bor x1 x0) (c 32 1)) (bxor x1 x0))) in
  setup source;
  let result = bit0_candidate source in
  require (U.size_of_expr result < U.size_of_expr source)
    "bit-0 shift/subtraction pushdown did not reduce size";
  replay source result;

  let y0 = E.var "r44_y0" 64 "r44_y0"
  and y1 = E.var "r44_y1" 64 "r44_y1"
  and y2 = E.var "r44_y2" 64 "r44_y2" in
  let product = mul y0 y1 in
  let zero_source = E.unary (E.Uext 63)
      (E.restrict ~lo:0 ~hi:0
         (sub (add product (E.binary E.Lsl y2 (c 64 3))) product)) in
  setup zero_source;
  let zero_result = bit0_candidate zero_source in
  require (U.size_of_expr zero_result = 1)
    ("nonlinear bit-0 cancellation did not reach zero: " ^ U.pp zero_result);
  replay zero_source zero_result;

  let z0 = E.var "r44_z0" 64 "r44_z0"
  and z1 = E.var "r44_z1" 64 "r44_z1"
  and z2 = E.var "r44_z2" 64 "r44_z2"
  and z3 = E.var "r44_z3" 64 "r44_z3" in
  let mixed = E.unary (E.Uext 63)
      (E.restrict ~lo:0 ~hi:0
         (add (bxor (add z0 z1) (c 64 1))
            (E.binary E.Lsl (mul z2 z3) (c 64 1)))) in
  setup mixed;
  let mixed_result = bit0_candidate mixed in
  require (U.size_of_expr mixed_result < U.size_of_expr mixed)
    "mixed bit-0 pushdown did not reduce size";
  replay mixed mixed_result;

  let narrow = E.var "r44_narrow" 64 "r44_narrow" in
  let cast_shift = E.binary E.Lsl
      (E.unary (E.Uext 32) narrow)
      (E.unary (E.Uext 32) (c 64 16)) in
  setup cast_shift;
  let cast_result = N.dag_constant_cast_simplify cast_shift in
  (match cast_result with
  | E.Binary { f = E.Lsl; y = E.Cst value; _ } ->
      require (Z.equal (Bitvector.value_of value) (Z.of_int 16))
        "constant cast produced the wrong shift amount"
  | _ -> failwith "constant shift cast was not folded");
  replay cast_shift cast_result;

  require (Array.length Sys.argv = 2) "round44_test expects the QSynth regression path";
  let json = Yojson.Basic.from_file Sys.argv.(1) in
  let width = J.member "bitwidth" json |> J.to_int in
  let original = J.member "obf_expr" json |> J.to_string
      |> String_to_sexpr.parse ~default_size:width in
  setup original;
  C.c_normalization := true; C.c_oes := true; C.c_ac_normalization := true;
  C.c_egraph_extraction := true; C.g_total_timeout := 5.;
  C.g_start_time := Unix.gettimeofday ();
  let regression = G.run_preprocessing_portfolio None original in
  require (U.size_of_expr regression <= U.size_of_expr original)
    "QSynth regression enlarged the expression";
  replay original regression;
  Printf.printf "round44_test: cycle guard, bit-0 pushdown and casts passed\n"
