module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module S = Greysynth__Synthesis
module B = Greysynth__Synth_backends
module I = Greysynth__Smir_interp
module P = Rewrite_proof
module C = Greysynth__Config
module R = Greysynth__Rewrite
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.create value width)
let var width name = E.var name width name
let norm width value = Z.logand value (Z.pred (Z.shift_left Z.one width))

let () =
  let width = 32 and x = var 32 "smir_x" in
  let modulus = Z.shift_left Z.one width in
  let values =
    Array.of_list
      (List.init 12 Z.of_int
       @ [ Z.of_string "0x80000000"; Z.of_string "0xffffffff";
           Z.of_string "0x12345678"; Z.of_string "0xfedcba98" ])
  in
  let prove label expected target =
    let candidates = I.analytical_candidates ~width ~target ~expression:x ~values in
    let candidate =
      List.find_opt
        (fun candidate ->
          let verdict, _, _ = U.are_equivalent candidate expected (Some 2) in
          verdict = U.Yes)
        candidates
    in
    require (Option.is_some candidate) (label ^ ": analytical rule was not recovered");
    let candidate = Option.get candidate in
    let builder = P.create expected in
    P.record builder ~pass:label expected candidate;
    let report = P.verify ~original:expected ~candidate (P.finish builder candidate) in
    require (J.member "verification" report = `String "proved_compositional")
      (label ^ ": candidate certificate did not replay")
  in
  let map f = Array.map (fun value -> norm width (f value)) values in
  prove "exact" x values;
  prove "add" (E.binary E.Plus x (c width (Z.of_string "0xdeadbeef")))
    (map (fun value -> Z.add value (Z.of_string "0xdeadbeef")));
  prove "xor" (E.binary E.Xor x (c width (Z.of_string "0xa5a55a5a")))
    (Array.map (fun value -> Z.logxor value (Z.of_string "0xa5a55a5a")) values);
  prove "multiply" (E.binary E.Mul (c width (Z.of_int 7)) x)
    (map (Z.mul (Z.of_int 7)));
  prove "and-or"
    (E.binary E.Or (E.binary E.And x (c width (Z.of_string "0x00ff00ff")))
       (c width (Z.of_string "0x01000000")))
    (Array.map (fun value ->
         Z.logor (Z.logand value (Z.of_string "0x00ff00ff"))
           (Z.of_string "0x01000000")) values);
  prove "affine"
    (E.binary E.Plus (E.binary E.Mul (c width (Z.of_string "0x12345679")) x)
       (c width (Z.of_string "0xc0de")))
    (map (fun value -> Z.add (Z.mul (Z.of_string "0x12345679") value)
                         (Z.of_string "0xc0de")));
  prove "poly2"
    (E.binary E.Plus
       (E.binary E.Plus (E.binary E.Mul (c width (Z.of_int 3)) (E.binary E.Mul x x))
          (E.binary E.Mul (c width (Z.of_int 5)) x)) (c width (Z.of_int 9)))
    (map (fun value -> Z.add (Z.of_int 9)
             (Z.add (Z.mul (Z.of_int 5) value)
                (Z.mul (Z.of_int 3) (Z.mul value value)))));
  let shift amount = c width (Z.of_int amount) in
  let ror value amount = norm width
      (Z.logor (Z.shift_right value amount) (Z.shift_left value (width - amount))) in
  prove "ror" (E.binary E.Ror x (shift 13)) (Array.map (fun value -> ror value 13) values);
  prove "lsl" (E.binary E.Lsl x (shift 5)) (map (fun value -> Z.shift_left value 5));
  prove "lsr" (E.binary E.Lsr x (shift 7)) (Array.map (fun value -> Z.shift_right value 7) values);
  let arithmetic_shift value amount =
    let signed = if Z.testbit value (width - 1) then Z.sub value modulus else value in
    norm width (Z.shift_right signed amount)
  in
  prove "asr" (E.binary E.Asr x (shift 3)) (Array.map (fun value -> arithmetic_shift value 3) values);
  prove "constant" (c width (Z.of_string "0x76543210"))
    (Array.make (Array.length values) (Z.of_string "0x76543210"));

  let y = var 32 "smir_y" in
  let samples =
    Array.init 16 (fun index ->
        let xv = Bitvector.of_int ~size:32 (index * 17 + 1)
        and yv = Bitvector.of_int ~size:32 (index * 29 + 2) in
        let mixed = Z.logxor (Bitvector.value_of xv) (Bitvector.value_of yv) in
        ({ args = [| xv; yv |]; res = Bitvector.create mixed 32 } : B.sample))
  in
  let problem : B.problem =
    { inputs = [| { name = "smir_x"; size = 32 }; { name = "smir_y"; size = 32 } |];
      output_size = 32; samples; constants = [];
      operators = { shifts = false; division = false; conditional = false };
      timeout = 1; repeat = 1 }
  in
  let enumerated = I.synthesize_exact problem in
  require (Option.is_some enumerated) "exact small-tree enumerator found no result";
  let expected = E.binary E.Xor x y in
  let verdict, _, _ = U.are_equivalent (Option.get enumerated) expected (Some 2) in
  require (verdict = U.Yes) "enumerator result was not universally valid";

  S.reset_rule_cache ();
  let a = var 32 "ga" and b = var 32 "gb" and d = var 32 "gd" in
  let shared = E.binary E.Plus a b in
  let sound_lhs = E.binary E.Plus (E.binary E.Or shared d) (E.binary E.And shared d)
  and sound_rhs = E.binary E.Plus shared d in
  require (Option.is_some (S.generalize_rule sound_lhs sound_rhs))
    "sound generalized rule was rejected";
  let unsound_lhs = E.binary E.Minus (E.binary E.Minus shared a) b
  and unsound_rhs = E.binary E.Minus shared shared in
  require (Option.is_none (S.generalize_rule unsound_lhs unsound_rhs))
    "unsound generalized rule was cached";

  C.evaluator := Sample_evaluator.make ~variables:[ "ga", 32; "gb", 32 ] ~seed:0 32;
  C.g_total_timeout := 0.;
  C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 2;
  R.reset ~original:(E.binary E.Plus (E.binary E.Plus a b) (E.unary E.Minus a)) ();
  let ac_source = E.binary E.Plus (E.binary E.Plus a b) (E.unary E.Minus a) in
  R.start_recording ac_source;
  let ac_result = S.ac_pairwise_candidate ac_source in
  require (Option.is_some ac_result) "AC pairwise cancellation found no candidate";
  let ac_result = Option.get ac_result in
  let ac_verdict, _, _ = U.are_equivalent ac_result b (Some 2) in
  require (ac_verdict = U.Yes) "AC pairwise cancellation returned the wrong result";
  let ac_certificate = P.finish (Option.get !(R.journal)) ac_result in
  require
    (J.member "verification" (P.verify ~original:ac_source ~candidate:ac_result ac_certificate)
     = `String "proved_compositional")
    "AC pairwise certificate did not replay";
  Printf.printf "round26_test: analytical rules, exact enumeration and generalized-rule gate passed\n"
