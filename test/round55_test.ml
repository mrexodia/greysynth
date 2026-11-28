module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)

let () =
  let atoms = List.init 5 (fun i -> E.var ("r55_x" ^ string_of_int i) 64 ("r55_x" ^ string_of_int i)) in
  let masked i = E.binary E.And (List.nth atoms i) (c 64 (0x11 * (i + 1))) in
  let terms = [ masked 0; masked 1; masked 2; masked 1; masked 2; masked 3; masked 3; masked 4 ] in
  let source = List.fold_left (E.binary E.Xor) (List.hd terms) (List.tl terms) in
  C.reset_defaults ();
  C.evaluator := Sample_evaluator.make ~variables:(Sample_evaluator.variables_of_expr source) 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original:source (); R.start_recording source;
  match N.gf2_masked_xor_candidate U.size_of_expr source with
  | None -> failwith "GF2 masked-XOR candidate missing"
  | Some candidate ->
      require (U.size_of_expr candidate < U.size_of_expr source)
        "GF2 masked-XOR candidate did not reduce size";
      require
        (R.accepts_compositional ~pass:"round55-gf2" ~equalities:[]
           ~semilinear_mba_equalities:[ source, candidate ] source candidate
         || R.accepts ~timeout:1.0 ~pass:"round55-gf2-smt" source candidate)
        "GF2 masked-XOR candidate did not certify";
      let certificate = P.finish (Option.get !(R.journal)) candidate in
      require
        (J.member "verification" (P.verify ~timeouts:[ 1.; 3. ]
           ~original:source ~candidate certificate) = `String "proved_compositional")
        "GF2 masked-XOR certificate did not replay";
      Printf.printf "round55_test: GF2 masked-XOR normalization passed\n"
