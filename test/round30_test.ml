module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module G = Greysynth
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message

let run maximum path =
  let json = Yojson.Basic.from_file path in
  let width = J.member "bitwidth" json |> J.to_int in
  let parse field =
    J.member field json |> J.to_string |> String_to_sexpr.parse ~default_size:width
  in
  let original = parse "obf_expr" and expected = parse "gt_expr" in
  C.reset_defaults ();
  C.c_normalization := true; C.c_oes := true; C.c_ac_normalization := true;
  C.c_egraph_extraction := true; C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 1; C.g_total_timeout := 30.;
  C.g_start_time := Unix.gettimeofday (); C.g_has_timedout := false;
  C.g_decidable_root_fast := false;
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 100;
  R.reset ~original (); R.start_recording original;
  let result = ref (G.run_preprocessing_portfolio (Some expected) original) in
  if not !(C.g_has_timedout) && U.size_of_expr !result > maximum then
    G.chs (Some expected) result;
  if not !(C.g_has_timedout) && U.size_of_expr !result > maximum then
    result := G.run_cleanup !result;
  require (U.size_of_expr !result <= maximum)
    (Printf.sprintf "%s: expected <= %d, got %d" path maximum (U.size_of_expr !result));
  let certificate = P.finish (Option.get !(R.journal)) !result in
  require
    (J.member "verification"
       (P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate:!result certificate)
     = `String "proved_compositional")
    (path ^ ": certificate did not replay");
  Printf.printf "round30_test: %s %d -> %d (GT %d)\n" path
    (U.size_of_expr original) (U.size_of_expr !result) (U.size_of_expr expected)

let () =
  if Array.length Sys.argv <> 6 then failwith "round30_test: expected five case JSONs";
  List.iter2 run [ 5; 5; 5; 13; 13 ] (List.tl (Array.to_list Sys.argv))
