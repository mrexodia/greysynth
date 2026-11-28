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
    J.member field json |> J.to_string
    |> String_to_sexpr.parse ~default_size:width
  in
  let original = parse "obf_expr" in
  let reference =
    match J.member "gt_expr" json with
    | `String _ -> Some (parse "gt_expr")
    | _ -> None
  in
  C.reset_defaults ();
  C.c_normalization := true; C.c_oes := true; C.c_ac_normalization := true;
  C.c_egraph_extraction := true; C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 1; C.g_total_timeout := 5.;
  C.g_start_time := Unix.gettimeofday (); C.g_has_timedout := false;
  C.g_decidable_root_fast := false;
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 100;
  R.reset ~original (); R.start_recording original;
  let result = ref (G.run_preprocessing_portfolio reference original) in
  if not !(C.g_has_timedout) && U.size_of_expr !result > maximum then
    G.chs reference result;
  if not !(C.g_has_timedout) && U.size_of_expr !result > maximum then
    result := G.run_cleanup !result;
  require (U.size_of_expr !result <= maximum)
    (Printf.sprintf "%s: expected <= %d, got %d: %s" path maximum
       (U.size_of_expr !result) (U.pp !result));
  let certificate = P.finish (Option.get !(R.journal)) !result in
  require
    (J.member "verification"
       (P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate:!result certificate)
     = `String "proved_compositional")
    (path ^ ": certificate did not replay");
  Printf.printf "round49_test: %s %d -> %d%s\n" path
    (U.size_of_expr original) (U.size_of_expr !result)
    (Option.fold ~none:"" ~some:(fun value ->
         Printf.sprintf " (ref %d)" (U.size_of_expr value)) reference)

let () =
  require (Array.length Sys.argv = 7) "round49_test expects six case JSONs";
  List.iter2 run [ 15; 15; 11; 7; 3; 1355 ]
    (List.tl (Array.to_list Sys.argv))
