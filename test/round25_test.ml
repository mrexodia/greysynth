module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module G = Greysynth
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message

let () =
  if Array.length Sys.argv <> 2 then failwith "round25_test: expected target_2558 JSON";
  let json = Yojson.Basic.from_file Sys.argv.(1) in
  let width = J.member "bitwidth" json |> J.to_int in
  let parse field =
    J.member field json |> J.to_string |> String_to_sexpr.parse ~default_size:width
  in
  let original = parse "obf_expr" and expected = parse "gt_expr" in
  C.reset_defaults ();
  C.c_normalization := true;
  C.c_oes := true;
  C.c_ac_normalization := true;
  C.c_egraph_extraction := true;
  C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 1;
  C.g_total_timeout := 5.;
  C.g_start_time := Unix.gettimeofday ();
  C.g_has_timedout := false;
  C.g_decidable_root_fast := false;
  C.evaluator :=
    Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 100;
  R.reset ~original ();
  R.start_recording original;
  let result = ref (G.run_preprocessing_portfolio (Some expected) original) in
  if not !(C.g_has_timedout) then G.chs (Some expected) result;
  let result = !result in
  require (U.size_of_expr result <= 107)
    (Printf.sprintf "target_2558: expected size <= 107, got %d"
       (U.size_of_expr result));
  let certificate = P.finish (Option.get !(R.journal)) result in
  let report = P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate:result certificate in
  require (J.member "verification" report = `String "proved_compositional")
    "target_2558: certificate did not replay";
  let verdict, _, _ = U.are_equivalent result expected (Some 5) in
  require (verdict = U.Yes) "target_2558: result differs from ground truth";
  Printf.printf "round25_test: target_2558 %d -> %d (GT %d), replayed\n"
    (U.size_of_expr original) (U.size_of_expr result) (U.size_of_expr expected)
