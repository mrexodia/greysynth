module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module G = Greysynth
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message

let run path =
  let json = Yojson.Basic.from_file path in
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
  let result = G.run_preprocessing_portfolio (Some expected) original in
  require (U.size_of_expr result <= U.size_of_expr expected)
    (Printf.sprintf "%s: expected size <= %d, got %d" path
       (U.size_of_expr expected) (U.size_of_expr result));
  let certificate = P.finish (Option.get !(R.journal)) result in
  let report = P.verify ~original ~candidate:result certificate in
  require (J.member "verification" report = `String "proved_compositional")
    (path ^ ": certificate did not replay");
  require (J.member "abstract_proofs" report = `Int 0
           && J.member "direct_proofs" report = `Int 0)
    (path ^ ": hybrid reduction unexpectedly emitted SMT proof edges");
  Printf.printf "round24_test: %s %d -> %d (GT %d), decidable replay\n"
    path (U.size_of_expr original) (U.size_of_expr result) (U.size_of_expr expected)

let () =
  if Array.length Sys.argv <> 4 then failwith "round24_test: expected three case JSONs";
  for index = 1 to 3 do run Sys.argv.(index) done
