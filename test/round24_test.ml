module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module G = Greysynth
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message

let run label original expected =
  C.reset_defaults ();
  C.c_normalization := true;
  C.c_oes := true;
  C.c_ac_normalization := true;
  C.c_egraph_extraction := true;
  C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 1;
  C.g_total_timeout := 30.;
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
    (Printf.sprintf "%s: expected size <= %d, got %d" label
       (U.size_of_expr expected) (U.size_of_expr result));
  let certificate = P.finish (Option.get !(R.journal)) result in
  let report = P.verify ~original ~candidate:result certificate in
  require (J.member "verification" report = `String "proved_compositional")
    (label ^ ": certificate did not replay");
  require (J.member "abstract_proofs" report = `Int 0
           && J.member "direct_proofs" report = `Int 0)
    (label ^ ": hybrid reduction unexpectedly emitted SMT proof edges");
  Printf.printf "round24_test: %s %d -> %d (GT %d), decidable replay\n"
    label (U.size_of_expr original) (U.size_of_expr result) (U.size_of_expr expected)

let () =
  if Array.length Sys.argv <> 2 then
    failwith "round24_test: expected permutation64.txt";
  let lines = In_channel.with_open_text Sys.argv.(1) In_channel.input_lines in
  List.iter
    (fun line_number ->
      let line = List.nth lines (line_number - 1) in
      let comma = String.index line ',' in
      let original = String.sub line 0 comma |> String_to_sexpr.parse ~default_size:64
      and expected =
        String.sub line (comma + 1) (String.length line - comma - 1)
        |> String_to_sexpr.parse ~default_size:64
      in
      run (Printf.sprintf "permutation64 line %d" line_number) original expected)
    [ 3; 6; 10 ]
