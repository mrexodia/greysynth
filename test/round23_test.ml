module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module G = Greysynth
module P = Rewrite_proof

let require condition message = if not condition then failwith message

let () =
  if Array.length Sys.argv <> 2 then failwith "round23_test: expected target_366 JSON";
  let open Yojson.Basic.Util in
  let json = Yojson.Basic.from_file Sys.argv.(1) in
  let width = member "bitwidth" json |> to_int in
  let original =
    member "obf_expr" json |> to_string |> String_to_sexpr.parse ~default_size:width
  in
  let expected =
    member "gt_expr" json |> to_string |> String_to_sexpr.parse ~default_size:width
  in
  C.reset_defaults ();
  C.c_normalization := true;
  C.c_oes := true;
  C.c_ac_normalization := true;
  C.c_egraph_extraction := true;
  C.c_egraph_max_enodes := 2048;
  C.c_egraph_max_iters := 4;
  C.c_reject_non_equiv_simplifications := true;
  C.c_equiv_timeout := 1;
  C.g_total_timeout := 5.;
  C.g_start_time := Unix.gettimeofday ();
  C.g_has_timedout := false;
  C.evaluator :=
    Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 100;
  R.reset ~original ();
  R.start_recording original;
  let result = ref (G.run_preprocessing_portfolio (Some expected) original) in
  if not !(C.g_has_timedout)
     && U.size_of_expr !result > U.size_of_expr expected
  then G.chs (Some expected) result;
  if not !(C.g_has_timedout) then result := G.run_cleanup !result;
  let result = !result in
  require (U.size_of_expr result <= U.size_of_expr expected)
    (Printf.sprintf "target_366: expected size <= %d, got %d"
       (U.size_of_expr expected) (U.size_of_expr result));
  let certificate = P.finish (Option.get !(R.journal)) result in
  let report = P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate:result certificate in
  require
    (member "verification" report = `String "proved_compositional")
    "target_366: independent certificate replay failed";
  let verdict, _, _ = U.are_equivalent result expected (Some 5) in
  require (verdict = U.Yes) "target_366: result does not match ground truth";
  Printf.printf "round23_test: target_366 %d -> %d (GT %d), certificate replayed\n"
    (U.size_of_expr original) (U.size_of_expr result) (U.size_of_expr expected)
