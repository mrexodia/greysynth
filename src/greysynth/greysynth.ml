(**************************************************************************)
(*  This file is part of BINSEC.                                          *)
(*                                                                        *)
(*  Copyright (C) 2026-2027                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  You can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

(* The main GreySynth file

It runs the enabled passes in order -- OES, fast_simplify, global synthesis,
CHS -- then a final OES clean-up, and checks equivalence against the ground
truth.

*)

open Greysynth_utils.Utils
open Logging
open Config
open Oes
open Synthesis

(* Helper that checks equiv of [e] if ground truth is set AND check_equiv is
   enabled *)
let check_equiv gt ~tag (verdict : equiv_t ref) e =
  match gt with
  | Some _ when !c_check_equiv && !g_has_timedout -> verdict := Timeout
  | Some gt when !c_check_equiv ->
      (try
         check_timeout ();
         let result, time, _ = are_equivalent e gt (Some !c_equiv_timeout) in
         verdict := result;
         _log_dim tag "equiv=%s (%.2fs)" (equiv_to_str result) time;
         check_timeout ()
       with Timeout_exception ->
         g_has_timedout := true;
         verdict := Timeout)
  | _ -> verdict := Disabled

let run_normalization expression =
  if not !c_normalization_portfolio then Normalization.run expression
  else
    let configured = !c_ac_normalization in
    Fun.protect
      ~finally:(fun () -> c_ac_normalization := configured)
      (fun () ->
        let proof = !(Rewrite.journal) in
        let restore state =
          match proof, state with
          | Some builder, Some checkpoint -> Rewrite_proof.restore builder checkpoint
          | _ -> ()
        in
        let initial = Option.map Rewrite_proof.checkpoint proof in
        let initial_cache = Rewrite.checkpoint_caches () in
        c_ac_normalization := false;
        let baseline = Normalization.run expression in
        let baseline_proof = Option.map Rewrite_proof.checkpoint proof in
        let baseline_cache = Rewrite.checkpoint_caches () in
        if !g_has_timedout then baseline
        else (
          restore initial;
          Rewrite.restore_caches initial_cache;
          c_ac_normalization := true;
          let alternative = Normalization.run expression in
          let alternative_proof = Option.map Rewrite_proof.checkpoint proof in
          let alternative_cache = Rewrite.checkpoint_caches () in
          let baseline_cost = size_of_expr baseline
          and alternative_cost = size_of_expr alternative in
          let choose_alternative =
            alternative_cost < baseline_cost
            || (alternative_cost = baseline_cost
                && Sexpr.Expr.compare alternative baseline < 0)
          in
          let selected_proof =
            if choose_alternative then alternative_proof else baseline_proof
          in
          restore selected_proof;
          Rewrite.restore_caches
            (if choose_alternative then alternative_cache else baseline_cache);
          if choose_alternative then alternative else baseline))

(* One OES pass, without the logging and stats of [oes_with_logs]. *)
let oes_quiet e = fst (linear_simplify e)

(* Synthesis at increasing horizons (2 .. depth), with an OES pass after
   each horizon when OES is enabled. Updates [best] after every horizon, so a
   timeout keeps validated rewrites from the current partial horizon too. *)
let chs gt best =
  c_current_mode_is_global := false;
  let start = Unix.gettimeofday () in
  let horizon = ref 2 in
  while
    not !g_has_timedout
    && !horizon <= depth_of_expr !best
    && (!c_chs_max_horizon = 0 || !horizon <= !c_chs_max_horizon)
  do
    try
      check_timeout ();
      let before = size_of_expr !best in
      best := simplify_with_horizon !horizon !c_synthesis_timeout !c_synthesis_repeat !best;
      if !c_normalization && not !g_has_timedout then best := run_normalization !best;
      if !c_oes && not !g_has_timedout then best := oes_quiet !best;
      if size_of_expr !best < before then horizon := 2 else incr horizon
    with Timeout_exception -> g_has_timedout := true
  done;
  let time = Unix.gettimeofday () -. start in
  log_chs_size_after := size_of_expr !best;
  log_chs_time := time;
  check_equiv gt ~tag:"CHS" log_chs_is_equiv !best;
  _log_ok "CHS" "done  size=%d  (%.2fs)" !log_chs_size_after time

type preprocessing_log = {
  linear_size : int;
  linear_simplifications : int;
  linear_vocab : int;
  local_vocab : int;
  linear_time : float;
  normalization_equiv : equiv_t;
  linear_equiv : equiv_t;
  fast_equiv : equiv_t;
  unique_before : (Sample_evaluator.outhash, int) Hashtbl.t;
  unique_after : (Sample_evaluator.outhash, int) Hashtbl.t;
  unique_semantics : int;
}

let snapshot_preprocessing_log () =
  {
    linear_size = !log_linear_size_after;
    linear_simplifications = !log_linear_number_simplifications;
    linear_vocab = !log_linear_vocab_injected;
    local_vocab = !log_local_extend_injected;
    linear_time = !log_linear_time;
    normalization_equiv = !log_normalization_is_equiv;
    linear_equiv = !log_linear_is_equiv;
    fast_equiv = !log_fast_simplify_is_equiv;
    unique_before = Hashtbl.copy log_linear_number_unique_hash_before;
    unique_after = Hashtbl.copy log_linear_number_unique_hash_after;
    unique_semantics = !tmp_uniq_semantic;
  }

let restore_table target source =
  Hashtbl.clear target;
  Hashtbl.iter (Hashtbl.replace target) source

let restore_preprocessing_log snapshot =
  log_linear_size_after := snapshot.linear_size;
  log_linear_number_simplifications := snapshot.linear_simplifications;
  log_linear_vocab_injected := snapshot.linear_vocab;
  log_local_extend_injected := snapshot.local_vocab;
  log_linear_time := snapshot.linear_time;
  log_normalization_is_equiv := snapshot.normalization_equiv;
  log_linear_is_equiv := snapshot.linear_equiv;
  log_fast_simplify_is_equiv := snapshot.fast_equiv;
  restore_table log_linear_number_unique_hash_before snapshot.unique_before;
  restore_table log_linear_number_unique_hash_after snapshot.unique_after;
  tmp_uniq_semantic := snapshot.unique_semantics

let run_preprocessing gt input =
  let best = ref input in
  let standard () =
    if !c_normalization && not !g_has_timedout then (
      best := run_normalization !best;
      check_equiv gt ~tag:"normalization" log_normalization_is_equiv !best);
    if !c_oes && not !g_has_timedout then (
      best := oes_with_logs !best;
      check_equiv gt ~tag:"OES" log_linear_is_equiv !best)
  in
  if !c_egraph_extraction && not !g_has_timedout then (
    let before = !best in
    best := Egraph.optimize !best;
    if Egraph.fell_back () || Sexpr.Expr.is_equal !best before then (
      let configured_ac = !c_ac_normalization in
      Fun.protect
        ~finally:(fun () -> c_ac_normalization := configured_ac)
        (fun () -> c_ac_normalization := false; standard ()))
    else check_equiv gt ~tag:"egraph" log_normalization_is_equiv !best)
  else standard ();
  (* This relational extension is not part of the CCS'26 paper. *)
  if !c_fast_simplify && not !g_has_timedout then (
    best := fast_simplify_with_logs !best;
    check_equiv gt ~tag:"fast_simplify" log_fast_simplify_is_equiv !best);
  !best

let run_preprocessing_portfolio gt input =
  if not !c_preprocessing_portfolio then run_preprocessing gt input
  else
    let configured_ac = !c_ac_normalization in
    let configured_normalization_portfolio = !c_normalization_portfolio in
    let configured_oracle = !c_mba_oracle in
    let proof = !(Rewrite.journal) in
    let proof_initial = Option.map Rewrite_proof.checkpoint proof in
    let cache_initial = Rewrite.checkpoint_caches () in
    let log_initial = snapshot_preprocessing_log () in
    let restore_proof = function
      | Some checkpoint -> Option.iter (fun builder -> Rewrite_proof.restore builder checkpoint) proof
      | None -> ()
    in
    Fun.protect
      ~finally:(fun () ->
        c_ac_normalization := configured_ac;
        c_normalization_portfolio := configured_normalization_portfolio;
        c_mba_oracle := configured_oracle)
      (fun () ->
        c_ac_normalization := false;
        c_normalization_portfolio := false;
        c_mba_oracle := "none";
        let baseline = run_preprocessing gt input in
        let baseline_log = snapshot_preprocessing_log () in
        let baseline_proof = Option.map Rewrite_proof.checkpoint proof in
        let baseline_cache = Rewrite.checkpoint_caches () in
        if !g_has_timedout then baseline
        else (
          restore_preprocessing_log log_initial;
          restore_proof proof_initial;
          Rewrite.restore_caches cache_initial;
          c_ac_normalization := configured_ac;
          c_normalization_portfolio := configured_normalization_portfolio;
          c_mba_oracle := configured_oracle;
          let experimental = run_preprocessing gt input in
          let experimental_log = snapshot_preprocessing_log () in
          let experimental_proof = Option.map Rewrite_proof.checkpoint proof in
          let experimental_cache = Rewrite.checkpoint_caches () in
          let choose_experimental =
            size_of_expr experimental < size_of_expr baseline
            || (size_of_expr experimental = size_of_expr baseline
                && Sexpr.Expr.compare experimental baseline < 0)
          in
          restore_preprocessing_log
            (if choose_experimental then experimental_log else baseline_log);
          restore_proof
            (if choose_experimental then experimental_proof else baseline_proof);
          Rewrite.restore_caches
            (if choose_experimental then experimental_cache else baseline_cache);
          if choose_experimental then experimental else baseline))

(* Run preprocessing, then the enabled synthesis passes. Traversals retain
   validated partial results when the budget expires. *)
let run_passes gt obf =
  let best = ref obf in
  (try
     best := run_preprocessing_portfolio gt !best;
     if !c_global_synthesis && not !g_has_timedout then (
       c_current_mode_is_global := true;
       best := simplify_global !c_synthesis_timeout !c_synthesis_repeat !best;
       check_equiv gt ~tag:"global" log_global_is_equiv !best);
     if !c_chs && not !g_has_timedout then chs gt best
   with Timeout_exception ->
     g_has_timedout := true;
     _log_warn "greysynth" "timeout reached");
  !best

(* ── Reporting ─────────────────────────────────────────────────── *)

let print_summary ~initial_size ~total_time gt result =
  _log_header "Result";
  Format.eprintf "  %d -> \027[1;32m%d\027[0m  (%.2fs)%s\n" initial_size
    (size_of_expr result)
    total_time
    (if !g_has_timedout then "  \027[33m[timed out]\027[0m" else "");
  Option.iter
    (fun gt -> Format.eprintf "  ground truth  %d\n" (size_of_expr gt))
    gt;
  Format.eprintf "  expr  %s\n%!" (pp result)

let floats l = `List (List.map (fun x -> `Float x) l)
let ints l = `List (List.map (fun x -> `Int x) l)
let sum_values tbl = Hashtbl.fold (fun _ v acc -> acc + v) tbl 0

(* horizon -> value tables *)
let per_horizon tbl to_json =
  `Assoc (Hashtbl.fold (fun h v acc -> (string_of_int h, to_json v) :: acc) tbl [])

let attempts_json attempts =
  `List
    (List.map
       (fun (attempt : Logging.synthesis_attempt) ->
         `Assoc
           [
             ("input_size", `Int attempt.input_size);
             ("status", `String attempt.status);
             ("success", `Bool (attempt.status = "returned"));
             ("time", `Float attempt.time);
             ("is_simplification", `Bool attempt.is_simplification);
           ])
       attempts)

(* A rewrite found by synthesis, with pass-specific [extra] fields. *)
let rule_json src dst count extra =
  `Assoc
    ([
       ("lhs_expr", `String (pp src));
       ("lhs_size", `Int (size_of_expr src));
       ("rhs_expr", `String (pp dst));
       ("rhs_size", `Int (size_of_expr dst));
       ("count", `Int count);
     ]
    @ extra)

let report_json ~initial_size ~total_time ?proof ?(outside_proof_semantics = false) gt result =
  let equiv r = `String (equiv_to_str !r) in
  let costs expression =
    `Assoc
      [ ("legacy", `Int (cost_of_expr Legacy expression));
        ("paper_ast", `Int (cost_of_expr PaperAst expression));
        ("instruction", `Int (cost_of_expr Instruction expression));
        ("readability", `Int (cost_of_expr Readability expression)) ]
  in
  let ground_truth =
    match gt with
    | Some gt -> [ ("gt_sz", `Int (size_of_expr gt)); ("gt_expr", `String (pp gt)) ]
    | None -> []
  in
  let global_rules =
    Hashtbl.fold
      (fun (src, dst) (count, times) acc ->
        rule_json src dst count [ ("times", floats times) ] :: acc)
      log_global_rules_found []
  in
  let chs_rules =
    Hashtbl.fold
      (fun (src, dst) (count, horizons, times) acc ->
        rule_json src dst count
          [ ("horizons", ints horizons); ("times", floats times) ]
        :: acc)
      log_chs_rules_found []
  in
  `Assoc
    ([
       ("obf_sz", `Int initial_size);
       ("obf_costs", costs !log_obfuscated_expression);
       ("syn_expr", `String (pp result));
       ("syn_sz", `Int (size_of_expr result));
       ("syn_costs", costs result);
       ("equiv", equiv log_final_is_equiv);
       ("time", `Float total_time);
       ("uniq_semantic", `Int !tmp_uniq_semantic);
       ("has_timed_out", `Bool !g_has_timedout);
     ]
    @ ground_truth
    @ (if outside_proof_semantics then
         [ "proof_semantics", `String "outside_proof_semantics" ]
       else [])
    @ (match proof with None -> [] | Some metadata -> ["proof_certificate", metadata])
    @ Config.report_fields ()
    @ [
        ( "rewrite_validation",
          `String
            (if !c_reject_non_equiv_simplifications then "proved" else "sampled") );
        ( "rewrite_checks",
          `Assoc
            [
              ("candidates", `Int !Rewrite.checked);
              ("proved", `Int !Rewrite.proved);
              ("sample_rejections", `Int !Rewrite.sample_rejections);
              ("disproved", `Int !Rewrite.disproved);
              ("inconclusive", `Int !Rewrite.inconclusive);
            ] );
        ("sampling_strategy", `String (string_of_sampling !c_sampling_strategy));
        ("nb_samples", `Int !c_nb_samples);
        ("synthesizer", `String !c_synthesizer_name);
        ("xyntia_grammar", `String !c_xyntia_grammar);
        ("normalization_is_equiv", equiv log_normalization_is_equiv);
        ("fast_simplify_is_equiv", equiv log_fast_simplify_is_equiv);
        (* OES ("linear") pass *)
        ("linear_size_after", `Int !log_linear_size_after);
        ("linear_time", `Float !log_linear_time);
        ("linear_number_simplifications", `Int !log_linear_number_simplifications);
        ( "linear_number_unique_hash_before",
          `Int (Hashtbl.length log_linear_number_unique_hash_before) );
        ( "linear_number_unique_hash_after",
          `Int (Hashtbl.length log_linear_number_unique_hash_after) );
        ("linear_is_equiv", equiv log_linear_is_equiv);
        (* global synthesis *)
        ("global_size_after", `Int !log_global_size_after);
        ("global_time", `Float !log_global_time);
        ("global_number_simplifications", `Int !log_global_number_simplifications);
        ("global_synthesis_attempts", attempts_json !log_global_synthesis_attempts);
        ("global_horizon", `Int !log_global_horizon);
        ("global_rules_found", `List global_rules);
        ("global_is_equiv", equiv log_global_is_equiv);
        (* CHS *)
        ("chs_size_after", `Int !log_chs_size_after);
        ("chs_time", `Float !log_chs_time);
        ("chs_total_cache_hits", `Int (sum_values log_chs_cache_hits_per_horizon));
        ("chs_total_processed", `Int (sum_values log_chs_process_per_horizon));
        ("chs_number_simplifications", `Int !log_chs_number_simplifications);
        ("chs_synthesis_attempts", attempts_json !log_chs_synthesis_attempts);
        ( "chs_time_per_horizon",
          per_horizon log_chs_time_per_horizon (fun t -> `Float t) );
        ( "chs_cache_hits_per_horizon",
          per_horizon log_chs_cache_hits_per_horizon (fun n -> `Int n) );
        ( "chs_process_per_horizon",
          per_horizon log_chs_process_per_horizon (fun n -> `Int n) );
        ("chs_rules_found", `List chs_rules);
        ("chs_is_equiv", equiv log_chs_is_equiv);
      ])

(* ── Entry point ───────────────────────────────────────────────── *)

let rec contains_load = function
  | Sexpr.Expr.Load _ -> true
  | Sexpr.Expr.Unary { x; _ } -> contains_load x
  | Sexpr.Expr.Binary { x; y; _ } -> contains_load x || contains_load y
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      contains_load c || contains_load t || contains_load e
  | _ -> false

let run ?proof_output obf config gt =
  Greysynth_utils.Utils.reset_solver_session ();
  Logging.reset ();
  load_config_from_json config;
  let outside_proof_semantics = contains_load obf in
  if not outside_proof_semantics then
    evaluator :=
      Sample_evaluator.make ~variables:(Sample_evaluator.variables_of_expr obf)
        ~seed:0 !c_nb_samples;
  log_obfuscated_expression := obf;
  g_start_time := Unix.gettimeofday ();
  g_has_timedout := false;
  Rewrite.reset ~original:obf ();
  Synthesis.reset_rule_cache ();
  Synthesis.load_learned_rules !c_learned_rules_file;
  if outside_proof_semantics then
    Logging._log_warn "proof" "memory loads are outside the pure-expression proof semantics";
  if not outside_proof_semantics then
    Option.iter (fun _ -> Rewrite.start_recording obf) proof_output;

  let initial_size = size_of_expr obf in
  _log "greysynth" "input size=%d%s" initial_size
    (if !g_total_timeout > 0. then
       Printf.sprintf "  (timeout=%.0fs)" !g_total_timeout
     else "");

  (* Checking does not require a separate ground truth: the input is the
     semantic reference when no ground truth was supplied. *)
  let reference = Some (Option.value gt ~default:obf) in
  let result = if outside_proof_semantics then obf else run_passes reference obf in
  let result =
    if not outside_proof_semantics && !c_normalization && not !g_has_timedout then
      try run_normalization result with Timeout_exception ->
        g_has_timedout := true;
        result
    else result
  in
  (* final OES clean-up, skipped once out of time *)
  let result =
    if not outside_proof_semantics && !c_oes && not !g_has_timedout then
      try oes_quiet result with Timeout_exception ->
        g_has_timedout := true;
        result
    else result
  in
  if not outside_proof_semantics then
    check_equiv reference ~tag:"final" log_final_is_equiv result;

  let proof =
    if outside_proof_semantics then None
    else Option.map (fun path -> Rewrite.write_certificate path result) proof_output
  in
  let total_time = Unix.gettimeofday () -. !g_start_time in
  print_summary ~initial_size ~total_time gt result;
  Format.printf "%s\n"
    (Yojson.Basic.pretty_to_string
       (report_json ~initial_size ~total_time ?proof ~outside_proof_semantics gt result));
  Greysynth_utils.Utils.reset_solver_session ()
