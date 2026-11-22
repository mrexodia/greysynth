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

(* Synthesis-based simplification: replace a (truncated) subtree by a smaller
   expression found by a black-box synthesizer. [truncate] cuts a node at a
   horizon and relabels the cut leaves with fresh Greek variables (via
   [greek_oracle]); [synthesize] samples the subtree into a
   [Synth_backends.problem] and runs the configured backend on it;
   [simplify_with_horizon] and [simplify_global] drive this over the whole tree. *)

open Greysynth_utils.Utils
open Logging
open Config
open Sexpr.Expr
open Sample_evaluator

class ['a] greek_oracle () =
  object (_)
    val mutable table : ('a, string) Hashtbl.t = Hashtbl.create 16
    val mutable next_index : int = 0

    val greek_letters =
      [|
        "α";
        "β";
        "γ";
        "δ";
        "ε";
        "ζ";
        "η";
        "θ";
        "ι";
        "κ";
        "λ";
        "μ";
        "ν";
        "ξ";
        "ο";
        "π";
        "ρ";
        "σ";
        "τ";
        "υ";
        "φ";
        "χ";
        "ψ";
        "ω";
      |]

    method init () =
      table <- Hashtbl.create 16;
      next_index <- 0

    method lookup (key : 'a) : string =
      match Hashtbl.find_opt table key with
      | Some letter -> letter
      | None ->
          let letter =
            if next_index < Array.length greek_letters then
              greek_letters.(next_index)
            else "ϕ" ^ string_of_int next_index
          in
          Hashtbl.replace table key letter;
          next_index <- next_index + 1;
          letter

    method dump pprint : unit =
      Hashtbl.iter (fun k v -> Printf.printf "%s → %s\n" (pprint k) v) table
  end

let truncate (expr : Sexpr.Expr.t) (depth : int) =
  let greek_counter = new greek_oracle () in
  greek_counter#init ();

  let counter : (Fingerprint.t, int) Hashtbl.t = Hashtbl.create 16 in
  let new_leafs : (Sexpr.Expr.t, Sexpr.Expr.t) Hashtbl.t = Hashtbl.create 16 in

  let get_label node =
    let fingerprint = !evaluator.node_to_fingerprint node in
    Greysynth_utils.Utils.increment_counter counter fingerprint;

    let label = greek_counter#lookup fingerprint in
    let labelled_var = Sexpr.Expr.var label (Sexpr.Expr.sizeof node) label in
    Hashtbl.replace new_leafs labelled_var node;
    labelled_var
  in

  let rec aux node n =
    if n > 0 then
      let ret =
        match node with
        | Sexpr.Expr.Unary r ->
            let new_depth =
              match r.f with
              | Sexpr.Expr.Sext _ | Sexpr.Expr.Uext _ | Sexpr.Expr.Restrict _ ->
                  n
              | _ -> n - 1
            in
            Sexpr.Expr.unary r.f (aux r.x new_depth)
        | Sexpr.Expr.Binary r ->
            Sexpr.Expr.binary r.f (aux r.x (n - 1)) (aux r.y (n - 1))
        | Var _ -> get_label node
        | Cst _ -> node
        | Sexpr.Expr.Ite _ -> get_label node (* opaque input to the synthesizer *)
        | _ -> failwith "Not implemented (extract_tree)"
      in
      ret
    else match node with Cst _ -> node | _ -> get_label node
  in
  let truncated_expression = aux expr depth in

  (truncated_expression, new_leafs)

(* ── Main synthesize entry point ──────────────────────────────── *)

(* Sample [e] into a synthesis problem whose inputs are the cut leaves
   [new_leafs] (Greek variable -> subtree it stands for). *)
let make_problem e new_leafs synthesis_timeout synthesis_repeat :
    Synth_backends.problem =
  let leaves = Hashtbl.fold (fun k _ acc -> k :: acc) new_leafs [] in
  let inputs =
    List.map
      (function
        | Sexpr.Expr.Var v -> { Synth_backends.name = v.name; size = v.size }
        | _ -> failwith "Expected variable in new_leafs keys")
      leaves
    |> Array.of_list
  in

  (* A sample that divides by zero is skipped for the next sample id. *)
  let samples =
    let offset = ref 0 in
    Array.init !c_nb_samples (fun sample_id ->
        let rec retry () =
          let id = sample_id + !offset in
          try
            let args =
              List.map (fun leaf -> !evaluator.eval_label leaf id new_leafs) leaves
              |> Array.of_list
            in
            { Synth_backends.args; res = !evaluator.eval_label e id new_leafs }
          with Division_by_zero ->
            offset := !offset + 1;
            if !offset > 100 then failwith "Too many division by zero errors"
            else retry ()
        in
        retry ())
  in

  let constants =
    let rec find_csts (node : Sexpr.Expr.t) : Bitvector.t list =
      match node with
      | Sexpr.Expr.Cst c -> [ c ]
      | Sexpr.Expr.Unary r -> find_csts r.x
      | Sexpr.Expr.Binary r -> find_csts r.x @ find_csts r.y
      | _ -> []
    in
    if !c_add_constants_to_synthesis then
      find_csts e |> List.sort_uniq Bitvector.compare
    else []
  in
  {
    inputs;
    output_size = Sexpr.Expr.sizeof e;
    samples;
    constants;
    timeout = synthesis_timeout;
    repeat = synthesis_repeat;
  }

(* Run the configured backend. Any failure (exception or ill-formed result)
   counts as "no result"; only the global timeout propagates. *)
let run_backend (problem : Synth_backends.problem) : Sexpr.Expr.t option * float
    =
  let t0 = Unix.gettimeofday () in
  let result =
    try !c_synthesizer problem with
    | Timeout_exception -> raise Timeout_exception
    | exn ->
        _log_warn !c_synthesizer_name "failed: %s" (Printexc.to_string exn);
        None
  in
  let result =
    match result with
    | Some r when not (Synth_backends.well_formed problem r) ->
        _log_warn !c_synthesizer_name "discarding ill-formed result: %s"
          (Greysynth_utils.Utils.pp r);
        None
    | r -> r
  in
  (result, Unix.gettimeofday () -. t0)

let synthesize e new_leafs synthesis_timeout synthesis_repeat =
  check_timeout ();
  let problem = make_problem e new_leafs synthesis_timeout synthesis_repeat in
  match run_backend problem with
  | None, time ->
      if !c_current_mode_is_global then (
        log_global_synthesis_attempts :=
          (Greysynth_utils.Utils.size_of_expr e, false, time, false)
          :: !log_global_synthesis_attempts;
        None)
      else (
        log_chs_synthesis_attempts :=
          (Greysynth_utils.Utils.size_of_expr e, false, time, false)
          :: !log_chs_synthesis_attempts;
        None)
  | Some synth_expr, time ->
      let synth_size = Greysynth_utils.Utils.size_of_expr synth_expr in
      let previous_size = Greysynth_utils.Utils.size_of_expr e in
      let is_smaller = synth_size < previous_size in

      (* Samples only show the result is plausible; optionally prove it.
         Only a proven non-equivalence rejects (unknown/timeout keeps it). *)
      let rejected =
        is_smaller && !c_reject_non_equiv_simplifications
        &&
        let is_equiv, _time, _ =
          Greysynth_utils.Utils.are_equivalent e synth_expr (Some 20)
        in
        match is_equiv with
        | Yes ->
            _log_ok "synth" "equivalence confirmed";
            false
        | No ->
            _log_warn "synth" "NOT equivalent -- rejecting";
            true
        | _ ->
            _log_warn "synth" "equivalence check timed out -- keeping";
            false
      in
      let is_simplification = is_smaller && not rejected in

      let mode = if !c_current_mode_is_global then "global" else "CHS" in
      if !c_current_mode_is_global then
        log_global_synthesis_attempts :=
          (Greysynth_utils.Utils.size_of_expr e, true, time, is_simplification)
          :: !log_global_synthesis_attempts
      else
        log_chs_synthesis_attempts :=
          (Greysynth_utils.Utils.size_of_expr e, true, time, is_simplification)
          :: !log_chs_synthesis_attempts;

      if is_simplification then (
        if !c_current_mode_is_global then
          log_global_number_simplifications :=
            !log_global_number_simplifications + 1
        else
          log_chs_number_simplifications :=
            !log_chs_number_simplifications + 1;

        _log_ok mode "\027[32m%d -> %d\027[0m  (%.2fs)  %s" previous_size
          synth_size time
          (Greysynth_utils.Utils.pp synth_expr);
        Some (synth_expr, time))
      else None

let replace_greek_vars expr new_leafs =
  let rec aux node =
    if Hashtbl.mem new_leafs node then Hashtbl.find new_leafs node
    else
      match node with
      | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (aux r.x)
      | Sexpr.Expr.Binary r -> Sexpr.Expr.binary r.f (aux r.x) (aux r.y)
      | _ -> node
  in
  aux expr

let simplify_with_horizon (horizon : int) synthesis_timeout synthesis_repeat
    (expr : Sexpr.Expr.t) =
  Hashtbl.clear chs_cache_per_horizon;
  let start_time = Unix.gettimeofday () in

  _log_dim "CHS" "horizon %d  (size=%d)" horizon
    (Greysynth_utils.Utils.size_of_expr expr);

  let process node =
    Greysynth_utils.Utils.increment_counter log_chs_process_per_horizon horizon;
    let n', new_leafs = truncate node horizon in

    let synthesized_expression =
      synthesize n' new_leafs synthesis_timeout synthesis_repeat
    in

    let ret =
      match synthesized_expression with
      | Some (expr, time) ->
          if !c_current_mode_is_global then
            Hashtbl.replace log_global_rules_found (n', expr)
              (match Hashtbl.find_opt log_global_rules_found (n', expr) with
              | Some (count, times) -> (count + 1, times @ [ time ])
              | None -> (1, [ time ]))
          else
            Hashtbl.replace log_chs_rules_found (n', expr)
              (match Hashtbl.find_opt log_chs_rules_found (n', expr) with
              | Some (count, horizons, times) ->
                  (count + 1, horizons @ [ horizon ], times @ [ time ])
              | None -> (1, [ horizon ], [ time ]));

          let simplified_expr = Greysynth_utils.Utils.binsec_simplify expr in
          replace_greek_vars simplified_expr new_leafs
      | None -> node
    in
    ret
  in
  let rec aux node =
    check_timeout ();
    if Greysynth_utils.Utils.depth_of_expr node < horizon then node
    else
      let outhash = !evaluator.node_to_outhash node in

      match
        (!c_local_cache, Hashtbl.find_opt chs_cache_per_horizon outhash)
      with
      | true, Some cached_node ->
          Greysynth_utils.Utils.increment_counter log_chs_cache_hits_per_horizon
            horizon;
          cached_node
      | false, _ | true, None ->
          let processed_node = process node in
          let simplified_node =
            match processed_node with
            | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (aux r.x)
            | Sexpr.Expr.Binary r -> Sexpr.Expr.binary r.f (aux r.x) (aux r.y)
            | _ -> processed_node
          in

          if !c_local_cache then
            Hashtbl.add chs_cache_per_horizon outhash simplified_node;
          simplified_node
  in
  let ret = aux expr in

  let end_time = Unix.gettimeofday () in
  let time_taken = end_time -. start_time in

  if !c_current_mode_is_global then (
    log_global_horizon := horizon;
    log_global_size_after := Greysynth_utils.Utils.size_of_expr ret;
    log_global_time := time_taken)
  else Hashtbl.replace log_chs_time_per_horizon horizon time_taken;

  _log_dim "CHS" "horizon %d done  (size=%d, %.2fs)" horizon
    (Greysynth_utils.Utils.size_of_expr ret)
    time_taken;
  ret

(* Global synthesis: traverse all nodes bottom-up, attempting synthesis on
   each complete subtree (no truncation). *)
let simplify_global synthesis_timeout synthesis_repeat (expr : Sexpr.Expr.t) =
  let start_time = Unix.gettimeofday () in
  _log "global" "starting bottom-up synthesis  (size=%d)"
    (Greysynth_utils.Utils.size_of_expr expr);

  let cache : (outhash, Sexpr.Expr.t) Hashtbl.t = Hashtbl.create 64 in

  let process node =
    check_timeout ();
    let h = Greysynth_utils.Utils.depth_of_expr node in
    if h < 2 then node (* leaf or trivially small *)
    else
      let n', new_leafs = truncate node h in
      let synthesized_expression =
        synthesize n' new_leafs synthesis_timeout synthesis_repeat
      in
      match synthesized_expression with
      | Some (synth_expr, time) ->
          Hashtbl.replace log_global_rules_found (n', synth_expr)
            (match Hashtbl.find_opt log_global_rules_found (n', synth_expr) with
            | Some (count, times) -> (count + 1, times @ [ time ])
            | None -> (1, [ time ]));
          let simplified_expr =
            Greysynth_utils.Utils.binsec_simplify synth_expr
          in
          replace_greek_vars simplified_expr new_leafs
      | None -> node
  in

  (* Bottom-up: simplify children first, then attempt synthesis on the node *)
  let rec aux node =
    check_timeout ();
    match node with
    | Sexpr.Expr.Var _ | Sexpr.Expr.Cst _ -> node
    | _ ->
        let outhash = !evaluator.node_to_outhash node in
        if !c_local_cache then (
          match Hashtbl.find_opt cache outhash with
          | Some cached_node -> cached_node
          | None ->
              let result = process_node node outhash in
              Hashtbl.replace cache outhash result;
              result)
        else process_node node outhash
  and process_node node _outhash =
    (* First, simplify children *)
    let children_simplified =
      match node with
      | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (aux r.x)
      | Sexpr.Expr.Binary r -> Sexpr.Expr.binary r.f (aux r.x) (aux r.y)
      | Sexpr.Expr.Ite r -> Sexpr.Expr.ite (aux r.c) (aux r.t) (aux r.e)
      | _ -> node
    in
    (* Then, attempt synthesis on the whole subtree *)
    process children_simplified
  in
  let ret = aux expr in

  let end_time = Unix.gettimeofday () in
  let time_taken = end_time -. start_time in
  log_global_horizon := Greysynth_utils.Utils.depth_of_expr expr;
  log_global_size_after := Greysynth_utils.Utils.size_of_expr ret;
  log_global_time := time_taken;

  _log "global" "done  (size=%d, %.2fs)"
    (Greysynth_utils.Utils.size_of_expr ret)
    time_taken;
  ret
