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

let associative = function
  | Plus | Mul | And | Or | Xor -> true
  | _ -> false

(* Reassociation is used only to construct a synthesis target. The concrete
   source tree is retained and every returned candidate is still restored and
   proved against it. This lets [balanced_tree] influence CHS horizons without
   introducing equal-cost rewrites or rewrite cycles in the result tree. *)
let balance_associative expr =
  let rec normalize node =
    match node with
    | Unary r -> unary r.f (normalize r.x)
    | Binary r when associative r.f ->
        let rec flatten acc node =
          match node with
          | Binary child when child.f = r.f ->
              flatten (flatten acc child.x) child.y
          | child -> normalize child :: acc
        in
        let terms = flatten (flatten [] r.x) r.y |> List.sort Sexpr.Expr.compare in
        let rec build = function
          | [] -> assert false
          | [ term ] -> term
          | terms ->
              let count = List.length terms in
              let left_count = count / 2 in
              let rec split n left rest =
                if n = 0 then (List.rev left, rest)
                else match rest with
                  | head :: tail -> split (n - 1) (head :: left) tail
                  | [] -> assert false
              in
              let left, right = split left_count [] terms in
              binary r.f (build left) (build right)
        in
        build terms
    | Binary r -> binary r.f (normalize r.x) (normalize r.y)
    | Ite r -> ite (normalize r.c) (normalize r.t) (normalize r.e)
    | _ -> node
  in
  normalize expr

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
    (* Repeated value classes may contain very different-sized subtrees.
       Restoring the smallest one gives synthesis the best chance to shrink
       the original expression. The final contextual check remains mandatory. *)
    (match Hashtbl.find_opt new_leafs labelled_var with
    | Some previous when size_of_expr previous <= size_of_expr node -> ()
    | _ -> Hashtbl.replace new_leafs labelled_var node);
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
  let target = if !c_balanced_tree then balance_associative expr else expr in
  let truncated_expression = aux target depth in

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

  (* The evaluator uses total SMT-LIB semantics, so every subtree and
     label is sampled on exactly the same input ids, including division by
     zero. *)
  let samples =
    Array.init !c_nb_samples (fun id ->
        let contextual leaf = !evaluator.eval_label leaf id new_leafs in
        let independent leaf = !evaluator.eval leaf id in
        let args, res =
          match !c_sampling_strategy with
          | RealValues ->
              (List.map contextual leaves, !evaluator.eval_label e id new_leafs)
          | LabelValues ->
              (List.map independent leaves, !evaluator.eval e id)
          | WrongNaive ->
              (* Historical ablation: independent label inputs paired with the
                 contextual output. Proof gating prevents this deliberately
                 inconsistent specification from corrupting the result. *)
              (List.map independent leaves, !evaluator.eval_label e id new_leafs)
        in
        { Synth_backends.args = Array.of_list args; res })
  in

  let operators =
    let rec inspect (profile : Synth_backends.operator_profile) = function
      | Unary { x; _ } -> inspect profile x
      | Binary { f; x; y; _ } ->
          let profile =
            match f with
            | Lsl | Lsr | Asr | Rol | Ror -> { profile with shifts = true }
            | Udiv | Sdiv | Umod | Smod -> { profile with division = true }
            | _ -> profile
          in
          inspect (inspect profile x) y
      | Ite { c; t; e; _ } ->
          let profile = { profile with conditional = true } in
          inspect (inspect (inspect profile c) t) e
      | _ -> profile
    in
    inspect { Synth_backends.shifts = false; division = false; conditional = false } e
  in
  let constants =
    let rec find_csts (node : Sexpr.Expr.t) : Bitvector.t list =
      match node with
      | Sexpr.Expr.Cst c -> [ c ]
      | Sexpr.Expr.Unary r -> find_csts r.x
      | Sexpr.Expr.Binary r -> find_csts r.x @ find_csts r.y
      | Sexpr.Expr.Ite r -> find_csts r.c @ find_csts r.t @ find_csts r.e
      | _ -> []
    in
    if not !c_add_constants_to_synthesis then []
    else
      let original = find_csts e |> List.sort_uniq Bitvector.compare in
      let widths =
        Sexpr.Expr.sizeof e :: List.map Bitvector.size_of original
        |> List.sort_uniq Int.compare
      in
      let seeds =
        List.concat_map
          (fun width ->
            [ Bitvector.zeros width; Bitvector.ones width;
              Bitvector.of_int ~size:width 2; Bitvector.fill width ])
          widths
      in
      let unary =
        List.concat_map
          (fun value -> [ Bitvector.neg value; Bitvector.lognot value ])
          original
      in
      let pairs =
        List.concat_map
          (fun left ->
            original
            |> List.filter (fun right -> Bitvector.size_of left = Bitvector.size_of right)
            |> List.concat_map (fun right ->
                   [ Bitvector.add left right; Bitvector.sub left right;
                     Bitvector.sub right left; Bitvector.logxor left right ]))
          original
      in
      let ranked = original @ seeds @ unary @ pairs in
      let seen = Hashtbl.create 32 in
      let rec unique count = function
        | _ when count >= 32 -> []
        | [] -> []
        | value :: rest ->
            let key = (Bitvector.size_of value, Bitvector.value_of value) in
            if Hashtbl.mem seen key then unique count rest
            else (
              Hashtbl.add seen key ();
              value :: unique (count + 1) rest)
      in
      unique 0 ranked
  in
  {
    inputs;
    output_size = Sexpr.Expr.sizeof e;
    samples;
    constants;
    operators;
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

let replace_greek_vars expr new_leafs =
  let rec aux node =
    match Hashtbl.find_opt new_leafs node with
    | Some original -> original
    | None -> (
        match node with
        | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (aux r.x)
        | Sexpr.Expr.Binary r -> Sexpr.Expr.binary r.f (aux r.x) (aux r.y)
        | Sexpr.Expr.Ite r -> Sexpr.Expr.ite (aux r.c) (aux r.t) (aux r.e)
        | _ -> node)
  in
  aux expr

(* The legacy algebraic simplifier is an optional candidate generator, not
   a trusted step: some of its rules assume nonzero divisors or host-sized
   shifts. Restore the raw backend result first so failed preparation or
   rejected algebraic rewrites cannot lose an otherwise useful synthesis. *)
let prepare_candidates synth_expr new_leafs =
  try
    let raw = replace_greek_vars synth_expr new_leafs in
    try
      let simplified =
        replace_greek_vars
          (Greysynth_utils.Utils.binsec_simplify synth_expr) new_leafs
      in
      if size_of_expr simplified < size_of_expr raw then [ simplified; raw ]
      else [ raw ]
    with
    | Timeout_exception -> raise Timeout_exception
    | exn ->
        _log_warn "synth" "algebraic simplification failed: %s; validating raw result"
          (Printexc.to_string exn);
        [ raw ]
  with
  | Timeout_exception -> raise Timeout_exception
  | exn ->
      _log_warn "synth" "discarding an unusable backend result: %s"
        (Printexc.to_string exn);
      []

let synthesize ~original e new_leafs synthesis_timeout synthesis_repeat =
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
      (* Cut leaves are correlated by the original expression. Check the
         concrete replacement, after restoring them and simplifying, against
         the original subtree. Template size/equivalence is insufficient. *)
      let previous_size = Greysynth_utils.Utils.size_of_expr original in
      let mode = if !c_current_mode_is_global then "global" else "CHS" in
      let candidate =
        prepare_candidates synth_expr new_leafs
        |> List.find_opt (Rewrite.accepts ~pass:mode original)
      in
      let is_simplification = Option.is_some candidate in
      if !c_current_mode_is_global then
        log_global_synthesis_attempts :=
          (previous_size, true, time, is_simplification)
          :: !log_global_synthesis_attempts
      else
        log_chs_synthesis_attempts :=
          (previous_size, true, time, is_simplification)
          :: !log_chs_synthesis_attempts;

      match candidate with
      | Some candidate ->
        let synth_size = Greysynth_utils.Utils.size_of_expr candidate in
        if !c_current_mode_is_global then
          log_global_number_simplifications :=
            !log_global_number_simplifications + 1
        else
          log_chs_number_simplifications :=
            !log_chs_number_simplifications + 1;

        _log_ok mode "\027[32m%d -> %d\027[0m  (%.2fs)  %s" previous_size
          synth_size time
          (Greysynth_utils.Utils.pp candidate);
        Some (synth_expr, candidate, time)
      | None -> None

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
      synthesize ~original:node n' new_leafs synthesis_timeout synthesis_repeat
    in

    let ret =
      match synthesized_expression with
      | Some (expr, candidate, time) ->
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

          candidate
      | None -> node
    in
    ret
  in
  let rec aux node =
    if !g_has_timedout then node
    else try
    check_timeout ();
    if Greysynth_utils.Utils.depth_of_expr node < horizon then node
    else
      let outhash = !evaluator.node_to_outhash node in

      match
        (!c_local_cache, Hashtbl.find_opt chs_cache_per_horizon outhash)
      with
      | true, Some cached_node
        when Sexpr.Expr.compare node cached_node = 0
             || Rewrite.accepts ~pass:"CHS cache" node cached_node ->
          Greysynth_utils.Utils.increment_counter log_chs_cache_hits_per_horizon
            horizon;
          cached_node
      | false, _ | true, _ ->
          let processed_node = process node in
          let simplified_node =
            match processed_node with
            | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (aux r.x)
            | Sexpr.Expr.Binary r ->
                let x = aux r.x in
                let y = aux r.y in
                Sexpr.Expr.binary r.f x y
            | Sexpr.Expr.Ite r ->
                let c = aux r.c in
                let t = aux r.t in
                let e = aux r.e in
                Sexpr.Expr.ite c t e
            | _ -> processed_node
          in

          if !c_local_cache && not !g_has_timedout then
            Hashtbl.replace chs_cache_per_horizon outhash simplified_node;
          simplified_node
    with Timeout_exception ->
      g_has_timedout := true;
      node
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
        synthesize ~original:node n' new_leafs synthesis_timeout synthesis_repeat
      in
      match synthesized_expression with
      | Some (synth_expr, candidate, time) ->
          Hashtbl.replace log_global_rules_found (n', synth_expr)
            (match Hashtbl.find_opt log_global_rules_found (n', synth_expr) with
            | Some (count, times) -> (count + 1, times @ [ time ])
            | None -> (1, [ time ]));
          candidate
      | None -> node
  in

  (* Bottom-up: simplify children first, then attempt synthesis on the node *)
  let rec aux node =
    if !g_has_timedout then node
    else try
    check_timeout ();
    match node with
    | Sexpr.Expr.Var _ | Sexpr.Expr.Cst _ -> node
    | _ ->
        let outhash = !evaluator.node_to_outhash node in
        if !c_local_cache then (
          match Hashtbl.find_opt cache outhash with
          | Some cached_node
            when Sexpr.Expr.compare node cached_node = 0
                 || Rewrite.accepts ~pass:"global cache" node cached_node ->
              cached_node
          | _ ->
              let result = process_node node outhash in
              Hashtbl.replace cache outhash result;
              result)
        else process_node node outhash
    with Timeout_exception ->
      g_has_timedout := true;
      node
  and process_node node _outhash =
    (* First, simplify children *)
    let children_simplified =
      match node with
      | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (aux r.x)
      | Sexpr.Expr.Binary r ->
          let x = aux r.x in
          let y = aux r.y in
          Sexpr.Expr.binary r.f x y
      | Sexpr.Expr.Ite r ->
          let c = aux r.c in
          let t = aux r.t in
          let e = aux r.e in
          Sexpr.Expr.ite c t e
      | _ -> node
    in
    (* A parent timeout must preserve the completed child rewrites. *)
    if !g_has_timedout then children_simplified
    else try process children_simplified with Timeout_exception ->
      g_has_timedout := true;
      children_simplified
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
