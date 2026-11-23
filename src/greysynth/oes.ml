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

(* The OES engine (Output-Equivalence Simplification): rewrite each node to the
   smallest other node sharing its semantic signature (outhash). [linear_simplify]
   is the two-pass core; [extend_node]/seed_relational pre-seed the cache with
   synthetic single-operand and relational vocabulary; [oes_with_logs] times a
   single pass and [oes_fixedpoint] iterates a pass to convergence. *)

open Logging
open Config
open Sexpr.Expr
open Sample_evaluator

let record_semantics table expr =
  let rec visit node =
    Greysynth_utils.Utils.increment_counter table (!evaluator.node_to_outhash node);
    match node with
    | Unary r -> visit r.x
    | Binary r -> visit r.x; visit r.y
    | Ite r -> visit r.c; visit r.t; visit r.e
    | _ -> ()
  in
  visit expr

(* OES vocabulary extension *)
let extend_node (n : Sexpr.Expr.t) : Sexpr.Expr.t list =
  let sz = Sexpr.Expr.sizeof n in
  let c k = Sexpr.Expr.constant (Bitvector.of_int ~size:sz k) in
  let cz z = Sexpr.Expr.constant (Bitvector.create z sz) in
  let bin f k = Sexpr.Expr.binary f n (c k) in
  let binz f z = Sexpr.Expr.binary f n (cz z) in
  let affine =
    List.concat_map (fun k -> [ bin Plus k; bin Minus k ]) [ 1; 2; 4; 8; 16 ]
  in
  let shifts =
    List.concat_map (fun k -> [ bin Lsl k; bin Lsr k; bin Asr k ]) [ 1; 2; 3 ]
  in
  let masks =
    let low_bits k = Z.sub (Z.shift_left Z.one k) Z.one in
    (* alternating bit pattern: set every [step]-th bit starting at [start] *)
    let pattern step start =
      let r = ref Z.zero in
      let i = ref start in
      while !i < sz do
        r := Z.logor !r (Z.shift_left Z.one !i);
        i := !i + step
      done;
      !r
    in
    let candidates =
      [ low_bits (min 8 sz) ]
      @ (if sz >= 4 then [ low_bits (sz / 2) ] else [])
      @ [ pattern 2 0; pattern 2 1 ]
      @ if sz >= 1 then [ Z.shift_left Z.one (sz - 1) ] else []
    in
    List.concat_map (fun z -> [ binz And z; binz Or z; binz Xor z ]) candidates
  in
  [
    Sexpr.Expr.unary Not n; Sexpr.Expr.unary Minus n; Sexpr.Expr.binary Mul n n;
  ]
  @ affine @ shifts @ masks

(* Repeated descendant value-classes of [n], within [c_local_extend_depth]
   (proper descendants only, so [n] itself is excluded). Each returned node is
   the smallest representative of a value-class (by outhash) that occurs at
   least twice. Shared by [seed_relational] and the fast-simplify relational
   pass. *)
let repeated_descendant_reps (n : Sexpr.Expr.t) : Sexpr.Expr.t array =
  let classes : (outhash, int * Sexpr.Expr.t) Hashtbl.t = Hashtbl.create 32 in
  let see node =
    let oh = !evaluator.node_to_outhash node in
    match Hashtbl.find_opt classes oh with
    | Some (c, prev) ->
        let smaller =
          if
            Greysynth_utils.Utils.size_of_expr node
            < Greysynth_utils.Utils.size_of_expr prev
          then node
          else prev
        in
        Hashtbl.replace classes oh (c + 1, smaller)
    | None -> Hashtbl.replace classes oh (1, node)
  in
  let rec collect node depth =
    if depth <= !c_local_extend_depth then (
      see node;
      match node with
      | Sexpr.Expr.Unary r -> collect r.x (depth + 1)
      | Sexpr.Expr.Binary r ->
          collect r.x (depth + 1);
          collect r.y (depth + 1)
      | Sexpr.Expr.Ite r ->
          collect r.c (depth + 1);
          collect r.t (depth + 1);
          collect r.e (depth + 1)
      | _ -> ())
  in
  (match n with
  | Sexpr.Expr.Unary r -> collect r.x 1
  | Sexpr.Expr.Binary r ->
      collect r.x 1;
      collect r.y 1
  | Sexpr.Expr.Ite r ->
      collect r.c 1;
      collect r.t 1;
      collect r.e 1
  | _ -> ());
  Hashtbl.fold
    (fun _oh (c, node) acc -> if c >= 2 then node :: acc else acc)
    classes []
  |> Array.of_list

(* Apply [emit op a b] to every X op Y over the operand array: commutative ops
   [Plus; Mul; And; Or; Xor] with canonical order i <= j (self-pairs included),
   and non-commutative [Minus] in both orders. [emit] owns the equal-size guard
   (bitvector binops require equal-width operands). *)
let iter_relational_pairs (reps : Sexpr.Expr.t array) emit : unit =
  let k = Array.length reps in
  let commutative = [ Plus; Mul; And; Or; Xor ] in
  for i = 0 to k - 1 do
    for j = i to k - 1 do
      List.iter (fun op -> emit op reps.(i) reps.(j)) commutative
    done;
    for j = 0 to k - 1 do
      emit Minus reps.(i) reps.(j)
    done
  done

let rec proof_complexity = function
  | Sexpr.Expr.Var _ | Sexpr.Expr.Cst _ -> 0
  | Sexpr.Expr.Load _ -> 20
  | Sexpr.Expr.Unary { f; x; _ } ->
      (match f with
      | Not | Minus -> 1
      | Uext _ | Sext _ | Restrict _ -> 2)
      + proof_complexity x
  | Sexpr.Expr.Binary { f; x; y; _ } ->
      let local =
        match f with
        | And | Or | Xor | Plus | Minus -> 1
        | Lsl | Lsr | Asr | Rol | Ror | Concat -> 2
        | Eq | Diff | Ule | Ult | Uge | Ugt | Sle | Slt | Sge | Sgt -> 3
        | Mul ->
            (match x, y with
            | Sexpr.Expr.Cst _, _ | _, Sexpr.Expr.Cst _ -> 3
            | _ -> 8)
        | Udiv | Sdiv | Umod | Smod -> 10
      in
      local + proof_complexity x + proof_complexity y
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      3 + proof_complexity c + proof_complexity t + proof_complexity e

let linear_simplify ?(seed = true) (expr : Sexpr.Expr.t) =
  let cache = Hashtbl.create 100 in
  let size = Greysynth_utils.Utils.size_of_expr in
  let compare_candidate left right =
    let order = Int.compare (size left) (size right) in
    let order =
      if order <> 0 then order
      else Int.compare (proof_complexity left) (proof_complexity right)
    in
    if order = 0 then Sexpr.Expr.compare left right else order
  in
  let rec take count = function
    | _ when count <= 0 -> []
    | [] -> []
    | head :: tail -> head :: take (count - 1) tail
  in
  let add_to_cache node outhash =
    let previous = Option.value (Hashtbl.find_opt cache outhash) ~default:[] in
    let candidates =
      node :: previous
      |> List.sort_uniq Sexpr.Expr.compare
      |> List.sort compare_candidate
      |> take !c_oes_candidate_limit
    in
    Hashtbl.replace cache outhash candidates
  in

  (* local_extend: relational (X op Y) vocabulary seeding. Seed [X op Y] into
     the cache for every pair of repeated descendant value-classes of [n] (see
     {!repeated_descendant_reps} / {!iter_relational_pairs}). Re-seeding a rule
     already present is a harmless no-op (add_to_cache keeps a bounded frontier
     of the smallest nodes per outhash). *)
  let seed_relational n =
    iter_relational_pairs (repeated_descendant_reps n) (fun op a b ->
        (* a bitvector binop requires equal-size operands; the window can hold
           subnodes of different widths (e.g. constants 1:64 and 1:32), so skip
           mismatched pairs. *)
        if Sexpr.Expr.sizeof a = Sexpr.Expr.sizeof b then (
          let g = Sexpr.Expr.binary op a b in
          add_to_cache g (!evaluator.node_to_outhash g);
          incr log_local_extend_injected))
  in

  (* Seed the synthetic-vocabulary caches derived from [n] (no-ops when the
     corresponding feature flags are off, or when [seed] is false). *)
  let seed_vocabulary n =
    if !c_oes_extended then
      List.iter
        (fun g ->
          add_to_cache g (!evaluator.node_to_outhash g);
          incr log_linear_vocab_injected)
        (extend_node n);
    if !c_local_extend then seed_relational n
  in

  let scanned = Sexpr.BvTbl.create 128 in
  let rec first_pass n =
    if Sexpr.BvTbl.mem scanned n then ()
    else (
      Sexpr.BvTbl.add scanned n ();
      check_timeout ();
      let outhash = !evaluator.node_to_outhash n in
      (match !evaluator.is_node_constant n with
      | Some cst ->
          (* [n] evaluates to a constant on every sample: cache the literal *)
          add_to_cache (Sexpr.Expr.constant cst) outhash
      | None ->
          add_to_cache n outhash;
          if seed then seed_vocabulary n);
      (* A constant-looking node may fail independent validation or proof.
         Its children must still be available when that candidate is rejected. *)
      recurse_into_children n)
  and recurse_into_children n =
    match n with
    | Sexpr.Expr.Unary r -> first_pass r.x
    | Sexpr.Expr.Binary r ->
        first_pass r.x;
        first_pass r.y
    | Sexpr.Expr.Ite r ->
        first_pass r.c;
        first_pass r.t;
        first_pass r.e
    | _ -> ()
  in
  let prepared =
    if !g_has_timedout then false
    else
      try first_pass expr; true with Timeout_exception ->
        g_has_timedout := true;
        false
  in

  let nb_simplifications = ref 0 in
  let rewritten = Sexpr.BvTbl.create 128 in

  let rec second_pass n =
    if !g_has_timedout then n
    else match Sexpr.BvTbl.find_opt rewritten n with
    | Some result -> result
    | None ->
      let result = try
      check_timeout ();
      let outhash = !evaluator.node_to_outhash n in

      match n with
    | Sexpr.Expr.Cst _ -> n
    | _ -> (
        let cached_nodes =
          Option.value (Hashtbl.find_opt cache outhash) ~default:[]
        in
        match List.find_opt (Rewrite.accepts ~pass:"OES" n) cached_nodes with
        | Some cached_node ->
            nb_simplifications := !nb_simplifications + 1;
            cached_node
        | None ->
          match n with
          | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (second_pass r.x)
          | Sexpr.Expr.Binary r ->
              let x = second_pass r.x in
              let y = second_pass r.y in
              Sexpr.Expr.binary r.f x y
          | Sexpr.Expr.Ite r ->
              let c = second_pass r.c in
              let t = second_pass r.t in
              let e = second_pass r.e in
              Sexpr.Expr.ite c t e
          | _ -> n)
      with Timeout_exception ->
        g_has_timedout := true;
        n
      in
      Sexpr.BvTbl.add rewritten n result;
      result
  in
  let ret = if prepared then second_pass expr else expr in
  (ret, nb_simplifications)

(* One timed OES pass over the whole tree, recording the per-pass metrics. *)
let oes_single_pass (expr : Sexpr.Expr.t) =
  _log "OES" "running linear simplification (size=%d)"
    (Greysynth_utils.Utils.size_of_expr expr);

  log_linear_vocab_injected := 0;
  log_local_extend_injected := 0;
  Hashtbl.clear log_linear_number_unique_hash_before;
  Hashtbl.clear log_linear_number_unique_hash_after;
  record_semantics log_linear_number_unique_hash_before expr;
  let start_time = Unix.gettimeofday () in
  let ret, nb_simplifications = linear_simplify expr in
  let end_time = Unix.gettimeofday () in

  if !c_oes_extended then
    _log_dim "OES" "vocabulary: %d synthetic nodes injected"
      !log_linear_vocab_injected;
  if !c_local_extend then
    _log_dim "OES" "relational: %d nodes injected" !log_local_extend_injected;

  log_linear_time := end_time -. start_time;
  log_linear_number_simplifications := !nb_simplifications;
  log_linear_size_after := Greysynth_utils.Utils.size_of_expr ret;
  record_semantics log_linear_number_unique_hash_after ret;
  tmp_uniq_semantic := Hashtbl.length log_linear_number_unique_hash_after;
  ret

(* OES entry point. Runs a single pass, or — when [c_oes_fixedpoint] is set —
   re-applies it until the result stops shrinking. OES only ever replaces a node
   with a strictly smaller equivalent, so total size is monotonically
   non-increasing and "output unchanged" is exactly "size unchanged" — a cheap,
   exact fixed-point test. A collapsed subtree can expose new sharing / vocabulary
   matches on the next round, so iterating can simplify further than one pass.
   Log totals are accumulated across iterations. *)
let oes_with_logs (expr : Sexpr.Expr.t) =
  if not !c_oes_fixedpoint then oes_single_pass expr
  else
    let total_time = ref 0.0 in
    let total_simpl = ref 0 in
    let rec loop e iter =
      if !g_has_timedout then e
      else try
      check_timeout ();
      let e' = oes_single_pass e in
      total_time := !total_time +. !log_linear_time;
      total_simpl := !total_simpl + !log_linear_number_simplifications;
      let s = Greysynth_utils.Utils.size_of_expr e in
      let s' = Greysynth_utils.Utils.size_of_expr e' in
      if s' < s && not !g_has_timedout then loop e' (iter + 1)
      else (
        _log_dim "OES" "fixed-point reached after %d iteration(s) (size=%d)"
          iter s';
        e')
      with Timeout_exception ->
        g_has_timedout := true;
        e
    in
    let result = loop expr 1 in
    log_linear_time := !total_time;
    log_linear_number_simplifications := !total_simpl;
    log_linear_size_after := Greysynth_utils.Utils.size_of_expr result;
    result

(* ------------------------------------------------------------------ *)
(* fast_simplify                                                       *)
(* ------------------------------------------------------------------ *)

(* Step 2 (directed relational), one traversal. For each non-constant node [n],
   build every  X op Y  over [n]'s repeated descendant value-classes; if a combo
   reproduces [n]'s outhash and is strictly smaller, replace [n] with the
   smallest such combo and recurse into the replacement's children, otherwise
   recurse into [n]'s children unchanged. Returns the tree and the number of
   replacements made. *)
let relational_pass (expr : Sexpr.Expr.t) : Sexpr.Expr.t * int =
  let size = Greysynth_utils.Utils.size_of_expr in
  let replacements = ref 0 in
  let rec go n =
    if !g_has_timedout then n
    else
      match n with
      | Sexpr.Expr.Cst _ -> n
      | _ ->
          let best = ref None in
          (* Keep an already validated candidate if a later candidate or
             descendant exhausts the budget. Never retain an unfinished proof. *)
          (try
             check_timeout ();
             let target = !evaluator.node_to_outhash n in
             let sz_n = size n in
             let consider g =
               check_timeout ();
               if size g < sz_n && !evaluator.node_to_outhash g = target
                  && Rewrite.accepts ~pass:"relational" n g then
                 match !best with
                 | Some previous when size previous <= size g -> ()
                 | _ -> best := Some g
             in
             let rec invert_kids node depth =
               if depth <= !c_local_extend_depth then (
                 consider (Sexpr.Expr.unary Not node);
                 match node with
                 | Sexpr.Expr.Unary r -> invert_kids r.x (depth + 1)
                 | Sexpr.Expr.Binary r ->
                     invert_kids r.x (depth + 1);
                     invert_kids r.y (depth + 1)
                 | _ -> ())
             in
             invert_kids n 0;
             iter_relational_pairs (repeated_descendant_reps n) (fun op a b ->
                 check_timeout ();
                 if Sexpr.Expr.sizeof a = Sexpr.Expr.sizeof b then
                   consider (Sexpr.Expr._binary op a b))
           with Timeout_exception -> g_has_timedout := true);
          let chosen =
            match !best with
            | Some candidate -> incr replacements; candidate
            | None -> n
          in
          if !g_has_timedout then chosen else recurse_children chosen
  and recurse_children n =
    match n with
    | Sexpr.Expr.Unary r -> Sexpr.Expr.unary r.f (go r.x)
    | Sexpr.Expr.Binary r ->
        let x = go r.x in
        let y = go r.y in
        Sexpr.Expr.binary r.f x y
    | Sexpr.Expr.Ite r ->
        let c = go r.c in
        let t = go r.t in
        let e = go r.e in
        Sexpr.Expr.ite c t e
    | _ -> n
  in
  let ret = go expr in
  (ret, !replacements)

(* fast_simplify: step 1 = one base-OES pass (no synthetic vocabulary: redundant
   semantics and constants collapse to the smallest node); step 2 = the
   relational directed pass iterated to a size fixed point. Every substitution
   is strictly smaller, so total size is monotonically non-increasing and "size
   unchanged" is exactly the fixed point. Returns the tree with the base-OES and
   relational replacement counts. *)
let fast_simplify_counted (expr : Sexpr.Expr.t) : Sexpr.Expr.t * int * int =
  let size = Greysynth_utils.Utils.size_of_expr in
  let base, base_simpl_ref = linear_simplify ~seed:false expr in
  let relational = ref 0 in
  let rec loop e =
    if !g_has_timedout then e
    else try
      check_timeout ();
      let e', changed = relational_pass e in
      relational := !relational + changed;
      if changed > 0 && size e' < size e && not !g_has_timedout then loop e' else e'
    with Timeout_exception ->
      g_has_timedout := true;
      e
  in
  let ret = loop base in
  (ret, !base_simpl_ref, !relational)

let fast_simplify (expr : Sexpr.Expr.t) : Sexpr.Expr.t =
  let ret, _, _ = fast_simplify_counted expr in
  ret

(* One timed fast_simplify run, recording per-pass metrics into the linear
   log slots (shared with OES) so the reporting picks them up. *)
let fast_simplify_with_logs (expr : Sexpr.Expr.t) : Sexpr.Expr.t =
  let size = Greysynth_utils.Utils.size_of_expr in
  _log "OES" "running fast_simplify (size=%d)" (size expr);
  Hashtbl.clear log_linear_number_unique_hash_before;
  Hashtbl.clear log_linear_number_unique_hash_after;
  record_semantics log_linear_number_unique_hash_before expr;
  let start_time = Unix.gettimeofday () in
  let ret, base_simpl, relational = fast_simplify_counted expr in
  let end_time = Unix.gettimeofday () in
  log_linear_time := end_time -. start_time;
  log_linear_number_simplifications := base_simpl + relational;
  log_linear_size_after := size ret;
  record_semantics log_linear_number_unique_hash_after ret;
  tmp_uniq_semantic := Hashtbl.length log_linear_number_unique_hash_after;
  _log_dim "OES"
    "fast_simplify: %d base + %d relational replacement(s) (size=%d, %.3fs)"
    base_simpl relational (size ret) (end_time -. start_time);
  ret
