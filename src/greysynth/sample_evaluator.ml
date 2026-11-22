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

(* Sample evaluator. Cache complete expression keys and retain every sampled
   output: a bounded structural hash is only a bucket selector, never evidence
   of output equivalence. *)

open Libterm.Sexpr

type outhash = { digest : int; values : Bitvector.t list }

(* The full vector decides equality. A digest over every output comes first
   so ordinary OCaml hash tables do not put all signatures with the same
   corner-sample prefix into one bucket. *)
let signature values =
  let digest =
    List.fold_left
      (fun seed value ->
        Hashtbl.seeded_hash seed
          (Bitvector.size_of value, Z.hash (Bitvector.value_of value)))
      0 values
  in
  { digest; values }

module Fingerprint = struct
  type t = outhash
end

type t = {
  eval : Expr.t -> int -> Bitvector.t;
  eval_all : Expr.t -> unit;
  reset : int -> unit;
  node_to_fingerprint : Expr.t -> Fingerprint.t;
  node_to_outhash : Expr.t -> outhash;
  is_node_constant : Expr.t -> Bitvector.t option;
  eval_label :
    Expr.t -> int -> (Sexpr.Expr.t, Sexpr.Expr.t) Hashtbl.t -> Bitvector.t;
}

let variables_of_expr expression =
  let variables = Hashtbl.create 16 in
  let rec visit = function
    | Expr.Var variable -> Hashtbl.replace variables (variable.name, variable.size) ()
    | Expr.Unary { x; _ } -> visit x
    | Expr.Binary { x; y; _ } -> visit x; visit y
    | Expr.Ite { c; t; e; _ } -> visit c; visit t; visit e
    | _ -> ()
  in
  visit expression;
  Hashtbl.fold (fun variable () result -> variable :: result) variables []
  |> List.sort compare

let deterministic_random ~seed ~name ~size sample_id =
  let state = Random.State.make [| seed; Hashtbl.hash name; size; sample_id |] in
  let rec bits remaining shift result =
    if remaining <= 0 then result
    else
      let count = min 30 remaining in
      let mask = (1 lsl count) - 1 in
      let chunk = Random.State.bits state land mask |> Z.of_int in
      bits (remaining - count) (shift + count)
        (Z.logor result (Z.shift_left chunk shift))
  in
  Bitvector.create (bits size 0 Z.zero) size

let sample_value ~seed ~ranks ~variable_count ~name ~size sample_id =
  match sample_id with
  | 0 -> Bitvector.zeros size
  | 1 -> Bitvector.ones size
  | 2 -> Bitvector.fill size
  | 3 -> Bitvector.max_sbv size
  | 4 -> Bitvector.min_sbv size
  | id when id < 5 + variable_count ->
      let rank = Hashtbl.find_opt ranks (name, size) in
      if rank = Some (id - 5) then Bitvector.ones size else Bitvector.zeros size
  | id ->
      let offset = id - 5 - variable_count in
      let bit = if size = 0 then 0 else offset mod size in
      (match offset mod 7 with
      | 0 -> Bitvector.create (Z.shift_left Z.one bit) size
      | 1 ->
          Bitvector.create
            (Z.logxor (Z.pred (Z.shift_left Z.one size)) (Z.shift_left Z.one bit))
            size
      | 2 -> Bitvector.create (Z.pred (Z.shift_left Z.one (bit + 1))) size
      | 3 ->
          let value = ref Z.zero in
          for index = 0 to size - 1 do
            if index mod 2 = 0 then
              value := Z.logor !value (Z.shift_left Z.one index)
          done;
          Bitvector.create !value size
      | 4 -> Bitvector.create (Z.shift_left Z.one (max 0 (size - 1))) size
      | 5 -> deterministic_random ~seed ~name ~size id
      | _ ->
          let random = deterministic_random ~seed ~name ~size id in
          Bitvector.of_int ~size
            ((Z.to_int (Z.rem (Bitvector.value_of random) (Z.of_int 101))) - 50))

(* SMT-LIB operations are total. In particular, shift counts are unsigned
   bitvectors, not host integers or x86-masked amounts. Bound them before
   converting to int, and reduce rotates modulo the operand's actual width.
   Keeping division-by-zero samples avoids changing the shared input bank
   halfway through an OES pass. *)
let eval_binary f x y =
  let width = Bitvector.size_of x in
  if f <> Expr.Concat && width <> Bitvector.size_of y then
    invalid_arg "sample evaluator: binary operand widths differ";
  let count = Bitvector.value_of y in
  match f with
  | Expr.Lsl | Expr.Lsr | Expr.Asr ->
      if Z.geq count (Z.of_int width) then
        if f = Expr.Asr && Bitvector.is_neg x then Bitvector.fill width
        else Bitvector.zeros width
      else
        let amount = Z.to_int count in
        (match f with
        | Expr.Lsl -> Bitvector.shift_left x amount
        | Expr.Lsr -> Bitvector.shift_right x amount
        | _ -> Bitvector.shift_right_signed x amount)
  | Expr.Rol | Expr.Ror ->
      let amount = Z.to_int (Z.rem count (Z.of_int width)) in
      if f = Expr.Rol then Bitvector.rotate_left x amount
      else Bitvector.rotate_right x amount
  | Expr.Udiv when Bitvector.is_zeros y -> Bitvector.fill width
  | Expr.Sdiv when Bitvector.is_zeros y ->
      if Bitvector.is_neg x then Bitvector.ones width
      else Bitvector.fill width
  | Expr.Umod | Expr.Smod when Bitvector.is_zeros y -> x
  | _ -> Term.Bv.binary f x y

let rec eval_with_bindings (bindings : (Expr.t, Bitvector.t) Hashtbl.t)
    (node : Expr.t) : Bitvector.t =
  match Hashtbl.find_opt bindings node with
  | Some value -> value
  | None ->
      match node with
      | Expr.Cst value -> value
      | Expr.Var _ -> invalid_arg "sample evaluator: unbound explicit variable"
      | Expr.Unary { f; x; _ } -> Term.Bv.unary f (eval_with_bindings bindings x)
      | Expr.Binary { f; x; y; _ } ->
          eval_binary f (eval_with_bindings bindings x) (eval_with_bindings bindings y)
      | Expr.Ite { c; t; e; _ } ->
          if Bitvector.is_zeros (eval_with_bindings bindings c) then
            eval_with_bindings bindings e
          else eval_with_bindings bindings t
      | Expr.Load _ -> invalid_arg "sample evaluator: memory load"

let make ?(variables = []) ?(seed = 0) nb_samples : t =
  if nb_samples <= 0 then
    invalid_arg "sample evaluator: nb_samples must be positive";

  let ranks = Hashtbl.create (List.length variables) in
  List.iteri (fun index variable -> Hashtbl.replace ranks variable index) variables;
  let variable_count = List.length variables in

  (* Allocate sample tables lazily rather than indexing a fixed retry array.
     Public callers can safely request held-out samples with any nonnegative
     id; signatures always use exactly ids 0 .. nb_samples - 1. *)
  let nodes_val : (int, Bitvector.t Sexpr.BvTbl.t) Hashtbl.t =
    Hashtbl.create nb_samples
  in
  let fingerprints : Fingerprint.t Sexpr.BvTbl.t = Sexpr.BvTbl.create 100 in
  let sample_cache sample_id =
    if sample_id < 0 then
      invalid_arg "sample evaluator: sample id must be nonnegative";
    match Hashtbl.find_opt nodes_val sample_id with
    | Some cache -> cache
    | None ->
        let cache = Sexpr.BvTbl.create 32 in
        Hashtbl.add nodes_val sample_id cache;
        cache
  in

  let rec eval (node : Expr.t) (sample_id : int) : Bitvector.t =
    let cache = sample_cache sample_id in
    match Sexpr.BvTbl.find_opt cache node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | Expr.Cst n -> n
          | Expr.Var v ->
              sample_value ~seed ~ranks ~variable_count ~name:v.name ~size:v.size sample_id
          | Expr.Unary { f; x; _ } -> Term.Bv.unary f (eval x sample_id)
          | Expr.Binary { f; x; y; _ } ->
              eval_binary f (eval x sample_id) (eval y sample_id)
          | Expr.Ite { c; t; e; _ } ->
              if Bitvector.is_zeros (eval c sample_id) then eval e sample_id
              else eval t sample_id
          | Expr.Load _ -> invalid_arg "sample evaluator: memory load"
        in
        Sexpr.BvTbl.add cache node result;
        result
  in

  let rec eval_label (node : Expr.t) (sample_id : int)
      (relations : (Expr.t, Expr.t) Hashtbl.t) : Bitvector.t =
    if sample_id < 0 then
      invalid_arg "sample evaluator: sample id must be nonnegative";
    match Hashtbl.find_opt relations node with
    | Some labeled_node -> eval labeled_node sample_id
    | None ->
        match node with
        | Expr.Unary { f; x; _ } ->
            Term.Bv.unary f (eval_label x sample_id relations)
        | Expr.Binary { f; x; y; _ } ->
            eval_binary f
              (eval_label x sample_id relations)
              (eval_label y sample_id relations)
        | Expr.Cst n -> n
        | Expr.Ite { c; t; e; _ } ->
            if Bitvector.is_zeros (eval_label c sample_id relations) then
              eval_label e sample_id relations
            else eval_label t sample_id relations
        | Expr.Var _ ->
            invalid_arg "sample evaluator: unbound synthesis label"
        | Expr.Load _ -> invalid_arg "sample evaluator: memory load"
  in

  let reset sample_id =
    if sample_id < 0 then
      invalid_arg "sample evaluator: sample id must be nonnegative";
    Hashtbl.remove nodes_val sample_id;
    if sample_id < nb_samples then Sexpr.BvTbl.clear fingerprints
  in

  let node_to_fingerprint (expr : Expr.t) : Fingerprint.t =
    match Sexpr.BvTbl.find_opt fingerprints expr with
    | Some signature -> signature
    | None ->
        let outputs = signature (List.init nb_samples (eval expr)) in
        Sexpr.BvTbl.add fingerprints expr outputs;
        outputs
  in

  let node_to_outhash = node_to_fingerprint in

  let eval_all expr = ignore (node_to_fingerprint expr) in

  let is_node_constant expr =
    match (node_to_fingerprint expr).values with
    | first :: rest when List.for_all (Bitvector.equal first) rest -> Some first
    | _ -> None
  in

  {
    eval;
    eval_all;
    reset;
    node_to_outhash;
    node_to_fingerprint;
    is_node_constant;
    eval_label;
  }
