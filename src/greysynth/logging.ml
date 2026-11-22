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

(* Logging helpers and the mutable log/metric state collected while
   simplifying. These globals are written throughout the pipeline and read
   back by the reporting code in the driver. *)

open Greysynth_utils.Utils

(* ── Metric / log state ────────────────────────────────────────── *)
let log_obfuscated_expression = ref Sexpr.Expr.zero
let log_linear_size_after = ref 0
let log_linear_number_simplifications = ref 0
let log_linear_vocab_injected = ref 0
let log_local_extend_injected = ref 0
let log_linear_number_unique_hash_before : (Sample_evaluator.outhash, int) Hashtbl.t =
  Hashtbl.create 100

let log_linear_number_unique_hash_after : (Sample_evaluator.outhash, int) Hashtbl.t =
  Hashtbl.create 100

let log_linear_time = ref 0.0
let log_normalization_is_equiv = ref Disabled
let log_linear_is_equiv = ref Disabled
let log_fast_simplify_is_equiv = ref Disabled
let log_global_size_after = ref 0
let log_global_time = ref 0.0
let log_global_number_simplifications = ref 0

type synthesis_attempt = {
  input_size : int;
  status : string;
  time : float;
  is_simplification : bool;
}

let log_global_synthesis_attempts : synthesis_attempt list ref = ref []

let log_global_horizon = ref 0

let log_global_rules_found :
    (Sexpr.Expr.t * Sexpr.Expr.t, int * float list) Hashtbl.t =
  Hashtbl.create 100

let log_global_is_equiv = ref Disabled
let log_chs_size_after = ref 0
let log_chs_synthesis_attempts : synthesis_attempt list ref = ref []
let log_chs_number_simplifications = ref 0
let log_chs_time = ref 0.0
let log_chs_time_per_horizon : (int, float) Hashtbl.t = Hashtbl.create 10
let log_chs_process_per_horizon : (int, int) Hashtbl.t = Hashtbl.create 10
let log_chs_cache_hits_per_horizon : (int, int) Hashtbl.t = Hashtbl.create 10

let log_chs_rules_found :
    (Sexpr.Expr.t * Sexpr.Expr.t, int * int list * float list) Hashtbl.t =
  Hashtbl.create 100

let tmp_uniq_semantic = ref 0
let log_chs_is_equiv = ref Disabled
let log_final_is_equiv = ref Disabled

let reset () =
  log_obfuscated_expression := Sexpr.Expr.zero;
  log_linear_size_after := 0;
  log_linear_number_simplifications := 0;
  log_linear_vocab_injected := 0;
  log_local_extend_injected := 0;
  Hashtbl.clear log_linear_number_unique_hash_before;
  Hashtbl.clear log_linear_number_unique_hash_after;
  log_linear_time := 0.;
  log_normalization_is_equiv := Disabled;
  log_linear_is_equiv := Disabled;
  log_fast_simplify_is_equiv := Disabled;
  log_global_size_after := 0;
  log_global_time := 0.;
  log_global_number_simplifications := 0;
  log_global_synthesis_attempts := [];
  log_global_horizon := 0;
  Hashtbl.clear log_global_rules_found;
  log_global_is_equiv := Disabled;
  log_chs_size_after := 0;
  log_chs_synthesis_attempts := [];
  log_chs_number_simplifications := 0;
  log_chs_time := 0.;
  Hashtbl.clear log_chs_time_per_horizon;
  Hashtbl.clear log_chs_process_per_horizon;
  Hashtbl.clear log_chs_cache_hits_per_horizon;
  Hashtbl.clear log_chs_rules_found;
  tmp_uniq_semantic := 0;
  log_chs_is_equiv := Disabled;
  log_final_is_equiv := Disabled

(* ── Logging helpers ───────────────────────────────────────────── *)
let _log section fmt =
  Format.eprintf ("\027[1;34m[%s]\027[0m " ^^ fmt ^^ "\n%!") section

let _log_dim section fmt =
  Format.eprintf ("\027[2m[%s] " ^^ fmt ^^ "\027[0m\n%!") section

let _log_ok section fmt =
  Format.eprintf ("\027[1;32m[%s]\027[0m " ^^ fmt ^^ "\n%!") section

let _log_warn section fmt =
  Format.eprintf ("\027[1;33m[%s]\027[0m " ^^ fmt ^^ "\n%!") section

let _log_header title =
  let bar = String.make 50 '-' in
  Format.eprintf
    "\n\027[1;36m%s\027[0m\n\027[1m  %s\027[0m\n\027[1;36m%s\027[0m\n%!" bar title
    bar
