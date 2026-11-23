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

(** GreySynth: simplification of obfuscated (MBA) expressions. *)

val run_normalization : Sexpr.Expr.t -> Sexpr.Expr.t
(** Run the configured deterministic normalizer, optionally racing the
    baseline and AC variants and returning the cheaper proved result. *)

val run_preprocessing_portfolio : Sexpr.Expr.t option -> Sexpr.Expr.t -> Sexpr.Expr.t
(** Race configured baseline/experimental normalization+OES branches when the
    preprocessing portfolio is enabled. *)

val run_cleanup : ?whole:bool -> Sexpr.Expr.t -> Sexpr.Expr.t
(** Run the configured post-synthesis cleanup, using bounded e-graph extraction
    with safe greedy fallback when enabled. *)

val chs : Sexpr.Expr.t option -> Sexpr.Expr.t ref -> unit
(** Run the configured contextual-horizon loop in place. Exposed for focused
    regression tests and advanced pipeline integrations. *)

val run : ?proof_output:string -> Sexpr.Expr.t -> string -> Sexpr.Expr.t option -> unit
(** [run obf config_file gt] loads the JSON configuration, runs the enabled
    passes on [obf] (OES, fast simplify, global synthesis then CHS) within
    the total timeout, logs progress to stderr and prints a JSON report to
    stdout. The ground truth [gt], if given, is only used for equivalence
    checks and in the report. *)

(** When [proof_output] is supplied, write a typed rewrite certificate. Its
    equality edges require independent replay with [mba_proof]; merely writing
    the certificate does not establish equivalence. *)
