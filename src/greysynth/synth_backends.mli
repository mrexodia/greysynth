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

(** Synthesis backends.

    A backend gets a {!problem} (input/output samples of an unknown function)
    and returns an expression over the problem's inputs that fits them, or
    [None]. {!Synthesis} builds the problem from a (truncated) subtree, calls
    the backend selected by the ["synthesizer"] config key, and keeps the
    answer only if it passes {!well_formed}. A backend may also raise on
    failure: the caller logs the exception and counts the attempt as failed.

    Available backends: [xyntia] (in-process), [syntia] (Python script),
    [cvc5] (SyGuS). Adding one only touches [synth_backends.ml], not this
    interface: see the instructions at the top of that file. *)

(** An input of the unknown function: a cut leaf, usually a Greek letter. *)
type input = { name : string; size : int }

type sample = {
  args : Bitvector.t array;  (** one value per input, in [inputs] order *)
  res : Bitvector.t;  (** output value, [output_size] bits *)
}

type operator_profile = { shifts : bool; division : bool; conditional : bool }

type problem = {
  inputs : input array;
  output_size : int;
  samples : sample array;
  constants : Bitvector.t list;
      (** constants of the original subtree when
          ["add_constants_to_synthesis"] is set, else empty; a hint backends
          are free to ignore *)
  operators : operator_profile;
  timeout : int;  (** seconds *)
  repeat : int;  (** attempts, for randomised backends *)
}

type synthesizer = problem -> Sexpr.Expr.t option

(** What a backend implements. *)
module type BACKEND = sig
  val name : string
  (** Value of the ["synthesizer"] config key that selects this backend. *)

  val make : Yojson.Basic.t -> synthesizer
  (** Called once with the whole config JSON: read backend-specific keys
      here, then return the synthesis function. *)
end

val xyntia_tree_to_expr : unit Xyntia_utils.Tree.t -> Sexpr.Expr.t
(** Translate a Xyntia result without dropping width or ternary-operator
    semantics. Exposed so the backend contract can be tested exhaustively. *)

val xyntia_grammar_for_profile : string -> operator_profile -> string
(** Resolve [auto] to the narrowest Xyntia grammar covering a target. *)

val cvc5_sygus_problem : problem -> string
(** Render the cvc5 problem. Exposed for grammar-contract tests. *)

val cvc5_parse_answer : problem -> string -> Sexpr.Expr.t option
(** Parse a cvc5 SyGuS answer, including conditional relations. *)

val names : string list
(** Names of the available backends. *)

val select : string -> Yojson.Basic.t -> synthesizer
(** [select name config] is the backend called [name], configured from the
    config JSON.
    @raise Failure if no backend has that name. *)

val well_formed : problem -> Sexpr.Expr.t -> bool
(** A result is usable only if it has width [output_size] and mentions
    nothing but the problem's inputs (and constants). *)
