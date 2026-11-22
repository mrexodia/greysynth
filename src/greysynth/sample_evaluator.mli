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

(** Concrete bitvector evaluation on a fixed bank of shared input samples.

    The first five samples are 0, 1, -1, maximum signed and minimum signed
    values at each variable's width; the remaining samples are random.
    Variables are sampled once per id and shared by every expression.
    Operations follow SMT-LIB bitvector semantics, including oversized shifts
    and division by zero. *)

type outhash
(** Complete, width-aware output vector. Despite the historical name, this is
    not an integer hash: equality compares every sampled output. Agreement on
    a finite sample bank is still a heuristic, not an equivalence proof. *)

module Fingerprint : sig
  type t = outhash
end

type t = {
  eval : Sexpr.Expr.t -> int -> Bitvector.t;
      (** [eval e i] evaluates [e] on sample [i], caching by complete expression
          keys. Any nonnegative id is valid, including held-out samples. *)
  eval_all : Sexpr.Expr.t -> unit;
      (** Evaluate [e] on all configured samples. *)
  reset : int -> unit;
      (** Forget one sample and invalidate any signatures that include it. *)
  node_to_fingerprint : Sexpr.Expr.t -> Fingerprint.t;
      (** Outputs on exactly the configured sample ids. *)
  node_to_outhash : Sexpr.Expr.t -> outhash;
      (** Same complete signature as [node_to_fingerprint]. *)
  is_node_constant : Sexpr.Expr.t -> Bitvector.t option;
      (** [Some v] if every configured sample produces [v]; evaluates missing
          samples rather than relying on a partially populated cache. *)
  eval_label :
    Sexpr.Expr.t -> int -> (Sexpr.Expr.t, Sexpr.Expr.t) Hashtbl.t -> Bitvector.t;
      (** Same semantics as [eval], substituting the cut subtrees in [labels].
          Unbound variables in the truncated expression are rejected. *)
}

val eval_with_bindings :
  (Sexpr.Expr.t, Bitvector.t) Hashtbl.t -> Sexpr.Expr.t -> Bitvector.t
(** Evaluate with an explicit environment. Every variable must be bound. *)

val make : int -> t
(** [make n] creates a fresh evaluator. [n] must be positive. *)
