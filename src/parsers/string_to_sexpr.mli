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

(** Parse pure bit-vector expression strings into [Sexpr.Expr.t].

    Operators, by increasing precedence (standard operators follow C):
    + ternary [? :], right associative
    + [|], then [^], then [&]
    + [==] (also [=]), [!=]
    + [<], [<=], [>], [>=] (unsigned), with explicit [u] or [s] suffixes
      available, e.g. [<u] and [<=s]
    + [<<], [>>] (logical), [>>s] (arithmetic), [rol], [ror], [++] (concat)
    + [+], [-]
    + [*], [/], [/s], [%], [%s] ([s]: signed)
    + [**] (constant exponent; [2 ** expr] also accepts variable exponents)
    + unary [~] (bitwise), [!] (1-bit logical negation), [-],
      [uext(n)], [sext(n)] (extend {e by} [n] bits), [restrict(lo,hi)].

    Variables ([x], [var1], [_tmp]) and constants may carry a positive width:
    [x<32>], [5<8>]. Quoted variables use OCaml string escapes, for example
    ["x!1"<32>]. Printed names and explicitly annotated literal widths are
    preserved. Concatenation preserves both operand widths. Other operand
    widths are reconciled by zero extension; an unsized literal may adopt
    the other operand's width when its value fits.

    This is a pure expression grammar, not a C parser. Logical [&&] and [||],
    memory loads, side effects, and C integer promotions are not supported. *)

val parse : ?default_size:int -> string -> Sexpr.Expr.t
(** [default_size] (default 64) is the positive width of unsized variables
    and constants. [Utils.pp] with its default [show_size=true] produces a
    round-trippable representation of pure expressions with ordinary
    name-based variable identity.
    @raise Failure ["Parse error: ..."] on invalid input. *)
