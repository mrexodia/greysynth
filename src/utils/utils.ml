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

open Sexpr.Expr

(* Import Bv module from Term for bitvector operations *)
module Bv = Term.Bv

(* Utility functions for MBA simplifier *)

type equiv_t = Yes | No | Unknown | Timeout | Disabled

let string_of_unop op =
  match op with
  | Sexpr.Expr.Not -> "~"
  | Sexpr.Expr.Minus -> "-"
  | Sexpr.Expr.Sext n -> Format.sprintf "sext(%d)" n
  | Sexpr.Expr.Uext n -> Format.sprintf "uext(%d)" n
  | Sexpr.Expr.Restrict { lo; hi } -> Format.sprintf "restrict(%d,%d)" lo hi

let string_of_binop op =
  match op with
  | Sexpr.Expr.Plus -> "+"
  | Sexpr.Expr.Minus -> "-"
  | Sexpr.Expr.Mul -> "*"
  | Sexpr.Expr.And -> "&"
  | Sexpr.Expr.Or -> "|"
  | Sexpr.Expr.Xor -> "^"
  | Sexpr.Expr.Lsl -> "<<"
  | Sexpr.Expr.Udiv -> "/"
  | Sexpr.Expr.Umod -> "%"
  | Sexpr.Expr.Sdiv -> "/s"
  | Sexpr.Expr.Smod -> "%s"
  | Sexpr.Expr.Concat -> "++"
  | Sexpr.Expr.Eq -> "=="
  | Sexpr.Expr.Diff -> "!="
  | Sexpr.Expr.Lsr -> ">>"
  | Sexpr.Expr.Asr -> ">>s"
  | Sexpr.Expr.Rol -> "rol"
  | Sexpr.Expr.Ror -> "ror"
  | Sexpr.Expr.Ule -> "<=u"
  | Sexpr.Expr.Ult -> "<u"
  | Sexpr.Expr.Sle -> "<=s"
  | Sexpr.Expr.Slt -> "<s"
  | Sexpr.Expr.Uge -> ">=u"
  | Sexpr.Expr.Ugt -> ">u"
  | Sexpr.Expr.Sge -> ">=s"
  | Sexpr.Expr.Sgt -> ">s"

let print_tabs n = print_string (String.make n '\t')
let heur = Xyntia_utils.Heuristic.kind_of_string "ils"

let xyntia_args : Xyntia.synthesis_args =
  {
    heuristic = heur;
    time = 1;
    dist = Xyntia_utils.Distance.LOGARITH;
    maxdepth = max_int;
    repeat = 1;
    formula = None;
    smt = None;
    smt_to = None;
    check = false;
    cegis = false;
    (* infrules = [Xyntia.Distance.Mul; Xyntia.Distance.MaskOTF; Xyntia.Distance.Xor; Xyntia.Distance.UShiftRight; Xyntia.Distance.ShiftLeft; Xyntia.Distance.Rotate; Xyntia.Distance.Affine; Xyntia.Distance.Poly2] *)
    infrules = [];
    noguidance = false;
    rules_combinator = "product";
  }

let increment_counter tbl key =
  let count = Option.value (Hashtbl.find_opt tbl key) ~default:0 in
  Hashtbl.replace tbl key (count + 1)

let pp ?(show_size = true) node =
  let memory_name_map : (Sexpr.Expr.t, string) Hashtbl.t = Hashtbl.create 8 in
  let counter = ref 0 in

  let get_memory_name addr_expr =
    if Hashtbl.mem memory_name_map addr_expr then
      Hashtbl.find memory_name_map addr_expr
    else
      let name = Format.sprintf "mem_%d" !counter in
      incr counter;
      Hashtbl.add memory_name_map addr_expr name;
      name
  in

  let rec aux node =
    let format_var name size =
      let initial c =
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || c = '_' || Char.code c > 127
      in
      let ordinary c = initial c || (c >= '0' && c <= '9') in
      let reserved = ["rol"; "ror"; "uext"; "sext"; "restrict"] in
      let printable =
        String.length name > 0 && initial name.[0]
        && String.for_all ordinary name && not (List.mem name reserved)
      in
      let encoded = if printable then name else Printf.sprintf "%S" name in
      if show_size then Format.sprintf "%s<%d>" encoded size else encoded
    in
    let format_const bv =
      let value = Bitvector.value_of bv in
      let size = Bitvector.size_of bv in
      let hex_str = Z.format "%x" value in
      let hex_digits = (size + 3) / 4 in
      let padded = String.make (max 0 (hex_digits - String.length hex_str)) '0' ^ hex_str in
      if show_size then Printf.sprintf "0x%s<%d>" padded size
      else "0x" ^ padded
    in
    match node with
    | Sexpr.Expr.Unary r ->
        Format.sprintf "(%s %s)" (string_of_unop r.f) (aux r.x)
    | Sexpr.Expr.Binary r ->
        Format.sprintf "(%s %s %s)" (aux r.x) (string_of_binop r.f) (aux r.y)
    | Sexpr.Expr.Var c -> format_var c.name c.size
    | Sexpr.Expr.Cst c -> format_const c
    | Sexpr.Expr.Ite r ->
        Format.sprintf "(%s ? %s : %s)" (aux r.c) (aux r.t) (aux r.e)
    (*
    | Sexpr.Expr.Load { addr; len; _ } ->
        format_var (get_memory_name addr) (len * 8)
    | _ -> failwith "Not supported (pp)"
    *)
    | Sexpr.Expr.Load { addr; _ } ->
        let _ = get_memory_name in
        Format.asprintf "[%a]" Term.pp addr
  in
  aux node

let rec pp_no_ext ?(show_size = true) node =
  let format_var name size =
    if show_size then Format.sprintf "%s<%d>" name size else name
  in
  (* This is used to always output 64 bits numbers *)
  let format_const c =
    let hex_str = Bitvector.to_hexstring c in
    (* Strip leading "0x" if present *)
    let hex_digits =
      if String.length hex_str >= 2 && String.sub hex_str 0 2 = "0x" then
        String.sub hex_str 2 (String.length hex_str - 2)
      else hex_str
    in
    let padded =
      String.make (max 0 (16 - String.length hex_digits)) '0' ^ hex_digits
    in
    "0x" ^ padded
  in
  match node with
  | Sexpr.Expr.Unary r -> (
      match r.f with
      | Sexpr.Expr.Restrict _ | Sexpr.Expr.Sext _ | Sexpr.Expr.Uext _ ->
          pp_no_ext ~show_size r.x
      | _ ->
          Format.sprintf "(%s %s)" (string_of_unop r.f)
            (pp_no_ext ~show_size r.x))
  | Sexpr.Expr.Binary r ->
      Format.sprintf "(%s %s %s)" (pp_no_ext ~show_size r.x)
        (string_of_binop r.f) (pp_no_ext ~show_size r.y)
  | Sexpr.Expr.Var c -> format_var c.name c.size
  | Sexpr.Expr.Cst c -> format_const c
  | Sexpr.Expr.Ite r ->
      Format.sprintf "(%s ? %s : %s)" (pp_no_ext ~show_size r.c)
        (pp_no_ext ~show_size r.t) (pp_no_ext ~show_size r.e)
  | _ -> "Unknown"

type cost_model = Legacy | PaperAst | Instruction | Readability

let cost_model = ref Legacy

let string_of_cost_model = function
  | Legacy -> "legacy"
  | PaperAst -> "paper_ast"
  | Instruction -> "instruction"
  | Readability -> "readability"

let cost_model_of_string = function
  | "legacy" -> Legacy
  | "paper_ast" -> PaperAst
  | "instruction" -> Instruction
  | "readability" -> Readability
  | value ->
      invalid_arg
        (Printf.sprintf
           "unknown cost model %S (expected legacy, paper_ast, instruction, or readability)"
           value)

let unary_cost model f =
  match model, f with
  | Legacy, (Sexpr.Expr.Restrict _ | Sexpr.Expr.Sext _ | Sexpr.Expr.Uext _) -> 0
  | Readability, (Sexpr.Expr.Restrict _ | Sexpr.Expr.Sext _ | Sexpr.Expr.Uext _) -> 2
  | _ -> 1

let binary_cost model f =
  match model, f with
  | Instruction, (Sexpr.Expr.Udiv | Sexpr.Expr.Sdiv | Sexpr.Expr.Umod | Sexpr.Expr.Smod) -> 8
  | Instruction, Sexpr.Expr.Mul -> 2
  | Readability, (Sexpr.Expr.Udiv | Sexpr.Expr.Sdiv | Sexpr.Expr.Umod | Sexpr.Expr.Smod
                 | Sexpr.Expr.Concat) -> 3
  | _ -> 1

let conditional_cost = function
  | Instruction -> 3
  | Readability -> 4
  | _ -> 1

let cost_of_expr model e =
  let memo = Sexpr.BvTbl.create 128 in
  let unary_cost f = unary_cost model f in
  let binary_cost f = binary_cost model f in
  let conditional_cost = conditional_cost model in
  let rec cost expression =
    match Sexpr.BvTbl.find_opt memo expression with
    | Some value -> value
    | None ->
        let value =
          match expression with
          | Sexpr.Expr.Unary r -> unary_cost r.f + cost r.x
          | Sexpr.Expr.Binary r -> binary_cost r.f + cost r.x + cost r.y
          | Sexpr.Expr.Ite r ->
              conditional_cost + cost r.c + cost r.t + cost r.e
          | Sexpr.Expr.Var _ | Sexpr.Expr.Load _ | Sexpr.Expr.Cst _ -> 1
        in
        Sexpr.BvTbl.add memo expression value;
        value
  in
  cost e


let size_of_expr e = cost_of_expr !cost_model e

let depth_of_expr expr =
  let memo = Sexpr.BvTbl.create 128 in
  let rec aux node =
    match Sexpr.BvTbl.find_opt memo node with
    | Some value -> value
    | None ->
        let value =
          match node with
          | Sexpr.Expr.Unary r -> 1 + aux r.x
          | Sexpr.Expr.Binary r -> 1 + max (aux r.x) (aux r.y)
          | Sexpr.Expr.Ite r -> 1 + max (aux r.c) (max (aux r.t) (aux r.e))
          | _ -> 0
        in
        Sexpr.BvTbl.add memo node value;
        value
  in
  aux expr

(** Check if two expressions are equivalent using SMT solver (Z3 or Bitwuzla).
    Returns (equiv_result, time, counter_example) where equiv_result is one of:
    - Yes: expressions are proven equivalent
    - No: expressions are proven different
    - Unknown: solver cannot determine equivalence
    - Timeout: solver timed out and time is the elapsed time in seconds.

    If show_counter_example is true and the result is No, counter_example will
    contain a Some mapping of variable names to their values that demonstrate
    non-equivalence. *)
exception Equivalence_timeout

let are_equivalent_seconds ?(show_counter_example = false) (expr1 : Sexpr.Expr.t)
    (expr2 : Sexpr.Expr.t) (timeout : float option) :
    equiv_t * float * (string * Z.t) list option =
  let started = Unix.gettimeofday () in
  let finish result model = (result, Unix.gettimeofday () -. started, model) in
  (* A missing optional solver must not crash simplification, nor count as a
     proof. Prefer Bitwuzla, retaining Z3 as a usable fallback. *)
  let factory =
    match Libsolver.bitwuzla_cxx with
    | Some _ as factory -> factory
    | None -> (
        match Libsolver.bitwuzla_c with
        | Some _ as factory -> factory
        | None -> Libsolver.z3)
  in
  if Sexpr.Expr.sizeof expr1 <> Sexpr.Expr.sizeof expr2 then finish No None
  else if Option.fold ~none:false
      ~some:(fun t -> t <= 0. || not (Float.is_finite t)) timeout then
    finish Timeout None
  else
    match factory with
    | None -> finish Unknown None
    | Some factory -> (
        try
          let module Factory = (val factory : Libsolver.F) in
          let module Solver = Factory () in
          Fun.protect
            ~finally:(fun () -> try Solver.close () with _ -> ())
            (fun () ->
              let solver_timeout = timeout in
              let var_cache : (string * int, Solver.Bv.t) Hashtbl.t =
                Hashtbl.create 16
              in
              let var_list = ref [] in
              let rec to_solver_bv (e : Sexpr.Expr.t) : Solver.Bv.t =
                match e with
                | Sexpr.Expr.Cst bv ->
                    Solver.Bv.value (Bitvector.size_of bv) (Bitvector.value_of bv)
                | Sexpr.Expr.Var v -> (
                    let key = (v.name, v.size) in
                    match Hashtbl.find_opt var_cache key with
                    | Some cached -> cached
                    | None ->
                        (* Solver C APIs may truncate embedded NULs in names.
                           Use fresh safe symbols; retain original names only
                           in the OCaml cache and counterexample mapping. *)
                        let symbol = Printf.sprintf "v%d" (Hashtbl.length var_cache) in
                        let fresh = Solver.Bv.const v.size symbol in
                        Hashtbl.add var_cache key fresh;
                        var_list := key :: !var_list;
                        fresh)
                | Sexpr.Expr.Unary { f; x; _ } -> (
                    let x' = to_solver_bv x in
                    match f with
                    | Sexpr.Expr.Not -> Solver.Bv.lognot x'
                    | Sexpr.Expr.Minus -> Solver.Bv.neg x'
                    | Sexpr.Expr.Uext n -> Solver.Bv.uext n x'
                    | Sexpr.Expr.Sext n -> Solver.Bv.sext n x'
                    | Sexpr.Expr.Restrict { lo; hi } ->
                        Solver.Bv.extract ~hi ~lo x')
                | Sexpr.Expr.Binary { f; x; y; _ } -> (
                    let x' = to_solver_bv x in
                    let y' = to_solver_bv y in
                    match f with
                    | Sexpr.Expr.Plus -> Solver.Bv.add x' y'
                    | Sexpr.Expr.Minus -> Solver.Bv.sub x' y'
                    | Sexpr.Expr.Mul -> Solver.Bv.mul x' y'
                    | Sexpr.Expr.Udiv -> Solver.Bv.udiv x' y'
                    | Sexpr.Expr.Sdiv -> Solver.Bv.sdiv x' y'
                    | Sexpr.Expr.Umod -> Solver.Bv.urem x' y'
                    (* Sexpr.Smod is the processor/C signed remainder, whose
                       sign follows the dividend, not SMT-LIB bvsmod. *)
                    | Sexpr.Expr.Smod -> Solver.Bv.srem x' y'
                    | Sexpr.Expr.And -> Solver.Bv.logand x' y'
                    | Sexpr.Expr.Or -> Solver.Bv.logor x' y'
                    | Sexpr.Expr.Xor -> Solver.Bv.logxor x' y'
                    | Sexpr.Expr.Lsl -> Solver.Bv.shift_left x' y'
                    | Sexpr.Expr.Lsr -> Solver.Bv.shift_right x' y'
                    | Sexpr.Expr.Asr -> Solver.Bv.shift_right_signed x' y'
                    | Sexpr.Expr.Ror -> Solver.Bv.rotate_right x' y'
                    | Sexpr.Expr.Rol -> Solver.Bv.rotate_left x' y'
                    | Sexpr.Expr.Concat -> Solver.Bv.append x' y'
                    | Sexpr.Expr.Eq -> Solver.Bl.to_bv (Solver.Bv.equal x' y')
                    | Sexpr.Expr.Diff -> Solver.Bl.to_bv (Solver.Bv.diff x' y')
                    | Sexpr.Expr.Ule -> Solver.Bl.to_bv (Solver.Bv.ule x' y')
                    | Sexpr.Expr.Ult -> Solver.Bl.to_bv (Solver.Bv.ult x' y')
                    | Sexpr.Expr.Uge -> Solver.Bl.to_bv (Solver.Bv.uge x' y')
                    | Sexpr.Expr.Ugt -> Solver.Bl.to_bv (Solver.Bv.ugt x' y')
                    | Sexpr.Expr.Sle -> Solver.Bl.to_bv (Solver.Bv.sle x' y')
                    | Sexpr.Expr.Slt -> Solver.Bl.to_bv (Solver.Bv.slt x' y')
                    | Sexpr.Expr.Sge -> Solver.Bl.to_bv (Solver.Bv.sge x' y')
                    | Sexpr.Expr.Sgt -> Solver.Bl.to_bv (Solver.Bv.sgt x' y'))
                | Sexpr.Expr.Ite { c; t; e; _ } ->
                    Solver.Bv.ite
                      (Solver.Bv.to_bl (to_solver_bv c))
                      (to_solver_bv t) (to_solver_bv e)
                | Sexpr.Expr.Load _ ->
                    failwith "Equivalence checking does not model memory loads"
              in
              let do_check () =
                let bv1 = to_solver_bv expr1 in
                let bv2 = to_solver_bv expr2 in
                Solver.assert_formula (Solver.Bv.diff bv1 bv2);
                match Solver.check_sat ?timeout:solver_timeout () with
                | Libsolver.Unsat -> finish Yes None
                | Libsolver.Unknown -> finish Unknown None
                | Libsolver.Sat ->
                    let model =
                      if show_counter_example then
                        Some
                          (List.map
                             (fun ((name, size) as key) ->
                               let label =
                                 if List.exists
                                      (fun (n, s) -> n = name && s <> size)
                                      !var_list
                                 then Printf.sprintf "%s<%d>" name size
                                 else name
                               in
                               (label,
                                Solver.get_bv_value
                                  (Hashtbl.find var_cache key)))
                             !var_list)
                      else None
                    in
                    finish No model
              in
              (* Keep native solver deadlines and a wall-clock backstop. Do
                 not replace an earlier caller alarm by a longer deadline. *)
              let wall_timeout =
                match timeout with
                | Some t when t > 0. -> max 1 (int_of_float (ceil t)) + 5
                | _ -> 120
              in
              let old_handler =
                Sys.signal Sys.sigalrm
                  (Sys.Signal_handle (fun _ -> raise Equivalence_timeout))
              in
              let previous_alarm = Unix.alarm wall_timeout in
              if previous_alarm > 0 && previous_alarm < wall_timeout then
                ignore (Unix.alarm previous_alarm);
              Fun.protect
                ~finally:(fun () ->
                  ignore (Unix.alarm 0);
                  Sys.set_signal Sys.sigalrm old_handler;
                  if previous_alarm > 0 then
                    let elapsed = int_of_float (Unix.gettimeofday () -. started) in
                    ignore (Unix.alarm (max 1 (previous_alarm - elapsed))))
                (fun () ->
                  try do_check () with
                  | Equivalence_timeout -> finish Timeout None
                  | _ -> finish Unknown None))
        with _ -> finish Unknown None)

(* Preserve the public integer-timeout API while allowing proof replay to
   share one fractional budget between abstraction and concrete fallback. *)
let are_equivalent ?show_counter_example expr1 expr2 timeout =
  are_equivalent_seconds ?show_counter_example expr1 expr2
    (Option.map float_of_int timeout)

let equiv_gt_then_obf expr gt obf timeout =
  let equiv_result, time_gt, _ = are_equivalent expr gt timeout in
  match equiv_result with
  | Yes -> (Yes, time_gt)
  | _ -> (
      let obf_equiv_result, time_obf, _ = are_equivalent expr obf timeout in
      match obf_equiv_result with
      | Yes -> (Yes, time_gt +. time_obf)
      | x -> (x, time_gt +. time_obf))

let equiv_to_str res = match res with Yes -> "yes" | No -> "no" | _ -> "ukn"

let rec binsec_simplify expr =
  let rec unary f x =
    match (f, x) with
    | _, Cst bv -> constant (Bv.unary f bv)
    (* identity *)
    | Not, Unary { f = Not; x; _ } -> x
    | Minus, Unary { f = Minus; x; _ } -> x
    | Minus, x when sizeof x = 1 -> x
    (* inversion *)
    | Minus, Binary { f = Minus; x; y; size; _ } -> binary Minus y x size
    | _, _ -> Sexpr.Expr.unary f x
  and binary f x y sx =
    let is_trivial_lognot x y =
      match (x, y) with
      | Unary { f = Not; x; _ }, y | y, Unary { f = Not; x; _ } ->
          compare x y = 0
      | _ -> false
    in
    match (f, x, y) with
    (* safety pattern guard *)
    (* TODO: move outside of the rec pattern if the rewriter is trusted *)
    (* | _, _, _ when f <> Concat && sizeof x <> sizeof y -> *)
    (*     abort @@ mk_binary f x y *)
    (* special boolean replacement *)
    | (Plus, _, _ | Minus, _, _) when sx = 1 -> binary Xor x y sx
    (* constant folding *)
    | _, Cst x, Cst y -> constant (Bv.binary f x y)
    | Plus, Binary { f = Plus; x = a; y = Cst b; _ }, Cst c ->
        binary Plus a (constant (Bv.binary Plus b c)) sx
    | Plus, Binary { f = Minus; x = a; y = Cst b; _ }, Cst c ->
        binary Minus a (constant (Bv.binary Minus b c)) sx
    | Minus, Binary { f = Plus; x = a; y = Cst b; _ }, Cst c ->
        binary Plus a (constant (Bv.binary Minus b c)) sx
    | Minus, Binary { f = Minus; x = a; y = Cst b; _ }, Cst c ->
        binary Minus a (constant (Bv.binary Plus b c)) sx
    | ((Plus | Minus) as f), Binary { f = Minus; x = Cst a; y = b; _ }, Cst c ->
        binary Minus (constant (Bv.binary f a c)) b sx
    | Plus, a, Cst bv when Bv.is_neg bv && not (Bv.is_min_sbv bv) ->
        binary Minus a (constant (Bv.neg bv)) sx
    | Minus, a, Cst bv when Bv.is_neg bv ->
        binary Plus a (constant (Bv.neg bv)) sx
    | Mul, Binary { f = Mul; x = a; y = Cst b; _ }, Cst c ->
        binary Mul a (constant (Bv.binary Mul b c)) sx
    | Or, Binary { f = Or; x = a; y = Cst b; _ }, Cst c ->
        binary Or a (constant (Bv.binary Or b c)) sx
    | And, Binary { f = And; x = a; y = Cst b; _ }, Cst c ->
        binary And a (constant (Bv.binary And b c)) sx
    | Xor, Binary { f = Xor; x = a; y = Cst b; _ }, Cst c ->
        binary Xor a (constant (Bv.binary Xor b c)) sx
    | Lsl, Binary { f = Lsl; x = a; y = Cst b; _ }, Cst c ->
        binary Lsl a (constant (Bv.binary Plus b c)) sx
    | Lsr, Binary { f = Lsr; x = a; y = Cst b; _ }, Cst c ->
        binary Lsr a (constant (Bv.binary Plus b c)) sx
    | Asr, Binary { f = Asr; x = a; y = Cst b; _ }, Cst c ->
        binary Asr a (constant (Bv.binary Plus b c)) sx
    | Rol, Binary { f = Rol; x = a; y = Cst b; _ }, Cst c ->
        binary Rol a (constant (Bv.binary Plus b c)) sx
    | Ror, Binary { f = Ror; x = a; y = Cst b; _ }, Cst c ->
        binary Ror a (constant (Bv.binary Plus b c)) sx
    (* identity *)
    | Plus, x, Cst bv
    | Minus, x, Cst bv
    | Lsl, x, Cst bv
    | Lsr, x, Cst bv
    | Asr, x, Cst bv
    | Rol, x, Cst bv
    | Ror, x, Cst bv
    | Xor, x, Cst bv
    | Or, x, Cst bv
      when Bv.is_zeros bv ->
        x
    | (Mul, x, Cst bv | Udiv, x, Cst bv | Sdiv, x, Cst bv) when Bv.is_ones bv ->
        x
    | And, x, Cst bv when Bv.is_fill bv -> x
    | (Rol, x, Cst bv | Ror, x, Cst bv) when sizeof x = Bv.to_uint bv -> x
    (* absorbing element *)
    | (Mul, _, Cst bv | And, _, Cst bv) when Bv.is_zeros bv -> y
    | Or, _, Cst bv when Bv.is_fill bv -> y
    | (Lsr | Lsl | Asr | Rol | Ror | Smod | Umod), Cst bv, _
      when Bv.is_zeros bv ->
        x
    | (Lsl, x, Cst bv | Lsr, x, Cst bv) when sizeof x <= Bv.to_uint bv ->
        zeros (Bv.size_of bv)
    (* elimination *)
    | (And, a, b | Or, a, b) when compare a b = 0 -> a
    | And, a, b when is_trivial_lognot a b -> zeros sx
    | Or, a, b when is_trivial_lognot a b -> constant (Bitvector.fill sx)
    | (And, Binary { f = And; y = a; _ }, b | Or, Binary { f = Or; y = a; _ }, b)
      when compare a b = 0 ->
        x
    | (Minus, a, b | Xor, a, b) when compare a b = 0 -> zeros (sizeof a)
    | Minus, Binary { f = Plus; x = a; y = b; _ }, c
    | Xor, Binary { f = Xor; x = a; y = b; _ }, c
      when compare b c = 0 ->
        a
    | (Smod | Umod), a, Cst bv when Bv.is_ones bv -> zeros (sizeof a)
    | (Smod | Umod), x, y when compare x y = 0 -> zeros (sizeof x)
    | (Lsl, x, Cst bv | Lsr, x, Cst bv) when Bv.to_uint bv >= sizeof x ->
        zeros (sizeof x)
    (* factorisation *)
    | Plus, a, b when compare a b = 0 -> binary Lsl a (constant (Bv.ones sx)) sx
    (* commutativity -- keep sorted *)
    (* special cases for + - *)
    | Plus, a, Binary { f = Minus; x = b; y = c; _ } when compare a b <= 0 ->
        binary Minus (binary Plus b a sx) c sx
    | Plus, Binary { f = Minus; x = a; y = b; _ }, c when compare b c <= 0 ->
        binary Minus (binary Plus a c sx) b sx
    | Plus, Binary { f = Minus; _ }, c -> Sexpr.Expr.binary Plus x c
    | Minus, Binary { f = Plus; x = a; y = b; _ }, c when compare b c < 0 ->
        binary Plus (binary Minus a c sx) b sx
    | Minus, Binary { f = Minus; x = a; y = b; _ }, c when compare b c < 0 ->
        binary Minus (binary Minus a c sx) b sx
    | Plus, Unary { f = Minus; x = a; _ }, b -> binary Minus b a sx
    (* generic chained *)
    | Plus, Binary { f = Plus; x = a; y = b; _ }, c
    | Mul, Binary { f = Mul; x = a; y = b; _ }, c
    | And, Binary { f = And; x = a; y = b; _ }, c
    | Or, Binary { f = Or; x = a; y = b; _ }, c
    | Xor, Binary { f = Xor; x = a; y = b; _ }, c
      when compare b c < 0 ->
        binary f (binary f a c sx) b sx
    | Plus, Binary { f = Plus; _ }, c
    | Mul, Binary { f = Mul; _ }, c
    | And, Binary { f = And; _ }, c
    | Or, Binary { f = Or; _ }, c
    | Xor, Binary { f = Xor; _ }, c ->
        Sexpr.Expr.binary f x c
    (* generic dual *)
    | Plus, _, _
    | Mul, _, _
    | And, _, _
    | Or, _, _
    | Xor, _, _
    | Eq, _, _
    | Diff, _, _
      when compare x y < 0 ->
        binary f y x sx
    (* associativity *)
    | Plus, a, Binary { f = Plus; x = b; y = c; _ }
    | Mul, a, Binary { f = Mul; x = b; y = c; _ }
    | And, a, Binary { f = And; x = b; y = c; _ }
    | Or, a, Binary { f = Or; x = b; y = c; _ }
    | Xor, a, Binary { f = Xor; x = b; y = c; _ } ->
        binary f (binary f a b sx) c sx
    (* TODO: possibly more to come *)
    (* inversion *)
    | Xor, a, Cst bv when Bv.is_fill bv -> unary Not a
    | Minus, a, Unary { f = Minus; x = b; _ } -> binary Plus a b sx
    | Minus, a, Binary { f = Plus; x = b; y = c; _ } ->
        binary Minus (binary Minus a b sx) c sx
    | Minus, a, Binary { f = Minus; x = b; y = c; _ } ->
        binary Plus (binary Minus a b sx) c sx
    (* basic arithmetic *)
    | Minus, Binary { f = Lsl; x; y = Cst bv; size; _ }, y when is_equal x y ->
        let one = Bv.ones size in
        binary Mul x (constant (Bv.sub (Bv.binary Lsl one bv) one)) size
    | Mul, x, Cst bv ->
        let z = Bv.value_of bv in
        if Z.popcount z = 1 then
          binary Lsl x (constant (Bv.of_int ~size:sx (Z.trailing_zeros z))) sx
        else Sexpr.Expr.binary Mul x y
    (* default case *)
    | _, _, _ -> Sexpr.Expr.binary f x y
  in

  match expr with
  | Unary r -> unary r.f (binsec_simplify r.x)
  | Binary r -> binary r.f (binsec_simplify r.x) (binsec_simplify r.y) r.size
  | _ -> expr
