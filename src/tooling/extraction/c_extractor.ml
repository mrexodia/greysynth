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

(* c_extractor.ml - Extract arithmetic/boolean expressions from C files
 *
 * Parses C files with CIL and extracts all expressions containing only
 * allowed operators: +, -, *, /, &, <<, >>, |, ^
 *
 * Unsupported constructs (field accessors, pointers, etc.) are abstracted
 * as fresh variables.
 *)

open GoblintCil

(* Counter for generating fresh variable names *)
let fresh_counter = ref 0

let fresh_var prefix size =
  incr fresh_counter;
  let name = Printf.sprintf "%s_%d" prefix !fresh_counter in
  Sexpr.Expr.var name size name

(* Table of constant variable values (name -> (value, size)) *)
let const_table : (string, Z.t * int) Hashtbl.t = Hashtbl.create 64

(* Table of variable signedness (name -> is_signed), populated during convert *)
let var_signs : (string, bool) Hashtbl.t = Hashtbl.create 64

(* Configurable pointer size (in bits). Default: 64 for x86-64 *)
let pointer_size = ref 64

(* Enable/disable constant inlining. Default: false (disabled) *)
let inline_constants = ref false

(* Get the bit size of a CIL integer kind *)
let bitsize_of_ikind (ik : Cil.ikind) : int =
  match ik with
  | IChar | ISChar | IUChar -> 8
  | IShort | IUShort -> 16
  | IInt | IUInt -> 32
  | ILong | IULong -> 64
  | ILongLong | IULongLong -> 64
  | IBool -> 1
  | IInt128 | IUInt128 -> 128

let bitsize_of_type (typ : Cil.typ) : int =
  match Cil.unrollType typ with
  | TInt (ik, _) -> bitsize_of_ikind ik
  | TPtr _ -> !pointer_size
  | TArray _ -> !pointer_size
  | TComp _ -> !pointer_size (* struct/union - abstract as pointer-sized *)
  | TEnum _ -> 32
  | _ -> !pointer_size

let is_signed_ikind (ik : Cil.ikind) : bool =
  match ik with
  | IChar | ISChar | IShort | IInt | ILong | ILongLong | IInt128 -> true
  | IUChar | IUShort | IUInt | IULong | IULongLong | IUInt128 | IBool -> false

let is_signed_type (typ : Cil.typ) : bool =
  match Cil.unrollType typ with
  | TInt (ik, _) -> is_signed_ikind ik
  | _ -> false

(* Create a constant bitvector of a specific size, masking the value to fit *)
let make_constant (value : Z.t) (size : int) : Sexpr.Expr.t =
  let mask = Z.sub (Z.shift_left Z.one size) Z.one in
  let masked = Z.logand value mask in
  let bv = Bitvector.create masked size in
  Sexpr.Expr.constant bv

(* Constant folding for binary operations *)
let fold_binary op (e1 : Sexpr.Expr.t) (e2 : Sexpr.Expr.t) : Sexpr.Expr.t =
  match (e1, e2) with
  | Sexpr.Expr.Cst bv1, Sexpr.Expr.Cst bv2 ->
      let v1 = Bitvector.value_of bv1 in
      let v2 = Bitvector.value_of bv2 in
      let size = Bitvector.size_of bv1 in
      let result =
        match op with
        | Sexpr.Expr.Plus -> Z.add v1 v2
        | Sexpr.Expr.Minus -> Z.sub v1 v2
        | Sexpr.Expr.Mul -> Z.mul v1 v2
        | Sexpr.Expr.Udiv -> if Z.equal v2 Z.zero then v1 else Z.div v1 v2
        | Sexpr.Expr.Sdiv -> if Z.equal v2 Z.zero then v1 else Z.div v1 v2
        | Sexpr.Expr.Umod -> if Z.equal v2 Z.zero then v1 else Z.rem v1 v2
        | Sexpr.Expr.Smod -> if Z.equal v2 Z.zero then v1 else Z.rem v1 v2
        | Sexpr.Expr.And -> Z.logand v1 v2
        | Sexpr.Expr.Or -> Z.logor v1 v2
        | Sexpr.Expr.Xor -> Z.logxor v1 v2
        | Sexpr.Expr.Lsl ->
            if Z.geq v2 (Z.of_int size) then Z.zero
            else Z.shift_left v1 (Z.to_int v2)
        | Sexpr.Expr.Lsr ->
            if Z.geq v2 (Z.of_int size) then Z.zero
            else Z.shift_right v1 (Z.to_int v2)
        | Sexpr.Expr.Asr ->
            (* Arithmetic shift right - need to handle sign bit *)
            if Z.geq v2 (Z.of_int size) then
              (* Fill with sign bit *)
              if Z.testbit v1 (size - 1) then
                Z.sub (Z.shift_left Z.one size) Z.one (* all 1s *)
              else Z.zero
            else
              let shift = Z.to_int v2 in
              let sign_bit = Z.testbit v1 (size - 1) in
              let shifted = Z.shift_right v1 shift in
              if sign_bit then
                (* Fill upper bits with 1s *)
                let fill_mask =
                  Z.shift_left
                    (Z.sub (Z.shift_left Z.one shift) Z.one)
                    (size - shift)
                in
                Z.logor shifted fill_mask
              else shifted
        | _ -> Z.add v1 v2 (* fallback for other operations *)
      in
      make_constant result size
  | _ -> Sexpr.Expr.binary op e1 e2

(* Constant folding for unary operations *)
let fold_unary op (e : Sexpr.Expr.t) : Sexpr.Expr.t =
  match e with
  | Sexpr.Expr.Cst bv ->
      let v = Bitvector.value_of bv in
      let size = Bitvector.size_of bv in
      let result =
        match op with
        | Sexpr.Expr.Minus -> Z.neg v
        | Sexpr.Expr.Not -> Z.lognot v
        | _ -> v (* extensions/restrictions handled in adjust_size *)
      in
      make_constant result size
  | _ -> Sexpr.Expr.unary op e

(* Adjust expression size for explicit casts, with constant propagation *)
let adjust_size ~is_signed (e : Sexpr.Expr.t) (target_size : int) : Sexpr.Expr.t
    =
  let current_size = Sexpr.Expr.sizeof e in
  if current_size = target_size then e
  else
    match e with
    | Sexpr.Expr.Cst bv ->
        (* Constant propagation: compute the result directly *)
        let value = Bitvector.value_of bv in
        if current_size > target_size then
          (* Restrict: just mask to target_size bits *)
          make_constant value target_size
        else if is_signed then
          (* Sign extension: check sign bit and extend *)
          let sign_bit = Z.testbit value (current_size - 1) in
          if sign_bit then
            (* Negative: fill upper bits with 1s *)
            let mask = Z.sub (Z.shift_left Z.one current_size) Z.one in
            let upper =
              Z.shift_left
                (Z.sub (Z.shift_left Z.one (target_size - current_size)) Z.one)
                current_size
            in
            make_constant (Z.logor upper (Z.logand value mask)) target_size
          else
            (* Positive: just zero extend *)
            make_constant value target_size
        else
          (* Zero extension: value stays the same, just bigger size *)
          make_constant value target_size
    | _ ->
        (* Non-constant: use extension operators *)
        if current_size > target_size then
          Sexpr.Expr.unary
            (Sexpr.Expr.Restrict { lo = 0; hi = target_size - 1 })
            e
        else
          let ext_amount = target_size - current_size in
          if is_signed then Sexpr.Expr.unary (Sexpr.Expr.Sext ext_amount) e
          else Sexpr.Expr.unary (Sexpr.Expr.Uext ext_amount) e

(* Equalize sizes of two Sexpr expressions by extending the smaller one *)
let equalize_sizes ~is_signed (e1 : Sexpr.Expr.t) (e2 : Sexpr.Expr.t) :
    Sexpr.Expr.t * Sexpr.Expr.t =
  let size1 = Sexpr.Expr.sizeof e1 in
  let size2 = Sexpr.Expr.sizeof e2 in
  if size1 = size2 then (e1, e2)
  else if size1 < size2 then (adjust_size ~is_signed e1 size2, e2)
  else (e1, adjust_size ~is_signed e2 size1)

(* Generate a name for an lval (for abstraction) *)
let rec name_of_lval (lv : Cil.lval) : string =
  match lv with
  | Var vi, NoOffset -> vi.vname
  | Var vi, off -> vi.vname ^ "_" ^ name_of_offset off
  | Mem e, off -> "mem_" ^ name_of_exp e ^ "_" ^ name_of_offset off

and name_of_offset (off : Cil.offset) : string =
  match off with
  | NoOffset -> ""
  | Field (fi, off') ->
      let rest = name_of_offset off' in
      if rest = "" then fi.fname else fi.fname ^ "_" ^ rest
  | Index (_, off') ->
      let rest = name_of_offset off' in
      if rest = "" then "idx" else "idx_" ^ rest

and name_of_exp (e : Cil.exp) : string =
  match e with
  | Const _ -> "cst"
  | Lval lv -> name_of_lval lv
  | UnOp (_, e', _) -> "u_" ^ name_of_exp e'
  | BinOp (_, e1, e2, _) -> name_of_exp e1 ^ "_" ^ name_of_exp e2
  | CastE (_, e') -> name_of_exp e'
  | _ -> "expr"

(* Check if a binary operator is allowed *)
let is_allowed_binop (b : Cil.binop) : bool =
  match b with
  | PlusA | PlusPI | IndexPI -> true (* + *)
  | MinusA | MinusPI | MinusPP -> true (* - *)
  | Mult -> true (* * *)
  | Div -> true (* / *)
  | Shiftlt -> true (* << *)
  | Shiftrt -> true (* >> *)
  | BAnd -> true (* & *)
  | BOr -> true (* | *)
  | BXor -> true (* ^ *)
  | _ -> false

(* Check if a unary operator is allowed *)
let is_allowed_unop (u : Cil.unop) : bool =
  match u with
  | Neg -> true (* unary - *)
  | BNot -> true (* ~ *)
  | LNot -> false (* ! - logical not, not bitwise *)

(* Result type for conversion *)
type conv_result =
  | Ok of Sexpr.Expr.t
  | Abstracted of Sexpr.Expr.t (* Expression was abstracted to a variable *)
  | Unsupported (* Expression cannot be converted *)

(* Convert CIL expression to Sexpr.Expr.t, abstracting unsupported constructs *)
let rec convert (cexpr : Cil.exp) : conv_result =
  match cexpr with
  | Const (CInt (i, ik, _)) ->
      let size = bitsize_of_ikind ik in
      Ok (make_constant i size)
  | Const (CReal _) -> Unsupported (* floats not supported *)
  | Const (CStr _ | CWStr _) -> Unsupported (* strings not supported *)
  | Const (CChr c) -> Ok (make_constant (Z.of_int (Char.code c)) 8)
  | Const (CEnum _) -> Unsupported
  | Lval (Var vi, NoOffset) -> (
      (* Simple variable - check if it's a known constant *)
      match (!inline_constants, Hashtbl.find_opt const_table vi.vname) with
      | true, Some (value, size) ->
          (* Inline the constant value *)
          Ok (make_constant value size)
      | _ ->
          (* Regular variable: record its signedness *)
          let size = bitsize_of_type vi.vtype in
          Hashtbl.replace var_signs vi.vname (is_signed_type vi.vtype);
          Ok (Sexpr.Expr.var vi.vname size vi.vname))
  | Lval lv ->
      (* Field access, array access, pointer deref - abstract as variable *)
      let name = name_of_lval lv in
      let size = bitsize_of_type (Cil.typeOfLval lv) in
      Abstracted (Sexpr.Expr.var name size name)
  | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
      (* sizeof/alignof - treat as constants, abstract *)
      Abstracted (fresh_var "sizeof" 64)
  | UnOp (u, e, res_typ) -> (
      if not (is_allowed_unop u) then Unsupported
      else
        match convert e with
        | Unsupported -> Unsupported
        | Ok inner | Abstracted inner ->
            let sexpr_op =
              match u with
              | Neg -> Sexpr.Expr.Minus
              | BNot -> Sexpr.Expr.Not
              | LNot -> Sexpr.Expr.Not (* shouldn't reach here *)
            in
            let result = fold_unary sexpr_op inner in
            (* Adjust size if needed *)
            let target_size = bitsize_of_type res_typ in
            let is_signed =
              match Cil.unrollType res_typ with
              | TInt (ik, _) -> is_signed_ikind ik
              | _ -> false
            in
            Ok (adjust_size ~is_signed result target_size))
  | BinOp (b, e1, e2, res_typ) -> (
      if not (is_allowed_binop b) then Unsupported
      else
        match (convert e1, convert e2) with
        | Unsupported, _ | _, Unsupported -> Unsupported
        | (Ok se1 | Abstracted se1), (Ok se2 | Abstracted se2) ->
            let is_result_signed =
              match Cil.unrollType res_typ with
              | TInt (ik, _) -> is_signed_ikind ik
              | _ -> false
            in
            let se1', se2' =
              equalize_sizes ~is_signed:is_result_signed se1 se2
            in
            let sexpr_op =
              match b with
              | PlusA | PlusPI | IndexPI -> Sexpr.Expr.Plus
              | MinusA | MinusPI | MinusPP -> Sexpr.Expr.Minus
              | Mult -> Sexpr.Expr.Mul
              | Div ->
                  if is_result_signed then Sexpr.Expr.Sdiv else Sexpr.Expr.Udiv
              | Shiftlt -> Sexpr.Expr.Lsl
              | Shiftrt ->
                  if is_result_signed then Sexpr.Expr.Asr else Sexpr.Expr.Lsr
              | BAnd -> Sexpr.Expr.And
              | BOr -> Sexpr.Expr.Or
              | BXor -> Sexpr.Expr.Xor
              | _ -> failwith "Unreachable: operator already checked"
            in
            Ok (fold_binary sexpr_op se1' se2'))
  | CastE (target_typ, e) -> (
      match convert e with
      | Unsupported -> Unsupported
      | Ok inner | Abstracted inner ->
          let target_size = bitsize_of_type target_typ in
          let is_signed =
            match Cil.unrollType target_typ with
            | TInt (ik, _) -> is_signed_ikind ik
            | _ -> false
          in
          Ok (adjust_size ~is_signed inner target_size))
  | AddrOf _ | StartOf _ ->
      (* Address-of operations - abstract as variable *)
      Abstracted (fresh_var "addr" !pointer_size)
  | Question (_, e1, e2, _) -> (
      (* Ternary operator - try to convert both branches *)
      match (convert e1, convert e2) with
      | Unsupported, _ | _, Unsupported -> Unsupported
      | (Ok _ | Abstracted _), (Ok _ | Abstracted _) ->
          (* We can't properly represent ternary, abstract it *)
          let size =
            match convert e1 with
            | Ok e | Abstracted e -> Sexpr.Expr.sizeof e
            | Unsupported -> 64
          in
          Abstracted (fresh_var "ite" size))
  | Real _ | Imag _ -> Unsupported (* complex numbers *)
  | AddrOfLabel _ -> Unsupported (* GCC extension for computed goto *)

(* Check if an expression contains at least one arithmetic/bitwise operation *)
let rec has_operation (e : Cil.exp) : bool =
  match e with
  | UnOp (u, _, _) -> is_allowed_unop u
  | BinOp (b, e1, e2, _) ->
      is_allowed_binop b || has_operation e1 || has_operation e2
  | CastE (_, e') -> has_operation e'
  | _ -> false

(* Minimum expression depth to extract (filter trivial expressions) *)
let min_depth = ref 1

(* Compute depth of a Sexpr (after constant folding) *)
let rec sexpr_depth (e : Sexpr.Expr.t) : int =
  match e with
  | Sexpr.Expr.Var _ | Sexpr.Expr.Cst _ | Sexpr.Expr.Load _ -> 0
  | Sexpr.Expr.Unary { x; _ } -> 1 + sexpr_depth x
  | Sexpr.Expr.Binary { x; y; _ } -> 1 + max (sexpr_depth x) (sexpr_depth y)
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      1 + max (sexpr_depth c) (max (sexpr_depth t) (sexpr_depth e))

(* Use shared MBA classifier *)
type mba_class = Mba_classifier.mba_class

(* Re-export classifier functions *)
let classify_expr = Mba_classifier.classify
let class_to_string = Mba_classifier.to_string
let class_to_colored_string = Mba_classifier.to_colored_string

(* Filter configuration *)
let exclude_bitwise = ref false
let exclude_linear = ref false
let exclude_polynomial = ref false
let exclude_non_polynomial = ref false
let exclude_non_mba = ref false

(* Check if expression should be excluded based on classification *)
let should_exclude (class_type : mba_class) : bool =
  match class_type with
  | Mba_classifier.Bitwise -> !exclude_bitwise
  | Mba_classifier.Bitwise_const -> !exclude_bitwise
  | Mba_classifier.Linear -> !exclude_linear
  | Mba_classifier.Linear_const -> !exclude_linear
  | Mba_classifier.Polynomial -> !exclude_polynomial
  | Mba_classifier.Polynomial_const -> !exclude_polynomial
  | Mba_classifier.Non_polynomial -> !exclude_non_polynomial
  | Mba_classifier.Non_mba -> !exclude_non_mba

(* GAMBA-friendly transformations *)
let gamba_friendly_mode = ref false

(* Rename variables to x0, x1, x2, ... *)
let rename_variables = ref false

(* Check if expression is GAMBA-compatible *)
let rec is_gamba_compatible (e : Sexpr.Expr.t) : bool =
  match e with
  | Sexpr.Expr.Var _ | Sexpr.Expr.Cst _ -> true
  | Sexpr.Expr.Unary { f; x; _ } -> (
      match f with
      | Sexpr.Expr.Sext _ | Sexpr.Expr.Uext _ | Sexpr.Expr.Restrict _ ->
          false (* Extensions and restrictions not allowed *)
      | _ -> is_gamba_compatible x)
  | Sexpr.Expr.Binary { f; x; y; _ } -> (
      match f with
      | Sexpr.Expr.Udiv | Sexpr.Expr.Sdiv | Sexpr.Expr.Umod | Sexpr.Expr.Smod ->
          false (* Division and modulo not allowed *)
      | Sexpr.Expr.Lsr | Sexpr.Expr.Asr -> false (* Right shifts not allowed *)
      | _ -> is_gamba_compatible x && is_gamba_compatible y)
  | Sexpr.Expr.Load _ -> true
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      is_gamba_compatible c && is_gamba_compatible t && is_gamba_compatible e

(* Propagate size through expressions by removing extensions/restrictions *)
let rec propagate_size (target_size : int) (e : Sexpr.Expr.t) : Sexpr.Expr.t =
  match e with
  | Sexpr.Expr.Var v ->
      if v.size = target_size then e
      else Sexpr.Expr.var v.name target_size v.label
  | Sexpr.Expr.Cst bv ->
      let value = Bitvector.value_of bv in
      let current_size = Bitvector.size_of bv in
      if current_size = target_size then e
      else
        (* Extend or truncate the constant *)
        let mask = Z.sub (Z.shift_left Z.one target_size) Z.one in
        let masked = Z.logand value mask in
        Sexpr.Expr.constant (Bitvector.create masked target_size)
  | Sexpr.Expr.Unary { f; x; _ } -> (
      match f with
      | Sexpr.Expr.Sext _ | Sexpr.Expr.Uext _ | Sexpr.Expr.Restrict _ ->
          (* Remove the extension/restriction and propagate size *)
          propagate_size target_size x
      | Sexpr.Expr.Minus ->
          Sexpr.Expr.unary Sexpr.Expr.Minus (propagate_size target_size x)
      | Sexpr.Expr.Not ->
          Sexpr.Expr.unary Sexpr.Expr.Not (propagate_size target_size x))
  | Sexpr.Expr.Binary { f; x; y; _ } ->
      let x' = propagate_size target_size x in
      let y' = propagate_size target_size y in
      Sexpr.Expr.binary f x' y'
  | Sexpr.Expr.Load _ -> e
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      let c' = propagate_size target_size c in
      let t' = propagate_size target_size t in
      let e' = propagate_size target_size e in
      Sexpr.Expr.ite c' t' e'

(* Make expression GAMBA-friendly *)
let make_gamba_friendly (e : Sexpr.Expr.t) : Sexpr.Expr.t option =
  if is_gamba_compatible e then Some e
  else
    (* Try to transform by propagating the target size *)
    let target_size = Sexpr.Expr.sizeof e in
    let e' = propagate_size target_size e in
    if is_gamba_compatible e' then Some e'
    else None (* Cannot be made GAMBA-friendly *)

(* Eliminate round-trip casts: uext(N, restrict(0, M, expr)) -> expr & mask
   when sizeof(expr) = M + 1 + N, i.e. the restrict+uext returns to the
   original size. This is a pure algebraic identity:
     uext(N, restrict(0,M, e))  ≡  e & ((1 << (M+1)) - 1)
   Applied recursively bottom-up. *)
let rec eliminate_roundtrip_casts (e : Sexpr.Expr.t) : Sexpr.Expr.t =
  match e with
  | Sexpr.Expr.Unary { f = Sexpr.Expr.Uext n;
                        x = Sexpr.Expr.Unary { f = Sexpr.Expr.Restrict { lo = 0; hi };
                                                x = inner; _ }; _ } ->
      let inner = eliminate_roundtrip_casts inner in
      let restrict_size = hi + 1 in
      let original_size = Sexpr.Expr.sizeof inner in
      if restrict_size + n = original_size then
        (* Round-trip: rewrite to inner & mask *)
        let mask_val = Z.sub (Z.shift_left Z.one restrict_size) Z.one in
        let mask = Sexpr.Expr.constant (Bitvector.create mask_val original_size) in
        Sexpr.Expr.binary Sexpr.Expr.And inner mask
      else
        (* Not a round-trip, keep but recurse into inner *)
        Sexpr.Expr.unary (Sexpr.Expr.Uext n)
          (Sexpr.Expr.unary (Sexpr.Expr.Restrict { lo = 0; hi }) inner)
  | Sexpr.Expr.Unary { f; x; _ } ->
      Sexpr.Expr.unary f (eliminate_roundtrip_casts x)
  | Sexpr.Expr.Binary { f; x; y; _ } ->
      Sexpr.Expr.binary f (eliminate_roundtrip_casts x) (eliminate_roundtrip_casts y)
  | Sexpr.Expr.Ite { c; t; e = else_e; _ } ->
      Sexpr.Expr.ite
        (eliminate_roundtrip_casts c)
        (eliminate_roundtrip_casts t)
        (eliminate_roundtrip_casts else_e)
  | Sexpr.Expr.Var _ | Sexpr.Expr.Cst _ | Sexpr.Expr.Load _ -> e

(* Collected expressions: (expr, location, output_is_signed) *)
let collected_exprs : (Sexpr.Expr.t * Cil.location * bool) list ref = ref []

(* Debug flag for const collection *)
let debug_const = ref false

(* Visitor to collect constant variable initializers *)
class const_collector =
  object
    inherit nopCilVisitor

    method! vglob (g : Cil.global) =
      match g with
      | GVar (vi, init, _) ->
          if !debug_const then
            Format.eprintf "GVar: %s, init=%s@." vi.vname
              (match init.init with Some _ -> "Some" | None -> "None");
          (* Inline any global variable with a constant integer initializer *)
          (* Helper to extract CInt from possibly cast expression *)
          let rec extract_cint e =
            match e with
            | Const (CInt (value, ik, _)) -> Some (value, ik)
            | CastE (_, e') -> extract_cint e'
            | _ -> None
          in
          (match init.init with
          | Some (SingleInit e) when Option.is_some (extract_cint e) ->
              let value, ik = Option.get (extract_cint e) in
              if !debug_const then
                Format.eprintf "  -> CInt, value=%s, size=%d@."
                  (Z.to_string value) (bitsize_of_ikind ik);
              (* Use type's size if available, otherwise use ikind's size *)
              let size =
                match Cil.unrollType vi.vtype with
                | TInt (tik, _) -> bitsize_of_ikind tik
                | _ -> bitsize_of_ikind ik
              in
              Hashtbl.replace const_table vi.vname (value, size)
          | Some (SingleInit (Const c)) ->
              if !debug_const then
                Format.eprintf "  -> Const (other): %s@."
                  (match c with
                  | CInt _ -> "CInt"
                  | CReal _ -> "CReal"
                  | CChr _ -> "CChr"
                  | CStr _ -> "CStr"
                  | CWStr _ -> "CWStr"
                  | CEnum _ -> "CEnum")
          | Some (SingleInit e) ->
              if !debug_const then
                Format.eprintf "  -> SingleInit: %s@."
                  (match e with
                  | Const _ -> "Const"
                  | Lval _ -> "Lval"
                  | SizeOf _ -> "SizeOf"
                  | SizeOfE _ -> "SizeOfE"
                  | SizeOfStr _ -> "SizeOfStr"
                  | AlignOf _ -> "AlignOf"
                  | AlignOfE _ -> "AlignOfE"
                  | UnOp _ -> "UnOp"
                  | BinOp _ -> "BinOp"
                  | Question _ -> "Question"
                  | CastE _ -> "CastE"
                  | AddrOf _ -> "AddrOf"
                  | AddrOfLabel _ -> "AddrOfLabel"
                  | StartOf _ -> "StartOf"
                  | Real _ -> "Real"
                  | Imag _ -> "Imag")
          | Some (CompoundInit _) ->
              if !debug_const then Format.eprintf "  -> CompoundInit@."
          | None -> ());
          DoChildren
      | GVarDecl _ -> DoChildren
      | _ -> DoChildren
  end

(* Visitor to collect outermost expressions only *)
class expr_collector =
  object
    inherit nopCilVisitor

    method! vexpr (e : Cil.exp) =
      if has_operation e then
        match convert e with
        | Ok sexpr | Abstracted sexpr ->
            let sexpr = eliminate_roundtrip_casts sexpr in
            (* Check depth AFTER constant folding *)
            if sexpr_depth sexpr >= !min_depth then (
              let loc = !currentLoc in
              let output_signed = is_signed_type (Cil.typeOf e) in
              collected_exprs := (sexpr, loc, output_signed) :: !collected_exprs;
              (* SkipChildren: don't collect subexpressions of this expression *)
              SkipChildren)
            else DoChildren
        | Unsupported -> DoChildren
      else DoChildren
  end

(* CIL initialization state *)
let cil_initialized = ref false

(* Preprocessor settings *)
let cpp_command = ref "gcc"
let cpp_args : string list ref = ref []

(* Common macOS/Clang compatibility defines - quoted for shell *)
let macos_compat_defines =
  [
    "-D_Nullable=";
    "-D_Nonnull=";
    "-D__nullable=";
    "-D__nonnull=";
    "-D__null_unspecified=";
    "-D_Null_unspecified=";
    "-D__block=";
    "-D__dead2=";
    "-D__pure2=";
    "-D__cold=";
    "-D__used=";
    "-D__unavailable=";
    "-U__BLOCKS__";
    (* Disable blocks support *)
    "'-D__printflike(a,b)='";
    "'-D__scanflike(a,b)='";
    "'-D__DARWIN_ALIAS(x)='";
    "'-D__DARWIN_ALIAS_C(x)='";
    "'-D__DARWIN_ALIAS_I(x)='";
    "'-D__DARWIN_INODE64(x)='";
    "'-D__OSX_AVAILABLE_STARTING(x,y)='";
    "'-D__OSX_AVAILABLE_BUT_DEPRECATED(a,b,c,d)='";
    "'-D__OSX_AVAILABLE(x)='";
    "'-D__IOS_AVAILABLE(x)='";
    "'-D__WATCHOS_AVAILABLE(x)='";
    "'-D__TVOS_AVAILABLE(x)='";
    "-DAvailability";
    "'-D__has_feature(x)=0'";
    "'-D__has_extension(x)=0'";
    "'-D__has_attribute(x)=0'";
    "'-D__has_builtin(x)=0'";
    "'-D__attribute__(x)='";
    "'-D__DARWIN_1050(x)='";
    "'-D__OSX_AVAILABLE_BUT_DEPRECATED_MSG(a,b,c,d,e)='";
    "-D__WATCHOS_PROHIBITED=";
    "-D__TVOS_PROHIBITED=";
    "-D__API_AVAILABLE(...)=";
    "-D__API_UNAVAILABLE(...)=";
    "-D__API_DEPRECATED(...)=";
    "-D__API_DEPRECATED_WITH_REPLACEMENT(...)=";
    "-D__swift_unavailable(...)=";
    "-D__AVAILABILITY_INTERNAL_DEPRECATED=";
    "-D__AVAILABILITY_INTERNAL_UNAVAILABLE=";
    "-D__AVAILABILITY_INTERNAL_WEAK_IMPORT=";
  ]

(* Preprocess a C file and return the path to the preprocessed file *)
let preprocess_file (file : string) : string =
  let temp_file = Filename.temp_file "c_extractor_" ".i" in
  let args = String.concat " " !cpp_args in
  let cmd =
    Printf.sprintf "%s -E %s %s -o %s 2>&1" !cpp_command args file temp_file
  in
  let ic = Unix.open_process_in cmd in
  let output = Buffer.create 256 in
  (try
     while true do
       Buffer.add_channel output ic 1
     done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 0 -> temp_file
  | _ ->
      (try Sys.remove temp_file with _ -> ());
      failwith
        (Printf.sprintf "Preprocessing failed:\n%s" (Buffer.contents output))

(* Extract expressions from a C file *)
let extract_from_file ?(preprocess = false) (file : string) :
    (Sexpr.Expr.t * Cil.location * bool) list =
  if not !cil_initialized then (
    Cil.initCIL ();
    cil_initialized := true);
  if not (Sys.file_exists file) then
    failwith (Printf.sprintf "File %s does not exist" file);

  collected_exprs := [];
  fresh_counter := 0;

  let file_to_parse, cleanup =
    if preprocess then
      let pp_file = preprocess_file file in
      (pp_file, fun () -> try Sys.remove pp_file with _ -> ())
    else (file, fun () -> ())
  in

  let result =
    try
      let cil_file = Frontc.parse file_to_parse () in
      (* First pass: collect constant variable values *)
      Hashtbl.clear const_table;
      let const_visitor = new const_collector in
      ignore (visitCilFile const_visitor cil_file);
      (* Second pass: collect expressions with constants inlined *)
      let expr_visitor = new expr_collector in
      ignore (visitCilFile expr_visitor cil_file);
      List.rev !collected_exprs
    with e ->
      cleanup ();
      raise e
  in
  cleanup ();
  result

(* Deduplicate expressions by their string representation *)
let deduplicate (exprs : (Sexpr.Expr.t * Cil.location * bool) list) :
    (Sexpr.Expr.t * Cil.location * bool) list =
  let seen = Hashtbl.create 256 in
  List.filter
    (fun (e, _, _) ->
      let key = Greysynth_utils.Utils.pp e in
      if Hashtbl.mem seen key then false
      else (
        Hashtbl.add seen key ();
        true))
    exprs

(* Extract all variables from a Sexpr.Expr.t *)
let rec extract_vars (e : Sexpr.Expr.t) : (string * int) list =
  match e with
  | Sexpr.Expr.Var v -> [ (v.name, v.size) ]
  | Sexpr.Expr.Cst _ -> []
  | Sexpr.Expr.Unary { x; _ } -> extract_vars x
  | Sexpr.Expr.Binary { x; y; _ } -> extract_vars x @ extract_vars y
  | Sexpr.Expr.Load _ -> [] (* Memory loads abstracted away *)
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      extract_vars c @ extract_vars t @ extract_vars e

(* Deduplicate and sort variables *)
let unique_vars (vars : (string * int) list) : (string * int) list =
  let seen = Hashtbl.create 16 in
  List.filter
    (fun (name, size) ->
      if Hashtbl.mem seen name then false
      else (
        Hashtbl.add seen name size;
        true))
    vars
  |> List.sort (fun (a, _) (b, _) -> String.compare a b)

(* Rename variables in expression to x0, x1, x2, ... *)
let rename_vars_sequential (e : Sexpr.Expr.t) : Sexpr.Expr.t =
  let vars = unique_vars (extract_vars e) in
  let var_map = Hashtbl.create 16 in
  List.iteri
    (fun i (name, _) -> Hashtbl.add var_map name (Printf.sprintf "x%d" i))
    vars;
  (* Transfer signedness from old names to new names *)
  List.iter
    (fun (old_name, _) ->
      let new_name = Hashtbl.find var_map old_name in
      let signed = Option.value ~default:false (Hashtbl.find_opt var_signs old_name) in
      Hashtbl.replace var_signs new_name signed)
    vars;

  let rec rename (expr : Sexpr.Expr.t) : Sexpr.Expr.t =
    match expr with
    | Sexpr.Expr.Var v ->
        let new_name = Hashtbl.find var_map v.name in
        Sexpr.Expr.var new_name v.size new_name
    | Sexpr.Expr.Cst _ -> expr
    | Sexpr.Expr.Unary { f; x; _ } -> Sexpr.Expr.unary f (rename x)
    | Sexpr.Expr.Binary { f; x; y; _ } ->
        Sexpr.Expr.binary f (rename x) (rename y)
    | Sexpr.Expr.Load _ -> expr
    | Sexpr.Expr.Ite { c; t; e; _ } ->
        Sexpr.Expr.ite (rename c) (rename t) (rename e)
  in
  rename e

(* Convert bitvector size to C type (unsigned by default for safety) *)
let size_to_c_type (size : int) : string =
  match size with
  | 1 -> "unsigned char" (* bool, but use char for C compatibility *)
  | 8 -> "unsigned char"
  | 16 -> "unsigned short"
  | 32 -> "unsigned int"
  | 64 -> "unsigned long long"
  | 128 -> "__uint128_t"
  | n when n < 8 -> "unsigned char"
  | n when n < 16 -> "unsigned short"
  | n when n < 32 -> "unsigned int"
  | n when n < 64 -> "unsigned long long"
  | _ -> "__uint128_t"

(* Convert Sexpr.Expr.t to C expression string *)
let rec sexpr_to_c (e : Sexpr.Expr.t) : string =
  match e with
  | Sexpr.Expr.Var v -> v.name
  | Sexpr.Expr.Cst bv ->
      let value = Bitvector.value_of bv in
      let size = Bitvector.size_of bv in
      if size <= 32 then
        let hex_digits = (size + 3) / 4 in
        (* Round up to nearest hex digit *)
        let hex_str = Z.format "%x" value in
        let padded =
          String.make (max 0 (hex_digits - String.length hex_str)) '0' ^ hex_str
        in
        Printf.sprintf "0x%s" padded
      else if size <= 64 then
        let hex_str = Z.format "%x" value in
        let padded =
          String.make (max 0 (16 - String.length hex_str)) '0' ^ hex_str
        in
        Printf.sprintf "0x%s" padded
      else
        let hex_str = Z.format "%x" value in
        let padded =
          String.make (max 0 (32 - String.length hex_str)) '0' ^ hex_str
        in
        Printf.sprintf "0x%s" padded
  | Sexpr.Expr.Unary { f; x; _ } -> (
      let inner = sexpr_to_c x in
      match f with
      | Sexpr.Expr.Minus -> Printf.sprintf "(-%s)" inner
      | Sexpr.Expr.Not -> Printf.sprintf "(~%s)" inner
      | Sexpr.Expr.Uext n ->
          let target_size = Sexpr.Expr.sizeof x + n in
          let cast = size_to_c_type target_size in
          Printf.sprintf "((%s)%s)" cast inner
      | Sexpr.Expr.Sext n ->
          (* For sign extension, cast to signed first, then extend *)
          let src_size = Sexpr.Expr.sizeof x in
          let target_size = src_size + n in
          let signed_src =
            match src_size with
            | 8 -> "signed char"
            | 16 -> "short"
            | 32 -> "int"
            | 64 -> "long long"
            | _ -> "int"
          in
          let cast = size_to_c_type target_size in
          Printf.sprintf "((%s)((%s)%s))" cast signed_src inner
      | Sexpr.Expr.Restrict { lo; hi } ->
          let width = hi - lo + 1 in
          let mask = Z.sub (Z.shift_left Z.one width) Z.one in
          let hex_str = Z.format "%x" mask in
          let padded =
            String.make (max 0 (16 - String.length hex_str)) '0' ^ hex_str
          in
          if lo = 0 then Printf.sprintf "(%s & 0x%s)" inner padded
          else Printf.sprintf "((%s >> %d) & 0x%s)" inner lo padded)
  | Sexpr.Expr.Binary { f; x; y; _ } ->
      let left = sexpr_to_c x in
      let right = sexpr_to_c y in
      let op =
        match f with
        | Sexpr.Expr.Plus -> "+"
        | Sexpr.Expr.Minus -> "-"
        | Sexpr.Expr.Mul -> "*"
        | Sexpr.Expr.Udiv -> "/"
        | Sexpr.Expr.Sdiv -> "/" (* Note: C division of signed types *)
        | Sexpr.Expr.Umod -> "%"
        | Sexpr.Expr.Smod -> "%"
        | Sexpr.Expr.Or -> "|"
        | Sexpr.Expr.And -> "&"
        | Sexpr.Expr.Xor -> "^"
        | Sexpr.Expr.Lsl -> "<<"
        | Sexpr.Expr.Lsr -> ">>"
        | Sexpr.Expr.Asr -> ">>" (* Arithmetic shift - need signed cast *)
        | Sexpr.Expr.Rol -> failwith "ROL not directly expressible in C"
        | Sexpr.Expr.Ror -> failwith "ROR not directly expressible in C"
        | Sexpr.Expr.Concat -> failwith "Concat not directly expressible in C"
        | Sexpr.Expr.Eq -> "=="
        | Sexpr.Expr.Diff -> "!="
        | Sexpr.Expr.Ule -> "<="
        | Sexpr.Expr.Ult -> "<"
        | Sexpr.Expr.Uge -> ">="
        | Sexpr.Expr.Ugt -> ">"
        | Sexpr.Expr.Sle -> "<="
        | Sexpr.Expr.Slt -> "<"
        | Sexpr.Expr.Sge -> ">="
        | Sexpr.Expr.Sgt -> ">"
      in
      Printf.sprintf "(%s %s %s)" left op right
  | Sexpr.Expr.Load _ -> failwith "Load not expressible in C"
  | Sexpr.Expr.Ite { c; t; e; _ } ->
      Printf.sprintf "(%s ? %s : %s)" (sexpr_to_c c) (sexpr_to_c t)
        (sexpr_to_c e)

(* Helper: sign string for JSON *)
let sign_str (signed : bool) : string = if signed then "signed" else "unsigned"

(* Generate C file with extracted functions, print JSON metadata to stdout *)
let generate_c_file
    (exprs : (Sexpr.Expr.t * Cil.location * mba_class * bool) list)
    (output_path : string) : unit =
  let oc = open_out output_path in
  let fprintf = Printf.fprintf in

  (* Header *)
  fprintf oc "/* Extracted expressions from C source */\n";
  fprintf oc "/* Generated by c_extractor */\n\n";
  fprintf oc "#include <stdint.h>\n\n";

  (* Generate each function *)
  List.iteri
    (fun idx (expr, loc, _class_type, out_signed) ->
      let vars = unique_vars (extract_vars expr) in
      let return_size = Sexpr.Expr.sizeof expr in
      let return_type =
        if out_signed then
          match return_size with
          | 8 -> "int8_t" | 16 -> "int16_t" | 32 -> "int32_t"
          | 64 -> "int64_t" | _ -> "__int128"
        else size_to_c_type return_size
      in

      fprintf oc "/* %s:%d */\n" loc.file loc.line;
      fprintf oc "%s target_%d(" return_type idx;

      (match vars with
      | [] -> fprintf oc "void"
      | _ ->
          List.iteri
            (fun i (name, size) ->
              if i > 0 then fprintf oc ", ";
              let signed =
                Option.value ~default:false (Hashtbl.find_opt var_signs name)
              in
              let typ =
                if signed then
                  match size with
                  | 8 -> "int8_t" | 16 -> "int16_t" | 32 -> "int32_t"
                  | 64 -> "int64_t" | _ -> "__int128"
                else size_to_c_type size
              in
              fprintf oc "%s %s" typ name)
            vars);

      fprintf oc ") {\n";

      (try
         let c_expr = sexpr_to_c expr in
         fprintf oc "    return %s;\n" c_expr
       with Failure msg ->
         fprintf oc "    /* Error: %s */\n" msg;
         fprintf oc "    return 0;\n");

      fprintf oc "}\n\n")
    exprs;

  fprintf oc "int main() { return 0; }\n";
  close_out oc;

  (* Output JSON metadata to stdout *)
  let json_list =
    List.mapi
      (fun idx (expr, loc, class_type, out_signed) ->
        let vars = unique_vars (extract_vars expr) in
        let var_list =
          List.map
            (fun (name, size) ->
              let signed =
                Option.value ~default:false (Hashtbl.find_opt var_signs name)
              in
              `Assoc
                [
                  ("name", `String name);
                  ("size", `Int size);
                  ("sign", `String (sign_str signed));
                ])
            vars
        in
        let input_signs =
          `Assoc
            (List.map
               (fun (name, _) ->
                 let signed =
                   Option.value ~default:false (Hashtbl.find_opt var_signs name)
                 in
                 (name, `String (sign_str signed)))
               vars)
        in
        `Assoc
          [
            ("id", `Int idx);
            ("function", `String (Printf.sprintf "target_%d" idx));
            ("expr", `String (Greysynth_utils.Utils.pp expr));
            ("file", `String loc.file);
            ("line", `Int loc.line);
            ("size", `Int (Greysynth_utils.Utils.size_of_expr expr));
            ("bitwidth", `Int (Sexpr.Expr.sizeof expr));
            ("classification", `String (class_to_string class_type));
            ("depth", `Int (Greysynth_utils.Utils.depth_of_expr expr));
            ("output_sign", `String (sign_str out_signed));
            ("input_signs", input_signs);
            ("variables", `List var_list);
          ])
      exprs
  in
  print_endline (Yojson.Basic.pretty_to_string (`List json_list))

(* ANSI color codes *)
let color_reset = "\027[0m"
let color_bold = "\027[1m"
let color_blue = "\027[34m"
let color_green = "\027[32m"
let color_cyan = "\027[36m"

(* Main *)
let () =
  let input_file = ref None in
  let output_json = ref false in
  let dedupe = ref false in
  let do_preprocess = ref false in
  let extract_file = ref None in
  let use_colors = ref true in

  let usage_msg =
    "Usage:\n\
    \  c_extractor <file.c> [options]\n\n\
     Extracts arithmetic/boolean expressions from C files.\n\n\
     MBA Classifications:\n\
     - bitwise: Pure bitwise operations (&, |, ^, ~) on variables\n\
     - linear: Sum of (constant * bitwise_operation)\n\
     Example: 2*(x&y) + 3*(a|b)\n\
     - polynomial: Sum of (constant * product_of_bitwise_operations)\n\
     Example: (x&y)*(x|y) + (x&~y)*(~x&y)\n\
     - non-polynomial: MBA operations (+, -, *, &, |, ^, ~, <<) but not \
     polynomial\n\
     - non-mba: Contains non-MBA operations (div, mod, >>, etc.)\n\n\
     GAMBA-Friendly Mode (-gamba-friendly):\n\
     Transforms expressions to be compatible with GAMBA simplifier:\n\
     - Removes type casts (sext, uext, restrict)\n\
     - Excludes division and modulo operations\n\
     - Excludes right shifts (>>, >>s)\n\
     - Propagates variable sizes (e.g., x<8> becomes x<32>)\n\
     Example: (uext(56) x<8>) + 5 becomes x<64> + 5\n\n\
     Note: Use -E to preprocess the file first (recommended for most C files).\n\
     You can also preprocess manually: gcc -E file.c > file.i\n\n\
     Options:"
  in

  let set_output_dir dir =
    (* Create directory if it doesn't exist *)
    if not (Sys.file_exists dir) then Unix.mkdir dir 0o755;
    extract_file := Some (Filename.concat dir "extracted.c")
  in

  let spec =
    [
      ( "-min-depth",
        Arg.Set_int min_depth,
        "<n> Minimum expression depth to extract (default: 1)" );
      ( "-ptr-size",
        Arg.Set_int pointer_size,
        "<bits> Pointer size in bits (default: 64)" );
      ("-json", Arg.Set output_json, " Output as JSON");
      ("-dedupe", Arg.Set dedupe, " Deduplicate expressions");
      ( "-extract",
        Arg.String (fun s -> extract_file := Some s),
        "<file.c> Generate C file with target_N functions" );
      ( "--out",
        Arg.String set_output_dir,
        "<dir> Output directory (creates extracted.c and extracted.json)" );
      ("-E", Arg.Set do_preprocess, " Preprocess the file with gcc -E first");
      ( "-cpp",
        Arg.Set_string cpp_command,
        "<cmd> Preprocessor command (default: gcc)" );
      ( "-I",
        Arg.String (fun s -> cpp_args := ("-I" ^ s) :: !cpp_args),
        "<dir> Add include directory (passed to preprocessor)" );
      ( "-D",
        Arg.String (fun s -> cpp_args := ("-D" ^ s) :: !cpp_args),
        "<macro> Define macro (passed to preprocessor)" );
      ( "-macos",
        Arg.Unit (fun () -> cpp_args := macos_compat_defines @ !cpp_args),
        " Add compatibility defines for macOS system headers" );
      ( "-nostdinc",
        Arg.Unit (fun () -> cpp_args := "-nostdinc" :: !cpp_args),
        " Don't include standard system headers (use with self-contained files)"
      );
      ( "-inline-constants",
        Arg.Set inline_constants,
        " Inline global constant variables" );
      ("-debug-const", Arg.Set debug_const, " Debug constant collection");
      ("-no-color", Arg.Clear use_colors, " Disable colored output");
      ( "-exclude-bitwise",
        Arg.Set exclude_bitwise,
        " Exclude pure bitwise expressions" );
      ( "-exclude-linear",
        Arg.Set exclude_linear,
        " Exclude linear MBA expressions" );
      ( "-exclude-polynomial",
        Arg.Set exclude_polynomial,
        " Exclude polynomial MBA expressions" );
      ( "-exclude-non-polynomial",
        Arg.Set exclude_non_polynomial,
        " Exclude non-polynomial MBA expressions" );
      ( "-exclude-non-mba",
        Arg.Set exclude_non_mba,
        " Exclude non-MBA expressions (with div, mod, >>, etc.)" );
      ( "-gamba-friendly",
        Arg.Set gamba_friendly_mode,
        " Transform to GAMBA-compatible format (remove casts, div, mod, right \
         shifts)" );
      ( "-rename-vars",
        Arg.Set rename_variables,
        " Rename variables to x0, x1, x2, ..." );
    ]
  in

  Arg.parse spec (fun s -> input_file := Some s) usage_msg;

  match !input_file with
  | None ->
      Arg.usage spec usage_msg;
      exit 1
  | Some file -> (
      try
        let exprs = extract_from_file ~preprocess:!do_preprocess file in
        let exprs = if !dedupe then deduplicate exprs else exprs in

        (* Apply GAMBA-friendly transformations if requested *)
        let exprs =
          if !gamba_friendly_mode then
            List.filter_map
              (fun (e, loc, out_signed) ->
                match make_gamba_friendly e with
                | Some e' -> Some (e', loc, out_signed)
                | None -> None)
              exprs
          else exprs
        in

        (* Apply variable renaming if requested *)
        let exprs =
          if !rename_variables then
            List.map
              (fun (e, loc, out_signed) -> (rename_vars_sequential e, loc, out_signed))
              exprs
          else exprs
        in

        (* Classify and filter expressions *)
        let exprs_with_class =
          List.map (fun (e, loc, out_signed) -> (e, loc, classify_expr e, out_signed)) exprs
        in
        let exprs_with_class =
          List.filter
            (fun (_, _, class_type, _) -> not (should_exclude class_type))
            exprs_with_class
        in

        match !extract_file with
        | Some output_path -> generate_c_file exprs_with_class output_path
        | None ->
        if !output_json then
          let json_list =
            List.map
              (fun (e, loc, class_type, out_signed) ->
                let vars = unique_vars (extract_vars e) in
                let input_signs =
                  `Assoc
                    (List.map
                       (fun (name, _) ->
                         let signed =
                           Option.value ~default:false
                             (Hashtbl.find_opt var_signs name)
                         in
                         (name, `String (sign_str signed)))
                       vars)
                in
                `Assoc
                  [
                    ("expr", `String (Greysynth_utils.Utils.pp e));
                    ("size", `Int (Greysynth_utils.Utils.size_of_expr e));
                    ("bitwidth", `Int (Sexpr.Expr.sizeof e));
                    ("line", `Int loc.line);
                    ("file", `String loc.file);
                    ("classification", `String (class_to_string class_type));
                    ("depth", `Int (Greysynth_utils.Utils.depth_of_expr e));
                    ("gamba_friendly", `Bool (is_gamba_compatible e));
                    ("output_sign", `String (sign_str out_signed));
                    ("input_signs", input_signs);
                  ])
              exprs_with_class
          in
          print_endline (Yojson.Basic.pretty_to_string (`List json_list))
        else
          List.iter
            (fun (e, loc, class_type, _out_signed) ->
              let gamba_status =
                if is_gamba_compatible e then "✓ GAMBA" else "✗ GAMBA"
              in
              if !use_colors then
                let gamba_colored =
                  if is_gamba_compatible e then "\027[32m✓ GAMBA\027[0m"
                    (* green checkmark *)
                  else "\027[31m✗ GAMBA\027[0m" (* red X *)
                in
                Printf.printf "%s%s%s:%s%d%s [%s] [%s]: %s%s%s\n" color_bold
                  color_blue loc.file color_green loc.line color_reset
                  (class_to_colored_string class_type)
                  gamba_colored color_cyan (Greysynth_utils.Utils.pp e)
                  color_reset
              else
                Printf.printf "%s:%d [%s] [%s]: %s\n" loc.file loc.line
                  (class_to_string class_type)
                  gamba_status (Greysynth_utils.Utils.pp e))
            exprs_with_class
      with
      | Failure msg ->
          Format.eprintf "Error: %s\n" msg;
          exit 1
      | e ->
          Format.eprintf "Unexpected error: %s\n" (Printexc.to_string e);
          exit 1)
