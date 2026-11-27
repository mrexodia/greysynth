(* Shared typed-AST, bitvector, constant, and canonicalization helpers.
All transformations remain untrusted candidates gated by Rewrite/Rewrite_proof. *)

(* Deterministic candidate generation before stochastic synthesis. Every
   replacement, including simple bitvector identities, crosses Rewrite.accepts.
   The local MBA normalizer treats unsupported subtrees as structural atoms;
   finite truth tables are used only to propose universally linear identities. *)

module E = Sexpr.Expr
module Nodes = Sexpr.BvTbl

let constant width value = E.constant (Bitvector.create value width)
let integer width value = constant width (Z.of_int value)
let zeros width = integer width 0

let rec constant_value = function
  | E.Cst value -> Some value
  | E.Unary { f; x; _ } ->
      Option.bind (constant_value x) (fun value ->
          try Some (Term.Bv.unary f value) with _ -> None)
  | _ -> None

let canonical_bitwise_atom expression =
  match constant_value expression with
  | Some value when not (Bitvector.is_zeros value || Bitvector.is_fill value) ->
      let complement = Bitvector.lognot value in
      if Bitvector.compare value complement <= 0 then (E.constant value, false)
      else (E.constant complement, true)
  | _ -> (expression, false)

let is_number number expression =
  match constant_value expression with
  | Some value -> Z.equal (Bitvector.value_of value) number
  | None -> false

let low_bits expression count =
  let width = E.sizeof expression in
  if count <= 0 then zeros width
  else if count >= width then expression
  else E.unary (E.Uext (width - count)) (E.restrict ~lo:0 ~hi:(count - 1) expression)

let logical_right expression count =
  let width = E.sizeof expression in
  if count <= 0 then expression
  else if count >= width then zeros width
  else
    match constant_value expression with
    | Some value -> E.constant (Bitvector.shift_right value count)
    | None -> E.unary (E.Uext count) (E.restrict ~lo:count ~hi:(width - 1) expression)

let arithmetic_right expression count =
  let width = E.sizeof expression in
  if count <= 0 then expression
  else
    let count = min count (width - 1) in
    E.unary (E.Sext count) (E.restrict ~lo:count ~hi:(width - 1) expression)

let bounded_count width value =
  let value = Bitvector.value_of value in
  if Z.geq value (Z.of_int width) then width else Z.to_int value
