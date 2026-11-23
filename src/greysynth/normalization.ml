(* Deterministic candidate generation before stochastic synthesis. Every
   replacement, including simple bitvector identities, crosses Rewrite.accepts.
   The local MBA normalizer treats unsupported subtrees as structural atoms;
   finite truth tables are used only to propose universally linear identities. *)

open Config
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

let peepholes evaluate expression =
  let width = E.sizeof expression in
  let zero = zeros width and one = integer width 1 in
  let fill = constant width (Z.pred (Z.shift_left Z.one width)) in
  let same = E.is_equal in
  match expression with
  | E.Unary { f = E.Not; x = E.Unary { f = E.Not; x; _ }; _ }
  | E.Unary { f = E.Minus; x = E.Unary { f = E.Minus; x; _ }; _ } -> [ x ]
  | E.Unary { f; x; _ } -> (
      match constant_value x with
      | Some value -> (try [ E.constant (Term.Bv.unary f value) ] with _ -> [])
      | None -> [])
  | E.Binary { f; x; y; _ } ->
      let folded =
        match constant_value x, constant_value y with
        | Some _, Some _ -> (try [ E.constant (evaluate expression 0) ] with _ -> [])
        | _ -> []
      in
      let merge_masked_addition () =
        let masked = function
          | E.Binary { f = E.And; x = base; y = E.Cst mask; _ }
          | E.Binary { f = E.And; x = E.Cst mask; y = base; _ } -> Some (base, mask)
          | E.Unary {
              f = E.Uext _;
              x = E.Unary { f = E.Restrict { lo = 0; hi }; x = base; _ };
              size;
              _;
            } ->
              Some (base, Bitvector.create (Z.pred (Z.shift_left Z.one (hi + 1))) size)
          | _ -> None
        in
        match masked x, masked y with
        | Some (left, left_mask), Some (right, right_mask) when same left right ->
            let left_bits = Bitvector.value_of left_mask in
            let right_bits = Bitvector.value_of right_mask in
            if Z.equal (Z.logand left_bits right_bits) Z.zero then
              let combined = Bitvector.logor left_mask right_mask in
              if Bitvector.is_fill combined then [ left ]
              else [ E.binary E.And left (E.constant combined) ]
            else []
        | _ -> []
      in
      let merge_scaled_masks () =
        let masked_term = function
          | E.Binary { f = E.And; x = base; y = E.Cst mask; _ }
          | E.Binary { f = E.And; x = E.Cst mask; y = base; _ } -> Some (base, mask)
          | E.Unary {
              f = E.Uext _;
              x = E.Unary { f = E.Restrict { lo = 0; hi }; x = base; _ };
              size;
              _;
            } ->
              Some (base, Bitvector.create (Z.pred (Z.shift_left Z.one (hi + 1))) size)
          | _ -> None
        in
        let scaled_masked = function
          | E.Binary { f = E.Mul; x; y; _ } ->
              (match constant_value x, constant_value y with
              | Some coefficient, _ ->
                  Option.map (fun (base, mask) -> (coefficient, base, mask))
                    (masked_term y)
              | _, Some coefficient ->
                  Option.map (fun (base, mask) -> (coefficient, base, mask))
                    (masked_term x)
              | _ -> None)
          | _ -> None
        in
        match scaled_masked x, scaled_masked y with
        | Some (left_coefficient, left, left_mask),
          Some (right_coefficient, right, right_mask)
          when Bitvector.equal left_coefficient right_coefficient && same left right ->
            let left_bits = Bitvector.value_of left_mask
            and right_bits = Bitvector.value_of right_mask in
            if Z.equal (Z.logand left_bits right_bits) Z.zero then
              let combined = Bitvector.logor left_mask right_mask in
              let merged =
                if Bitvector.is_fill combined then left
                else E.binary E.And left (E.constant combined)
              in
              [ E.binary E.Mul (E.constant left_coefficient) merged ]
            else []
        | _ -> []
      in
      let complements left right =
        match left, right with
        | E.Unary { f = E.Not; x; _ }, other
        | other, E.Unary { f = E.Not; x; _ } -> same x other
        | _ -> false
      in
      let negates left right =
        match left, right with
        | E.Unary { f = E.Minus; x; _ }, other
        | other, E.Unary { f = E.Minus; x; _ } -> same x other
        | _ -> false
      in
      let null_quadratic () =
        let rec flatten coefficient factors = function
          | E.Binary { f = E.Mul; x; y; _ } ->
              let coefficient, factors = flatten coefficient factors x in
              flatten coefficient factors y
          | term ->
              (match constant_value term with
              | Some value ->
                  (Z.mul coefficient (Bitvector.value_of value), factors)
              | None -> (coefficient, term :: factors))
        in
        let coefficient, factors = flatten Z.one [] expression in
        let half = Z.shift_left Z.one (E.sizeof x - 1) in
        let divisible = Z.equal (Z.erem coefficient half) Z.zero in
        let pair =
          match factors with
          | [ first; E.Binary { f = E.Minus; x = second; y = one; _ } ]
          | [ E.Binary { f = E.Minus; x = second; y = one; _ }; first ] ->
              same first second && is_number Z.one one
          | _ -> false
        in
        if divisible && pair then [ zero ] else []
      in
      let identities =
        match f with
        | E.Mul when null_quadratic () <> [] -> null_quadratic ()
        | E.And when complements x y -> [ zero ]
        | E.Or | E.Xor when complements x y -> [ fill ]
        | E.Plus when complements x y -> [ fill ]
        | E.Plus when negates x y -> [ zero ]
        | E.Plus when merge_scaled_masks () <> [] -> merge_scaled_masks ()
        | E.Plus when merge_masked_addition () <> [] -> merge_masked_addition ()
        | E.Plus when is_number Z.zero x -> [ y ]
        | E.Plus | E.Minus | E.Or | E.Xor when is_number Z.zero y -> [ x ]
        | E.Or | E.Xor when is_number Z.zero x -> [ y ]
        | E.Mul | E.And when is_number Z.zero x || is_number Z.zero y -> [ zero ]
        | E.Mul when is_number Z.one x -> [ y ]
        | E.Mul | E.Udiv | E.Sdiv when is_number Z.one y -> [ x ]
        | E.Minus | E.Xor when same x y -> [ zero ]
        | E.And | E.Or when same x y -> [ x ]
        | E.Umod | E.Smod when same x y || is_number Z.one y -> [ zero ]
        | E.Eq | E.Ule | E.Uge | E.Sle | E.Sge when same x y -> [ one ]
        | E.Diff | E.Ult | E.Ugt | E.Slt | E.Sgt when same x y -> [ zero ]
        | E.Ult when is_number Z.zero y -> [ zero ]
        | E.Uge when is_number Z.zero y -> [ one ]
        | E.Ule when is_number (Z.pred (Z.shift_left Z.one (E.sizeof x))) y -> [ one ]
        | E.Ugt when is_number (Z.pred (Z.shift_left Z.one (E.sizeof x))) y -> [ zero ]
        | E.Slt when is_number (Z.shift_left Z.one (E.sizeof x - 1)) y -> [ zero ]
        | E.Sge when is_number (Z.shift_left Z.one (E.sizeof x - 1)) y -> [ one ]
        | E.Sle when is_number (Z.pred (Z.shift_left Z.one (E.sizeof x - 1))) y -> [ one ]
        | E.Sgt when is_number (Z.pred (Z.shift_left Z.one (E.sizeof x - 1))) y -> [ zero ]
        | E.And -> (
            let masked base mask =
              match constant_value mask with
              | Some value ->
                  let bits = Bitvector.value_of value in
                  if Z.equal (Z.logand bits (Z.succ bits)) Z.zero then
                    [ low_bits base (Z.numbits bits) ]
                  else []
              | None -> []
            in
            masked x y @ masked y x)
        | E.Udiv | E.Umod -> (
            match constant_value y with
            | Some divisor ->
                let value = Bitvector.value_of divisor in
                if Z.equal value Z.zero then
                  [ if f = E.Udiv then fill else x ]
                else if Z.popcount value = 1 then
                  let count = Z.trailing_zeros value in
                  [ if f = E.Udiv then logical_right x count else low_bits x count ]
                else []
            | None -> (
                match f, y with
                | E.Udiv, E.Binary { f = E.Lsl; x = base; y = amount; _ } -> (
                    match constant_value amount with
                    | None -> []
                    | Some amount ->
                        let count = bounded_count width amount in
                        if count >= width then [ fill ]
                        else
                          [ E.binary E.Udiv (logical_right x count)
                              (low_bits base (width - count)) ])
                | _ -> []))
        | E.Lsl | E.Lsr | E.Asr | E.Rol | E.Ror -> (
            match constant_value y with
            | None -> []
            | Some amount ->
                let count = bounded_count width amount in
                if f = E.Lsr then [ logical_right x count ]
                else if f = E.Asr then [ arithmetic_right x count ]
                else if f = E.Lsl then
                  if count >= width then [ zero ] else if count = 0 then [ x ] else []
                else if Z.equal (Z.rem (Bitvector.value_of amount) (Z.of_int width)) Z.zero
                then [ x ] else [])
        | E.Concat -> (
            if is_number Z.zero x then [ E.unary (E.Uext (E.sizeof x)) y ]
            else
              match x, y with
              | E.Unary { f = E.Restrict a; x = lhs; _ },
                E.Unary { f = E.Restrict b; x = rhs; _ }
                when same lhs rhs && a.lo = b.hi + 1 ->
                  [ E.restrict ~lo:b.lo ~hi:a.hi lhs ]
              | _ -> [])
        | _ -> []
      in
      folded @ identities
  | E.Ite { c; t; e; _ } ->
      if same t e then [ t ]
      else
        let branch_width = E.sizeof t in
        let condition_mask =
          if E.sizeof c = 1 then Some (E.unary (E.Sext (branch_width - 1)) c)
          else None
        in
        (match constant_value c with
        | Some condition -> [ if Bitvector.is_zeros condition then e else t ]
        | None when branch_width = 1 && is_number Z.one t && is_number Z.zero e -> [ c ]
        | None ->
            match condition_mask with
            | Some mask when is_number Z.zero e
                             && is_number (Z.pred (Z.shift_left Z.one branch_width)) t ->
                [ mask ]
            | Some mask when is_number Z.zero t
                             && is_number (Z.pred (Z.shift_left Z.one branch_width)) e ->
                [ E.unary E.Not mask ]
            | Some mask when is_number Z.zero e -> [ E.binary E.And t mask ]
            | Some mask when is_number Z.zero t ->
                [ E.binary E.And e (E.unary E.Not mask) ]
            | _ -> [])
  | _ -> []

let build_balanced op = function
  | [] -> invalid_arg "normalization: empty associative expression"
  | terms ->
      let rec build = function
        | [] -> assert false
        | [ term ] -> term
        | terms ->
            let count = List.length terms in
            let rec split n left rest =
              if n = 0 then (List.rev left, rest)
              else match rest with
                | head :: tail -> split (n - 1) (head :: left) tail
                | [] -> assert false
            in
            let left, right = split (count / 2) [] terms in
            E.binary op (build left) (build right)
      in
      build terms

(* Exact associative/commutative candidates. These rules do not depend on
   finite truth tables; the shared acceptance boundary still proves every
   size-reducing result. *)
let canonical_candidates expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let normalize value = Z.erem value modulus |> fun value ->
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let const value = constant width (normalize value) in
  let rec flatten op acc = function
    | E.Binary { f; x; y; _ } when f = op -> flatten op (flatten op acc x) y
    | term -> term :: acc
  in
  let sorted terms = List.sort E.compare terms in
  match expression with
  | E.Binary { f = (E.Plus | E.Minus); _ } ->
      let coefficients = Nodes.create 16 in
      let offset = ref Z.zero in
      let add atom coefficient =
        let old = Option.value (Nodes.find_opt coefficients atom) ~default:Z.zero in
        Nodes.replace coefficients atom (normalize (Z.add old coefficient))
      in
      let rec collect coefficient = function
        | E.Cst value ->
            offset := normalize (Z.add !offset (Z.mul coefficient (Bitvector.value_of value)))
        | E.Unary { f = E.Minus; x; _ } -> collect (Z.neg coefficient) x
        | E.Binary { f = E.Plus; x; y; _ } -> collect coefficient x; collect coefficient y
        | E.Binary { f = E.Minus; x; y; _ } ->
            collect coefficient x; collect (Z.neg coefficient) y
        | E.Binary { f = E.Mul; x = E.Cst value; y; _ }
        | E.Binary { f = E.Mul; x = y; y = E.Cst value; _ } ->
            collect (Z.mul coefficient (Bitvector.value_of value)) y
        | E.Binary { f = E.Lsl; x; y = E.Cst amount; _ }
          when Z.lt (Bitvector.value_of amount) (Z.of_int width) ->
            let scale = Z.shift_left Z.one (Z.to_int (Bitvector.value_of amount)) in
            collect (Z.mul coefficient scale) x
        | atom -> add atom coefficient
      in
      collect Z.one expression;
      let positives, negatives =
        Nodes.fold
          (fun atom coefficient (positives, negatives) ->
            let coefficient = normalize coefficient in
            if Z.equal coefficient Z.zero then (positives, negatives)
            else if Z.equal coefficient (Z.pred modulus) then
              (positives, atom :: negatives)
            else
              let term =
                if Z.equal coefficient Z.one then atom
                else E.binary E.Mul atom (const coefficient)
              in
              (term :: positives, negatives))
          coefficients ([], [])
      in
      let positives =
        if Z.equal !offset Z.zero then positives else const !offset :: positives
      in
      let positive =
        match sorted positives with
        | [] -> None
        | terms -> Some (build_balanced E.Plus terms)
      in
      let negative =
        match sorted negatives with
        | [] -> None
        | terms -> Some (build_balanced E.Plus terms)
      in
      [ (match positive, negative with
        | None, None -> zeros width
        | Some result, None -> result
        | None, Some result -> E.unary E.Minus result
        | Some positive, Some negative -> E.binary E.Minus positive negative) ]
  | E.Binary { f = E.Xor; _ } ->
      let terms = flatten E.Xor [] expression in
      let counts = Nodes.create 16 and bits = ref Z.zero in
      List.iter
        (function
          | E.Cst value -> bits := Z.logxor !bits (Bitvector.value_of value)
          | term ->
              let count = Option.value (Nodes.find_opt counts term) ~default:0 in
              Nodes.replace counts term (count lxor 1))
        terms;
      let terms = Nodes.fold (fun term odd acc -> if odd = 1 then term :: acc else acc) counts [] in
      let terms = if Z.equal !bits Z.zero then terms else const !bits :: terms in
      [ (match sorted terms with [] -> zeros width | terms -> build_balanced E.Xor terms) ]
  | E.Binary { f = (E.And | E.Or as op); _ } ->
      let terms = flatten op [] expression |> List.sort_uniq E.compare in
      let zero = Z.zero and fill = Z.pred modulus in
      let constant_value = if op = E.And then fill else zero in
      let absorbing = if op = E.And then zero else fill in
      let constants, terms = List.partition_map
          (function E.Cst value -> Left (Bitvector.value_of value) | term -> Right term) terms in
      let combined = List.fold_left
          (if op = E.And then Z.logand else Z.logor) constant_value constants |> normalize in
      let has_complement = List.exists (function
          | E.Unary { f = E.Not; x; _ } -> List.exists (E.is_equal x) terms
          | term -> List.exists (function
              | E.Unary { f = E.Not; x; _ } -> E.is_equal x term
              | _ -> false) terms) terms in
      if has_complement || Z.equal combined absorbing then [ const absorbing ]
      else
        let terms = if Z.equal combined constant_value then terms else const combined :: terms in
        [ (match sorted terms with [] -> const constant_value | terms -> build_balanced op terms) ]
  | E.Binary { f = E.Mul; _ } ->
      let terms = flatten E.Mul [] expression in
      let coefficient, terms = List.fold_left
          (fun (coefficient, terms) -> function
            | E.Cst value -> (normalize (Z.mul coefficient (Bitvector.value_of value)), terms)
            | term -> (coefficient, term :: terms))
          (Z.one, []) terms in
      if Z.equal coefficient Z.zero then [ zeros width ]
      else if terms = [] then [ const coefficient ]
      else
        let terms = if Z.equal coefficient Z.one then terms else const coefficient :: terms in
        [ build_balanced E.Mul (sorted terms) ]
  | _ -> []

let minterm_ring_expansion original candidate =
  let width = E.sizeof original in
  if E.sizeof candidate <> width then None
  else
    let atom_table = Sexpr.BvTbl.create 16 in
    let valid = ref true in
    let add_atom expression =
      let expression, _ = canonical_bitwise_atom expression in
      if E.sizeof expression = width then Sexpr.BvTbl.replace atom_table expression ()
    in
    let rec collect_boolean = function
      | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
      | E.Unary { f = E.Not; x; _ } -> collect_boolean x
      | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
          collect_boolean x; collect_boolean y
      | expression -> add_atom expression
    and collect_arithmetic expression =
      if Sexpr.BvTbl.mem atom_table expression then ()
      else
        match expression with
        | E.Cst _ -> ()
        | E.Unary { f = E.Minus; x; _ } -> collect_arithmetic x
        | E.Binary { f = (E.Plus | E.Minus); x; y; _ } ->
            collect_arithmetic x; collect_arithmetic y
        | E.Binary { f = E.Mul; x; y; _ } ->
            (match constant_value x, constant_value y with
            | Some _, _ -> collect_arithmetic y
            | _, Some _ -> collect_arithmetic x
            | _ -> collect_arithmetic x; collect_arithmetic y)
        | E.Binary { f = E.Lsl; x; y; _ } when Option.is_some (constant_value y) ->
            collect_arithmetic x
        | (E.Var _ | E.Unary { f = E.Not; _ }
          | E.Binary { f = (E.And | E.Or | E.Xor); _ }) as expression ->
            collect_boolean expression
        | _ -> valid := false
    in
    (* Source bitwise contexts define opaque atoms first; candidate arithmetic
       may then reuse the exact same compound term (for example [x*y]). *)
    collect_arithmetic original;
    collect_arithmetic candidate;
    let atoms =
      Sexpr.BvTbl.fold (fun expression () result -> expression :: result)
        atom_table []
      |> List.sort E.compare |> Array.of_list
    in
    if not !valid || Array.length atoms = 0
       || Array.length atoms > !c_normalization_max_atoms then None
    else
      let count = Array.length atoms in
      let atom_index expression =
        let expression, complemented = canonical_bitwise_atom expression in
        let rec find index =
          if index = count then None
          else if E.is_equal atoms.(index) expression then Some (index, complemented)
          else find (index + 1)
        in
        find 0
      in
      let rec boolean_value assignment expression =
        match atom_index expression with
        | Some (index, complemented) ->
            let value = assignment land (1 lsl index) <> 0 in
            Some (if complemented then not value else value)
        | None ->
            match expression with
            | E.Cst value when Bitvector.is_zeros value -> Some false
            | E.Cst value when Bitvector.is_fill value -> Some true
            | E.Unary { f = E.Not; x; _ } ->
                Option.map not (boolean_value assignment x)
            | E.Binary { f = (E.And | E.Or | E.Xor as op); x; y; _ } ->
                Option.bind (boolean_value assignment x) (fun left ->
                    Option.map
                      (fun right ->
                        match op with
                        | E.And -> left && right
                        | E.Or -> left || right
                        | E.Xor -> left <> right
                        | _ -> assert false)
                      (boolean_value assignment y))
            | _ -> None
      in
      let is_boolean expression =
        let saw_variable = ref false in
        let rec inspect expression =
          if Option.is_some (atom_index expression) then (
            saw_variable := true;
            true)
          else
            match expression with
            | E.Cst value -> Bitvector.is_zeros value || Bitvector.is_fill value
            | E.Unary { f = E.Not; x; _ } -> inspect x
            | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
                inspect x && inspect y
            | _ -> false
        in
        inspect expression && !saw_variable
      in
      let minterms =
        Array.init (1 lsl count) (fun assignment ->
            Array.to_list atoms
            |> List.mapi (fun index atom ->
                   if assignment land (1 lsl index) = 0 then E.unary E.Not atom
                   else atom)
            |> function
            | head :: tail -> List.fold_left (fun result term -> E.binary E.And result term) head tail
            | [] -> assert false)
      in
      let rec sum = function
        | [] -> zeros width
        | [ term ] -> term
        | head :: tail -> E.binary E.Plus head (sum tail)
      in
      let all_minterms = sum (Array.to_list minterms) in
      let fill_expr = E.constant (Bitvector.fill width) in
      let expansions = Hashtbl.create 32 in
      let smt_edges = ref [] and ring_edges = ref [] in
      let fill_expanded = ref false in
      let ensure_fill_expansion () =
        if not !fill_expanded then (
          fill_expanded := true;
          smt_edges := (fill_expr, all_minterms) :: !smt_edges)
      in
      let expand_boolean expression =
        match Hashtbl.find_opt expansions expression with
        | Some result -> result
        | None ->
            let result =
              List.init (Array.length minterms) Fun.id
              |> List.filter (fun assignment ->
                     boolean_value assignment expression = Some true)
              |> List.map (Array.get minterms) |> sum
            in
            Hashtbl.add expansions expression result;
            smt_edges := (expression, result) :: !smt_edges;
            result
      in
      let rec expand expression =
        if is_boolean expression then Some (expand_boolean expression)
        else
          match expression with
          | E.Cst value when Bitvector.is_zeros value -> Some expression
          | E.Cst value ->
              ensure_fill_expansion ();
              if Bitvector.is_fill value then Some all_minterms
              else
                let coefficient = E.constant (Bitvector.neg value) in
                let via_fill = E.binary E.Mul coefficient fill_expr in
                ring_edges := (expression, via_fill) :: !ring_edges;
                Some (E.binary E.Mul coefficient all_minterms)
          | E.Unary { f = E.Minus; x; _ } -> Option.map (E.unary E.Minus) (expand x)
          | E.Binary { f = E.Mul; x; y; _ } ->
              (match constant_value x, constant_value y with
              | Some _, _ -> Option.map (fun y -> E.binary E.Mul x y) (expand y)
              | _, Some _ -> Option.map (fun x -> E.binary E.Mul x y) (expand x)
              | _ ->
                  Option.bind (expand x) (fun x ->
                      Option.map (fun y -> E.binary E.Mul x y) (expand y)))
          | E.Binary { f = (E.Plus | E.Minus as op); x; y; _ } ->
              Option.bind (expand x) (fun x ->
                  Option.map (fun y -> E.binary op x y) (expand y))
          | E.Binary { f = E.Lsl; x; y; _ } ->
              (match constant_value y with
              | Some amount when Z.lt (Bitvector.value_of amount) (Z.of_int width) ->
                  Option.map
                    (fun expanded_x ->
                      let power =
                        constant width
                          (Z.shift_left Z.one (Z.to_int (Bitvector.value_of amount)))
                      in
                      let unexpanded = E.binary E.Mul x power in
                      smt_edges := (expression, unexpanded) :: !smt_edges;
                      E.binary E.Mul expanded_x power)
                    (expand x)
              | _ -> None)
          | _ -> None
      in
      Option.bind (expand original) (fun left ->
          Option.map
            (fun right ->
              (List.rev !smt_edges, List.rev ((left, right) :: !ring_edges),
               left, right))
            (expand candidate))

let minterm_ring_proof original candidate =
  Option.map
    (fun (equalities, ring_equalities, _, _) -> (equalities, ring_equalities))
    (minterm_ring_expansion original candidate)

(* Break constant-scaled complements into small replayable algebraic steps.
   This avoids one monolithic bit-blasted proof for otherwise linear MBAs. *)
let complement_product_steps original candidate =
  let negate value = Bitvector.neg value in
  let rec rewrite expression =
    let rewritten, child_edges =
      match expression with
      | E.Unary { f; x; _ } ->
          let x, edges = rewrite x in
          (E.unary f x, edges)
      | E.Binary { f; x; y; _ } ->
          let x, left = rewrite x in
          let y, right = rewrite y in
          (E.binary f x y, left @ right)
      | E.Ite { c; t; e; _ } ->
          let c, first = rewrite c in
          let t, second = rewrite t in
          let e, third = rewrite e in
          (E.ite c t e, first @ second @ third)
      | _ -> (expression, [])
    in
    match rewritten with
    | E.Unary { f = E.Not; x = term; _ } ->
        let replacement =
          E.binary E.Minus (E.unary E.Minus term) (integer (E.sizeof term) 1)
        in
        (replacement, (rewritten, replacement) :: child_edges)
    | E.Binary { f = E.Mul; x = E.Cst coefficient;
                 y = E.Unary { f = E.Not; x = term; _ }; _ }
    | E.Binary { f = E.Mul; x = E.Unary { f = E.Not; x = term; _ };
                 y = E.Cst coefficient; _ } ->
        let inverse = negate coefficient in
        let replacement =
          E.binary E.Plus (E.binary E.Mul (E.constant inverse) term)
            (E.constant inverse)
        in
        (replacement, (rewritten, replacement) :: child_edges)
    | _ -> (rewritten, child_edges)
  in
  let rewritten, edges = rewrite original in
  if edges = [] then None
  else
    let compact =
      canonical_candidates rewritten
      |> List.sort (fun left right ->
             Int.compare (Greysynth_utils.Utils.size_of_expr left)
               (Greysynth_utils.Utils.size_of_expr right))
      |> function head :: _ -> head | [] -> rewritten
    in
    Some (edges, [ rewritten, compact; compact, candidate ])

(* Linear arithmetic combinations of bitwise functions admit a conjunction
   basis over their atoms. Nonlinear/mixed-width subtrees are opaque atoms,
   never evaluated as independent bits inside an unsupported operation. *)
type form =
  | Number of Z.t
  | Atom of int
  | Add of form * form
  | Sub of form * form
  | Scale of Z.t * form
  | Not of form
  | And of form * form
  | Or of form * form
  | Xor of form * form

exception Too_complex

let linear_candidates cost expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let mask = Z.pred modulus in
  let normalize value = Z.logand value mask in
  let atoms = ref [] in
  let visited = ref 0 in
  let tick () =
    incr visited;
    let visit_limit = max 512 (8 * (1 lsl min 10 !c_normalization_max_atoms)) in
    if !visited > visit_limit then raise Too_complex;
    if !visited mod 32 = 0 then check_timeout ()
  in
  let atom expression =
    if E.sizeof expression <> width then raise Too_complex;
    let expression, complemented = canonical_bitwise_atom expression in
    let rec lookup index = function
      | [] ->
          if index >= !c_normalization_max_atoms then raise Too_complex;
          atoms := !atoms @ [ expression ];
          Atom index
      | previous :: rest ->
          if E.is_equal previous expression then Atom index
          else lookup (index + 1) rest
    in
    let result = lookup 0 !atoms in
    if complemented then Not result else result
  in
  let rec linear expression =
    tick ();
    match expression with
    | E.Cst value -> Number (Bitvector.value_of value)
    | E.Unary { f = E.Minus; x; _ } -> Scale (mask, linear x)
    | E.Unary { f = E.Not; x; _ } -> Not (linear x)
    | E.Binary { f = E.Plus; x; y; _ } -> Add (linear x, linear y)
    | E.Binary { f = E.Minus; x; y; _ } -> Sub (linear x, linear y)
    | E.Binary { f = E.Mul; x; y; _ } -> (
        match constant_value x, constant_value y with
        | Some k, _ -> Scale (Bitvector.value_of k, linear y)
        | _, Some k -> Scale (Bitvector.value_of k, linear x)
        | _ -> atom expression)
    | E.Binary { f = E.Lsl; x; y; _ } -> (
        match constant_value y with
        | Some count ->
            let count = bounded_count width count in
            if count >= width then Number Z.zero
            else Scale (Z.shift_left Z.one count, linear x)
        | None -> atom expression)
    | _ -> boolean expression
  and boolean expression =
    tick ();
    match expression with
    | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value ->
        Number (Bitvector.value_of value)
    | E.Unary { f = E.Not; x; _ } -> Not (boolean x)
    | E.Binary { f = E.And; x; y; _ } -> And (boolean x, boolean y)
    | E.Binary { f = E.Or; x; y; _ } -> Or (boolean x, boolean y)
    | E.Binary { f = E.Xor; x; y; _ } -> Xor (boolean x, boolean y)
    | _ -> atom expression
  in
  try
    let source = linear expression in
    let atoms = Array.of_list !atoms in
    let count = Array.length atoms in
    let rec evaluate assignment = function
      | Number n -> normalize n
      | Atom index -> if assignment land (1 lsl index) = 0 then Z.zero else Z.one
      | Add (x, y) -> normalize (Z.add (evaluate assignment x) (evaluate assignment y))
      | Sub (x, y) -> normalize (Z.sub (evaluate assignment x) (evaluate assignment y))
      | Scale (k, x) -> normalize (Z.mul k (evaluate assignment x))
      | Not x -> Z.logxor mask (evaluate assignment x)
      | And (x, y) -> Z.logand (evaluate assignment x) (evaluate assignment y)
      | Or (x, y) -> Z.logor (evaluate assignment x) (evaluate assignment y)
      | Xor (x, y) -> Z.logxor (evaluate assignment x) (evaluate assignment y)
    in
    let table form = Array.init (1 lsl count) (fun input -> evaluate input form) in
    let target = table source in
    let results = ref [] in
    let offer candidate =
      if cost candidate < cost expression then results := candidate :: !results
    in
    let scale coefficient value =
      if Z.equal coefficient Z.zero then zeros width
      else if Z.equal coefficient Z.one then value
      else if Z.equal coefficient mask then E.unary E.Minus value
      else E.binary E.Mul value (constant width coefficient)
    in
    let combine op identity terms =
      match terms with [] -> identity | terms -> build_balanced op terms
    in
    let boolean_candidates truth =
      let assignments = Array.length target in
      let literal assignment index =
        if assignment land (1 lsl index) = 0 then E.unary E.Not atoms.(index)
        else atoms.(index)
      in
      let minterms =
        List.init assignments Fun.id
        |> List.filter (fun assignment -> truth.(assignment))
        |> List.map (fun assignment ->
               List.init count (literal assignment)
               |> combine E.And (constant width mask))
      in
      let clauses =
        List.init assignments Fun.id
        |> List.filter (fun assignment -> not truth.(assignment))
        |> List.map (fun assignment ->
               List.init count (fun index ->
                   if assignment land (1 lsl index) = 0 then atoms.(index)
                   else E.unary E.Not atoms.(index))
               |> combine E.Or (zeros width))
      in
      let coefficients = Array.copy truth in
      for bit = 0 to count - 1 do
        for subset = 0 to assignments - 1 do
          if subset land (1 lsl bit) <> 0 then
            coefficients.(subset) <-
              coefficients.(subset) <> coefficients.(subset lxor (1 lsl bit))
        done
      done;
      let anf =
        List.init assignments Fun.id
        |> List.filter (fun subset -> coefficients.(subset))
        |> List.map (fun subset ->
               if subset = 0 then constant width mask
               else
                 List.init count Fun.id
                 |> List.filter (fun index -> subset land (1 lsl index) <> 0)
                 |> List.map (Array.get atoms)
                 |> combine E.And (constant width mask))
        |> combine E.Xor (zeros width)
      in
      [ combine E.Or (zeros width) minterms;
        combine E.And (constant width mask) clauses;
        anf ]
      |> List.sort_uniq E.compare
    in
    let distinct =
      Array.to_list target |> List.sort_uniq Z.compare
    in
    (match distinct with
    | [ low; high ] when count <= min 6 !c_normalization_max_atoms ->
        let truth = Array.map (Z.equal high) target in
        List.iter
          (fun boolean ->
            let coefficient = normalize (Z.sub high low) in
            let weighted = scale coefficient boolean in
            let candidate =
              if Z.equal low Z.zero then weighted
              else E.binary E.Plus (constant width low) weighted
            in
            offer candidate)
          (boolean_candidates truth)
    | _ -> ());
    let affine candidate form =
      check_timeout ();
      let values = table form in
      let difference index = normalize (Z.sub values.(index) values.(0)) in
      let pivot = ref None in
      for index = 1 to Array.length values - 1 do
        if !pivot = None && Z.testbit (difference index) 0 then pivot := Some index
      done;
      match !pivot with
      | None -> ()
      | Some index ->
          let coefficient = normalize
              (Z.mul (Z.sub target.(index) target.(0))
                 (Z.invert (difference index) modulus)) in
          let offset = normalize (Z.sub target.(0) (Z.mul coefficient values.(0))) in
          if Array.for_all Fun.id (Array.mapi (fun i value ->
              Z.equal target.(i) (normalize (Z.add offset (Z.mul coefficient value)))) values)
          then
            let result = scale coefficient candidate in
            offer (if Z.equal offset Z.zero then result
                   else E.binary E.Plus result (constant width offset))
    in
    Array.iteri (fun index value ->
        affine value (Atom index);
        affine (E.unary E.Not value) (Not (Atom index));
        affine (E.unary E.Minus value) (Scale (mask, Atom index))) atoms;
    for i = 0 to count - 1 do
      for j = i + 1 to count - 1 do
        let a = atoms.(i) and b = atoms.(j) in
        let x = Atom i and y = Atom j in
        List.iter (fun (op, form) -> affine (E.binary op a b) form)
          [ E.Plus, Add (x, y); E.And, And (x, y);
            E.Or, Or (x, y); E.Xor, Xor (x, y);
            E.Minus, Sub (x, y) ];
        affine (E.binary E.Minus b a) (Sub (y, x))
      done
    done;
    (* Möbius inversion obtains coefficients of the AND-monomial basis. *)
    let coefficients = Array.copy target in
    for bit = 0 to count - 1 do
      for subset = 0 to Array.length coefficients - 1 do
        if subset land (1 lsl bit) <> 0 then
          coefficients.(subset) <- normalize
              (Z.sub coefficients.(subset) coefficients.(subset lxor (1 lsl bit)))
      done
    done;
    let result = ref
        (if Z.equal coefficients.(0) Z.zero then None
         else Some (constant width coefficients.(0))) in
    for subset = 1 to Array.length coefficients - 1 do
      let coefficient = coefficients.(subset) in
      if not (Z.equal coefficient Z.zero) then (
        let term = ref None in
        Array.iteri (fun index atom ->
            if subset land (1 lsl index) <> 0 then
              term := Some (match !term with None -> atom | Some old -> E.binary E.And old atom)) atoms;
        let term = Option.get !term in
        result := Some (match !result with
          | None -> scale coefficient term
          | Some old when Z.equal coefficient mask -> E.binary E.Minus old term
          | Some old -> E.binary E.Plus old (scale coefficient term)))
    done;
    offer (Option.value !result ~default:(zeros width));
    !results
  with Too_complex -> []

(* A first proof-decomposed polynomial identity. The direct 64-bit obligation
   routinely times out because it contains multiplication. The local Boolean
   partitions and distributive ring steps below each prove quickly, while the
   certificate checker derives the endpoints through congruence/transitivity. *)
module RingMonomial = struct
  type t = E.t list
  let compare = List.compare E.compare
end

module RingPolynomial = Map.Make (RingMonomial)

exception Ring_candidate_too_complex

let ring_polynomial_candidate cost expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let normalize value =
    let value = Z.erem value modulus in
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let operations = ref 0 in
  let add_term monomial coefficient polynomial =
    incr operations;
    if !operations > 50_000 || List.length monomial > 8 then
      raise Ring_candidate_too_complex;
    let old = Option.value (RingPolynomial.find_opt monomial polynomial) ~default:Z.zero in
    let value = normalize (Z.add old coefficient) in
    let result =
      if Z.equal value Z.zero then RingPolynomial.remove monomial polynomial
      else RingPolynomial.add monomial value polynomial
    in
    if RingPolynomial.cardinal result > 256 then raise Ring_candidate_too_complex;
    result
  in
  let add left right = RingPolynomial.fold add_term left right in
  let neg polynomial =
    RingPolynomial.fold
      (fun monomial coefficient result -> add_term monomial (Z.neg coefficient) result)
      polynomial RingPolynomial.empty
  in
  let mul left right =
    RingPolynomial.fold
      (fun left_monomial left_coefficient result ->
        RingPolynomial.fold
          (fun right_monomial right_coefficient result ->
            add_term
              (List.sort E.compare (left_monomial @ right_monomial))
              (Z.mul left_coefficient right_coefficient) result)
          right result)
      left RingPolynomial.empty
  in
  let saw_ring = ref false in
  let memo = Nodes.create 128 in
  let rec parse expression =
    match Nodes.find_opt memo expression with
    | Some polynomial -> polynomial
    | None ->
      let polynomial = match expression with
    | E.Cst value ->
        add_term [] (Bitvector.value_of value) RingPolynomial.empty
    | E.Unary { f = E.Minus; x; _ } -> saw_ring := true; neg (parse x)
    | E.Binary { f = E.Plus; x; y; _ } -> saw_ring := true; add (parse x) (parse y)
    | E.Binary { f = E.Minus; x; y; _ } ->
        saw_ring := true; add (parse x) (neg (parse y))
    | E.Binary { f = E.Mul; x; y; _ } -> saw_ring := true; mul (parse x) (parse y)
    | opaque -> add_term [ opaque ] Z.one RingPolynomial.empty
      in
      Nodes.add memo expression polynomial;
      polynomial
  in
  try
    let polynomial = parse expression in
    if not !saw_ring then None
    else
      let positive = ref [] and negative = ref [] in
      let half = Z.shift_left Z.one (width - 1) in
      let monomial_expression = function
        | [] -> None
        | head :: tail -> Some (List.fold_left (E.binary E.Mul) head tail)
      in
      RingPolynomial.iter
        (fun monomial coefficient ->
          let is_negative = Z.geq coefficient half in
          let magnitude = if is_negative then Z.sub modulus coefficient else coefficient in
          let term =
            match monomial_expression monomial with
            | None -> constant width magnitude
            | Some monomial when Z.equal magnitude Z.one -> monomial
            | Some monomial -> E.binary E.Mul (constant width magnitude) monomial
          in
          if is_negative then negative := term :: !negative
          else positive := term :: !positive)
        polynomial;
      let sum terms =
        match List.sort E.compare terms with
        | [] -> None
        | head :: tail -> Some (List.fold_left (E.binary E.Plus) head tail)
      in
      let candidate =
        match sum !positive, sum !negative with
        | None, None -> zeros width
        | Some value, None -> value
        | None, Some value -> E.unary E.Minus value
        | Some positive, Some negative -> E.binary E.Minus positive negative
      in
      if cost candidate < cost expression then Some candidate else None
  with Ring_candidate_too_complex -> None

let minterm_polynomial_candidate cost expression =
  Option.bind (minterm_ring_expansion expression expression)
    (fun (equalities, ring_equalities, expanded, _) ->
      Option.bind (ring_polynomial_candidate cost expanded) (fun candidate ->
          if cost candidate >= cost expression then None
          else Some (candidate, equalities, (expanded, candidate) :: ring_equalities)))

let factor_group_candidate cost expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let normalize value =
    let value = Z.erem value modulus in
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let rec additive coefficient = function
    | E.Binary { f = E.Plus; x; y; _ } -> additive coefficient x @ additive coefficient y
    | E.Binary { f = E.Minus; x; y; _ } ->
        additive coefficient x @ additive (Z.neg coefficient) y
    | E.Unary { f = E.Minus; x; _ } -> additive (Z.neg coefficient) x
    | term -> [ normalize coefficient, term ]
  in
  let rec factors coefficient = function
    | E.Cst value -> (normalize (Z.mul coefficient (Bitvector.value_of value)), [])
    | E.Unary { f = E.Minus; x; _ } -> factors (Z.neg coefficient) x
    | E.Binary { f = E.Mul; x; y; _ } ->
        let left_coefficient, left = factors coefficient x in
        let right_coefficient, right = factors Z.one y in
        (normalize (Z.mul left_coefficient right_coefficient), left @ right)
    | factor -> (normalize coefficient, [ factor ])
  in
  let terms =
    additive Z.one expression
    |> List.map (fun (coefficient, term) ->
           let coefficient, factors = factors coefficient term in
           (coefficient, List.sort E.compare factors))
  in
  let frequencies = Sexpr.BvTbl.create 32 in
  List.iter
    (fun (_, factors) ->
      List.sort_uniq E.compare factors
      |> List.iter (fun factor ->
             let count = Option.value (Sexpr.BvTbl.find_opt frequencies factor) ~default:0 in
             Sexpr.BvTbl.replace frequencies factor (count + 1)))
    terms;
  let selected =
    Sexpr.BvTbl.fold
      (fun factor frequency result ->
        if frequency < 2 then result else (factor, frequency) :: result)
      frequencies []
    |> List.sort (fun (left, left_frequency) (right, right_frequency) ->
           let order = Int.compare right_frequency left_frequency in
           if order = 0 then E.compare left right else order)
    |> (fun factors ->
         let rec take count = function
           | _ when count = 0 -> []
           | [] -> []
           | head :: tail -> head :: take (count - 1) tail
         in
         take 6 factors)
  in
  List.find_map (fun (factor, _) ->
      let remove_factor factors =
        let rec remove prefix = function
          | [] -> None
          | head :: tail when E.is_equal head factor -> Some (List.rev_append prefix tail)
          | head :: tail -> remove (head :: prefix) tail
        in
        remove [] factors
      in
      let grouped, remainder =
        List.fold_left
          (fun (grouped, remainder) (coefficient, factors) ->
            match remove_factor factors with
            | Some cofactor -> ((coefficient, cofactor) :: grouped, remainder)
            | None -> (grouped, (coefficient, factors) :: remainder))
          ([], []) terms
      in
      let term_expression (coefficient, factors) =
        let product =
          match factors with
          | [] -> None
          | head :: tail -> Some (List.fold_left (E.binary E.Mul) head tail)
        in
        match product with
        | None -> constant width coefficient
        | Some product when Z.equal coefficient Z.one -> product
        | Some product -> E.binary E.Mul (constant width coefficient) product
      in
      let sum terms =
        match List.map term_expression (List.rev terms) with
        | [] -> zeros width
        | head :: tail -> List.fold_left (E.binary E.Plus) head tail
      in
      let cofactor = sum grouped in
      let remainder_expression = sum remainder in
      let candidates =
        let variables =
          Sample_evaluator.variables_of_expr cofactor
          |> List.map (fun (name, size) -> E.var name size name)
        in
        let ring = Option.to_list (ring_polynomial_candidate cost cofactor) in
        variables @ ring @ linear_candidates cost cofactor
        |> List.filter (fun candidate -> cost candidate < cost cofactor)
        |> List.sort_uniq (fun left right ->
               let order = Int.compare (cost left) (cost right) in
               if order = 0 then E.compare left right else order)
      in
      let simplification =
        List.find_map
          (fun candidate ->
            if not (Rewrite.samples_agree cofactor candidate) then None
            else
              Option.map (fun proof -> (candidate, proof))
                (minterm_ring_proof cofactor candidate))
          candidates
      in
      Option.bind simplification (fun (simplified, (equalities, cofactor_ring)) ->
          let factored = E.binary E.Mul factor cofactor in
          let raw_simplified = E.binary E.Mul factor simplified in
          let simplified_factored =
            if is_number Z.zero simplified then zeros width
            else if is_number Z.one simplified then factor
            else if is_number (Z.pred modulus) simplified then E.unary E.Minus factor
            else raw_simplified
          in
          let raw =
            if is_number Z.zero remainder_expression then factored
            else E.binary E.Plus factored remainder_expression
          in
          let candidate =
            if is_number Z.zero simplified_factored then remainder_expression
            else if is_number Z.zero remainder_expression then simplified_factored
            else E.binary E.Plus simplified_factored remainder_expression
          in
          if cost candidate >= cost expression then None
          else
            let post =
              if is_number Z.zero remainder_expression then raw_simplified
              else E.binary E.Plus raw_simplified remainder_expression
            in
            let cleanup =
              (if E.is_equal raw_simplified simplified_factored then cofactor_ring
               else (raw_simplified, simplified_factored) :: cofactor_ring)
              |> fun edges ->
              if E.is_equal post candidate then edges else (post, candidate) :: edges
            in
            Some (candidate, equalities, (expression, raw) :: cleanup)))
    selected

let rec product_partition_candidate expression =
  let same = E.is_equal in
  let commutative_operator = function
    | E.Plus | E.Mul | E.And | E.Or | E.Xor -> true
    | _ -> false
  in
  let rec canonical = function
    | E.Unary { f; x; _ } -> E.unary f (canonical x)
    | E.Binary { f; x; y; _ } ->
        let x = canonical x and y = canonical y in
        if commutative_operator f && E.compare x y > 0 then E.binary f y x
        else E.binary f x y
    | E.Ite { c; t; e; _ } -> E.ite (canonical c) (canonical t) (canonical e)
    | expression -> expression
  in
  let canonical_expression = canonical expression in
  let commutative op left right = function
    | E.Binary { f; x; y; _ } when f = op ->
        (same x left && same y right) || (same x right && same y left)
    | _ -> false
  in
  let product left right = commutative E.Mul left right in
  let union left right = commutative E.Or left right in
  let cbin op left right =
    if commutative_operator op && E.compare left right > 0 then E.binary op right left
    else E.binary op left right
  in
  let try_order source first second =
    match first with
    | E.Binary { f = E.Mul; x = factor; y = other; _ } ->
        let try_factors m1 union_term =
          match m1 with
          | E.Binary { f = E.And; x; y; _ } when union x y union_term ->
              let m2 = cbin E.And x (E.unary E.Not y) in
              let m3 = cbin E.And (E.unary E.Not x) y in
              if not (product m2 m3 second) then None
              else
                let add = E.binary E.Plus and mul = E.binary E.Mul in
                let ordered_source = add first second in
                let ordered_first = mul m1 union_term in
                let ordered_second = mul m2 m3 in
                let candidate = mul x y in
                let x_parts = add m1 m2 and y_parts = add m1 m3 in
                let all_parts = add (add m1 m2) m3 in
                let left0 = mul m1 all_parts in
                let left1 = add (mul m1 (add m1 m2)) (mul m1 m3) in
                let left2 = add (add (mul m1 m1) (mul m1 m2)) (mul m1 m3) in
                let expanded_left = add left2 (mul m2 m3) in
                let right0 = mul x_parts y_parts in
                let right1 = add (mul x_parts m1) (mul x_parts m3) in
                let expanded_right =
                  add (add (mul m1 m1) (mul m1 m2))
                    (add (mul m1 m3) (mul m2 m3))
                in
                Some
                  (candidate,
                   [ expression, canonical_expression;
                     source, ordered_source;
                     first, ordered_first;
                     second, ordered_second;
                     x, x_parts; y, y_parts; union_term, all_parts;
                     left0, left1; mul m1 (add m1 m2), add (mul m1 m1) (mul m1 m2);
                     right0, right1; mul x_parts m1, add (mul m1 m1) (mul m2 m1);
                     mul x_parts m3, add (mul m1 m3) (mul m2 m3);
                     mul m2 m1, mul m1 m2;
                     expanded_left, expanded_right ])
          | _ -> None
        in
        (match try_factors factor other with
        | Some result -> Some result
        | None -> try_factors other factor)
    | _ -> None
  in
  let scaled = function
    | E.Binary { f = E.Mul; x = E.Cst coefficient; y; _ }
    | E.Binary { f = E.Mul; x = y; y = E.Cst coefficient; _ } ->
        Some (coefficient, y)
    | _ -> None
  in
  match canonical_expression with
  | E.Binary { f = E.Plus; x; y; _ } ->
      (match try_order canonical_expression x y with
      | Some result -> Some result
      | None ->
          (match try_order canonical_expression y x with
          | Some result -> Some result
          | None ->
              match scaled x, scaled y with
              | Some (left_coefficient, left), Some (right_coefficient, right)
                when Bitvector.equal left_coefficient right_coefficient ->
                  let inner = E.binary E.Plus left right in
                  Option.map
                    (fun (candidate, equalities) ->
                      let factor = E.constant left_coefficient in
                      let factored = E.binary E.Mul factor inner in
                      let result = E.binary E.Mul factor candidate in
                      (result,
                       (expression, canonical_expression)
                       :: (canonical_expression, factored) :: equalities))
                    (product_partition_candidate inner)
              | _ -> None))
  | _ -> None

let bitsliced_candidate cost expression =
  let width = E.sizeof expression in
  let variables = Sample_evaluator.variables_of_expr expression in
  let rec has_nontrivial_mask = function
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
        let here =
          match constant_value x, constant_value y with
          | Some value, _ | _, Some value ->
              not (Bitvector.is_zeros value || Bitvector.is_fill value)
          | _ -> false
        in
        here || has_nontrivial_mask x || has_nontrivial_mask y
    | E.Unary { x; _ } -> has_nontrivial_mask x
    | E.Binary { x; y; _ } -> has_nontrivial_mask x || has_nontrivial_mask y
    | E.Ite { c; t; e; _ } ->
        has_nontrivial_mask c || has_nontrivial_mask t || has_nontrivial_mask e
    | _ -> false
  in
  match variables with
  | [ name, variable_width ]
    when variable_width = width && width <= 128 && has_nontrivial_mask expression ->
      let variable = E.var name width name in
      let evaluate value =
        let bindings = Hashtbl.create 1 in
        Hashtbl.add bindings variable (Bitvector.create value width);
        Sample_evaluator.eval_with_bindings bindings expression
      in
      (try
         let modulus = Z.shift_left Z.one width in
         let normalize value =
           let value = Z.erem value modulus in
           if Z.sign value < 0 then Z.add value modulus else value
         in
         let eval_candidate candidate value =
           let bindings = Hashtbl.create 1 in
           Hashtbl.add bindings variable (Bitvector.create value width);
           Sample_evaluator.eval_with_bindings bindings candidate
         in
         let test_inputs =
           Z.zero :: Z.pred modulus
           :: List.init width (fun bit -> Z.shift_left Z.one bit)
         in
         let agrees candidate =
           List.for_all
             (fun input -> Bitvector.equal (evaluate input) (eval_candidate candidate input))
             test_inputs
         in
         let base = evaluate Z.zero in
         let mask = ref Z.zero and valid = ref true in
         for bit = 0 to width - 1 do
           let input = Z.shift_left Z.one bit in
           let difference =
             Bitvector.logxor (evaluate input) base |> Bitvector.value_of
           in
           if Z.equal difference Z.zero then ()
           else if Z.equal difference input then mask := Z.logor !mask input
           else valid := false
         done;
         let candidates = ref [] in
         if !valid then (
           let masked =
             let full = Z.pred modulus in
             if Z.equal !mask full then variable
             else E.binary E.And variable (constant width !mask)
           in
           let candidate =
             if Bitvector.is_zeros base then masked
             else E.binary E.Xor masked (E.constant base)
           in
           candidates := candidate :: !candidates);
         let bitwise_constants = ref [] in
         let rec collect = function
           | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
               (match constant_value x, constant_value y with
               | Some value, _ -> bitwise_constants := value :: !bitwise_constants
               | _, Some value -> bitwise_constants := value :: !bitwise_constants
               | _ -> ());
               collect x; collect y
           | E.Unary { x; _ } -> collect x
           | E.Binary { x; y; _ } -> collect x; collect y
           | E.Ite { c; t; e; _ } -> collect c; collect t; collect e
           | _ -> ()
         in
         collect expression;
         List.sort_uniq Bitvector.compare !bitwise_constants
         |> List.iter (fun xor_constant ->
                let constant_value = Bitvector.value_of xor_constant in
                let toggled = Z.logxor constant_value Z.one |> normalize in
                let delta = normalize (Z.sub toggled constant_value) in
                if Z.testbit delta 0 then (
                  let output_delta =
                    normalize
                      (Z.sub (Bitvector.value_of (evaluate Z.one))
                         (Bitvector.value_of base))
                  in
                  let coefficient = normalize (Z.mul output_delta (Z.invert delta modulus)) in
                  let offset =
                    normalize
                      (Z.sub (Bitvector.value_of base)
                         (Z.mul coefficient constant_value))
                  in
                  let xor = E.binary E.Xor variable (E.constant xor_constant) in
                  let scaled =
                    if Z.equal coefficient Z.one then xor
                    else E.binary E.Mul (constant width coefficient) xor
                  in
                  let candidate =
                    if Z.equal offset Z.zero then scaled
                    else E.binary E.Plus scaled (constant width offset)
                  in
                  candidates := candidate :: !candidates));
         !candidates
         |> List.filter (fun candidate -> cost candidate < cost expression && agrees candidate)
         |> List.sort (fun left right -> Int.compare (cost left) (cost right))
         |> function head :: _ -> Some head | [] -> None
       with _ -> None)
  | _ -> None

let oracle_compatible expression =
  let width = E.sizeof expression in
  let rec inspect = function
    | E.Var variable -> variable.size = width
    | E.Cst value -> Bitvector.size_of value = width
    | E.Unary { f = (E.Not | E.Minus); x; _ } -> inspect x
    | E.Binary { f = (E.Plus | E.Minus | E.Mul | E.And | E.Or | E.Xor);
                 x; y; _ } -> inspect x && inspect y
    | E.Binary { f = E.Lsl; x; y = (E.Cst _ as y); _ } -> inspect x && inspect y
    | _ -> false
  in
  inspect expression

let oracle_candidate expression =
  if !c_mba_oracle = "none" then None
  else
    let width = E.sizeof expression in
    let variables = Hashtbl.create 16 in
    let rec inspect = function
      | E.Var variable when variable.size = width ->
          Hashtbl.replace variables (variable.name, variable.size) (); true
      | E.Cst value -> Bitvector.size_of value = width
      | E.Unary { f = (E.Not | E.Minus); x; _ } -> inspect x
      | E.Binary { f = (E.Plus | E.Minus | E.Mul | E.And | E.Or | E.Xor);
                   x; y; _ } -> inspect x && inspect y
      | E.Binary { f = E.Lsl; x; y = (E.Cst _ as y); _ } -> inspect x && inspect y
      | _ -> false
    in
    if not (inspect expression) then None
    else
      let variables =
        Hashtbl.fold (fun variable () result -> variable :: result) variables []
        |> List.sort Stdlib.compare |> Array.of_list
      in
      let positions = Hashtbl.create (Array.length variables) in
      Array.iteri (fun index variable -> Hashtbl.add positions variable index) variables;
      let rec rename = function
        | E.Var variable ->
            let index = Hashtbl.find positions (variable.name, variable.size) in
            E.var (Printf.sprintf "v%d" index) variable.size
              (Printf.sprintf "v%d" index)
        | E.Unary { f; x; _ } -> E.unary f (rename x)
        | E.Binary { f; x; y; _ } -> E.binary f (rename x) (rename y)
        | node -> node
      in
      let rendered = Greysynth_utils.Utils.pp ~show_size:false (rename expression) in
      let command =
        match !c_mba_oracle with
        | "rumba" ->
            Printf.sprintf "%s --n %d %s" !c_mba_oracle_command width
              (Filename.quote rendered)
        | "cobra" ->
            Printf.sprintf "%s --mba %s --bitwidth %d" !c_mba_oracle_command
              (Filename.quote rendered) width
        | _ -> assert false
      in
      try
        let timeout =
          if !g_total_timeout <= 0. then !c_mba_oracle_timeout
          else
            let remaining =
              !g_total_timeout -. (Unix.gettimeofday () -. !g_start_time)
              |> floor |> int_of_float
            in
            if remaining <= 0 then raise Timeout_exception;
            min !c_mba_oracle_timeout remaining
        in
        let output =
          Synth_backends.run_command ~timeout command
          |> String.split_on_char '\n'
          |> List.filter (fun line -> String.trim line <> "")
          |> List.rev
        in
        let rec restore = function
              | E.Var variable when String.length variable.name >= 2
                                  && variable.name.[0] = 'v' ->
                  let index =
                    int_of_string
                      (String.sub variable.name 1 (String.length variable.name - 1))
                  in
                  let name, size = variables.(index) in
                  if variable.size <> size then failwith "MBA oracle changed variable width";
                  E.var name size name
              | E.Var _ -> failwith "MBA oracle returned an unknown variable"
              | E.Unary { f; x; _ } -> E.unary f (restore x)
              | E.Binary { f; x; y; _ } -> E.binary f (restore x) (restore y)
              | E.Ite _ | E.Load _ -> failwith "MBA oracle returned an unsupported node"
              | node -> node
            in
        let rec parse = function
          | [] -> None
          | answer :: rest ->
              (try
                 let parsed =
                   String_to_sexpr.parse ~default_size:width (String.trim answer)
                 in
                 let candidate = restore parsed in
                 if E.sizeof candidate = width then Some candidate else parse rest
               with _ -> parse rest)
        in
        parse output
      with
      | Config.Timeout_exception -> raise Config.Timeout_exception
      | exn ->
          Logging._log_warn "mba-oracle" "%s" (Printexc.to_string exn);
          None

let run expression =
  let results = Nodes.create 128 in
  let sizes = Nodes.create 128 in
  let constants = Sample_evaluator.make 1 in
  let oracle_calls = ref 0 in
  let rec cost expression =
    match Nodes.find_opt sizes expression with
    | Some value -> value
    | None ->
        let open Greysynth_utils.Utils in
        let value =
          match expression with
          | E.Unary { f; x; _ } -> unary_cost !cost_model f + cost x
          | E.Binary { f; x; y; _ } -> binary_cost !cost_model f + cost x + cost y
          | E.Ite { c; t; e; _ } ->
              conditional_cost !cost_model + cost c + cost t + cost e
          | _ -> 1
        in
        Nodes.add sizes expression value;
        value
  in
  let try_oracle current =
    if !oracle_calls >= !c_mba_oracle_calls || cost current < 11
       || !c_mba_oracle = "none" || not (oracle_compatible current)
    then None
    else (
      incr oracle_calls;
      match oracle_candidate current with
      | Some candidate when cost candidate < cost current ->
          let accepted =
            if not (Rewrite.samples_agree current candidate) then
              Rewrite.accepts ~pass:"mba-oracle" current candidate
            else
              match minterm_ring_proof current candidate with
              | Some (equalities, ring_equalities) ->
                  Rewrite.accepts_compositional ~pass:"mba-oracle-ring"
                    ~equalities ~ring_equalities current candidate
              | None -> Rewrite.accepts ~pass:"mba-oracle" current candidate
          in
          if accepted then Some candidate else None
      | _ -> None)
  in
  let rec oracle_visit node =
    if !g_has_timedout then node
    else (
      check_timeout ();
      if oracle_compatible node && cost node >= 11 then
        Option.value (try_oracle node) ~default:node
      else
        match node with
        | E.Unary { f; x; _ } -> E.unary f (oracle_visit x)
        | E.Binary { f; x; y; _ } ->
            E.binary f (oracle_visit x) (oracle_visit y)
        | E.Ite { c; t; e; _ } ->
            E.ite (oracle_visit c) (oracle_visit t) (oracle_visit e)
        | _ -> node)
  in
  let rec visit ?(allow_oracle = true) original =
    if !g_has_timedout then original
    else match Nodes.find_opt results original with
    | Some result -> result
    | None ->
        let current = ref original in
        (try
           check_timeout ();
           let accept_minterm pass candidate =
             if not (Rewrite.samples_agree original candidate) then false
             else
               match minterm_ring_proof original candidate with
               | Some (equalities, ring_equalities) ->
                   Rewrite.accepts_compositional ~pass
                     ~equalities ~ring_equalities original candidate
               | None -> Rewrite.accepts ~pass original candidate
           in
           let early_minterm =
             if cost original < 11 then None
             else
               Sample_evaluator.variables_of_expr original
               |> List.map (fun (name, width) -> E.var name width name)
               |> List.filter (fun candidate -> cost candidate < cost original)
               |> List.find_opt (accept_minterm "minterm-ring-mba")
           in
           (match early_minterm with
           | Some candidate -> current := visit candidate
           | None ->
               current := (match original with
                 | E.Unary { f; x; _ } -> E.unary f (visit ~allow_oracle x)
                 | E.Binary { f; x; y; _ } ->
                     let x = visit ~allow_oracle x in
                     let y = visit ~allow_oracle y in
                     E.binary f x y
                 | E.Ite { c; t; e; _ } ->
                     let c = visit ~allow_oracle c in
                     let t = visit ~allow_oracle t in
                     let e = visit ~allow_oracle e in
                     E.ite c t e
                 | _ -> original));
           if Option.is_none early_minterm && not !g_has_timedout then (
             let oracle = if allow_oracle then try_oracle !current else None in
             match oracle with
             | Some candidate -> current := candidate; current := visit ~allow_oracle:false candidate
             | None ->
             let bitsliced =
               match if cost original >= 11 then bitsliced_candidate cost original else None with
               | Some candidate when cost candidate < cost !current
                                     && Rewrite.samples_agree original candidate ->
                   (match minterm_ring_proof original candidate with
                   | Some (equalities, ring_equalities)
                     when Rewrite.accepts_compositional ~pass:"bitsliced"
                            ~equalities ~ring_equalities original candidate ->
                       Some candidate
                   | _ ->
                       if Rewrite.accepts ~pass:"bitsliced" original candidate
                       then Some candidate else None)
               | _ -> None
             in
             let minterm_polynomial =
               match bitsliced with
               | Some candidate -> Some (candidate, [], [])
               | None when cost !current < 11 -> None
               | None ->
                   (match minterm_polynomial_candidate cost !current with
                   | Some (candidate, equalities, ring_equalities)
                     when Rewrite.samples_agree !current candidate
                          && Rewrite.accepts_compositional ~pass:"minterm-polynomial"
                               ~equalities ~ring_equalities !current candidate ->
                       Some (candidate, equalities, ring_equalities)
                   | _ -> None)
             in
             let factor_grouped =
               match minterm_polynomial with
               | Some (candidate, _, _) -> Some candidate
               | None when cost !current < 11 -> None
               | None ->
                   (match factor_group_candidate cost !current with
                   | Some (candidate, equalities, ring_equalities)
                     when Rewrite.accepts_compositional ~pass:"factor-group"
                            ~equalities ~ring_equalities !current candidate ->
                       Some candidate
                   | _ -> None)
             in
             let ring_normalized =
               match factor_grouped with
               | Some candidate -> Some candidate
               | None when cost !current < 5 -> None
               | None ->
                   (match ring_polynomial_candidate cost !current with
                   | Some candidate
                     when Rewrite.samples_agree !current candidate
                          && Rewrite.accepts_compositional ~pass:"ring-polynomial"
                               ~equalities:[] ~ring_equalities:[ !current, candidate ]
                               !current candidate -> Some candidate
                   | _ -> None)
             in
             let decomposed =
               match ring_normalized with
               | Some candidate -> Some candidate
               | None ->
                   (match product_partition_candidate !current with
                   | Some (candidate, equalities)
                     when cost candidate < cost !current
                          && Rewrite.accepts_compositional ~pass:"polynomial"
                               ~equalities !current candidate ->
                       Some candidate
                   | _ -> None)
             in
             match decomposed with
             | Some candidate ->
                 current := candidate;
                 current := visit ~allow_oracle candidate
             | None ->
                 let candidates = peepholes constants.eval !current
                     @ (if !c_ac_normalization then canonical_candidates !current else [])
                     @ (if cost !current >= 4 then linear_candidates cost !current else []) in
                 let candidates = List.filter (fun candidate -> cost candidate < cost !current) candidates in
                 let candidates = List.sort_uniq (fun a b ->
                     let order = Int.compare (cost a) (cost b) in
                     if order = 0 then E.compare a b else order) candidates in
                 let accepts candidate =
                   let fallback () =
                     match complement_product_steps !current candidate with
                     | Some (equalities, ring_equalities) ->
                         if Rewrite.accepts_compositional ~pass:"linear-mba"
                              ~equalities ~ring_equalities !current candidate
                         then true
                         else Rewrite.accepts ~pass:"normalize" !current candidate
                     | None -> Rewrite.accepts ~pass:"normalize" !current candidate
                   in
                   if not (Rewrite.samples_agree !current candidate) then
                     Rewrite.accepts ~pass:"normalize" !current candidate
                   else
                     match minterm_ring_proof !current candidate with
                     | Some (equalities, ring_equalities) ->
                         if Rewrite.accepts_compositional ~pass:"minterm-ring-mba"
                              ~equalities ~ring_equalities !current candidate
                         then true else fallback ()
                     | None -> fallback ()
                 in
                 match List.find_opt accepts candidates with
                 | Some candidate ->
                     current := candidate;
                     current := visit ~allow_oracle candidate
                 | None -> ())
         with Timeout_exception -> g_has_timedout := true);
        Nodes.replace results original !current;
        !current
  in
  let expression =
    if !c_mba_oracle = "none" || !c_mba_oracle_calls = 0 then expression
    else oracle_visit expression
  in
  let root_bitsliced =
    if cost expression > 512 then None
    else
      match bitsliced_candidate cost expression with
      | Some candidate when Rewrite.samples_agree expression candidate ->
          (match minterm_ring_proof expression candidate with
          | Some (equalities, ring_equalities)
            when Rewrite.accepts_compositional ~pass:"bitsliced-root"
                   ~equalities ~ring_equalities expression candidate ->
              Some candidate
          | _ -> None)
      | _ -> None
  in
  match root_bitsliced with
  | Some candidate -> visit ~allow_oracle:false candidate
  | None -> visit ~allow_oracle:false expression
