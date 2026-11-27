(* Compiler-style bitvector peepholes, canonical forms, and minterm proof bridges.
Every emitted rewrite remains subject to the common proof gate. *)

open Config
include Norm_common

let rec peepholes evaluate expression =
  let width = E.sizeof expression in
  let zero = zeros width and one = integer width 1 in
  let fill = constant width (Z.pred (Z.shift_left Z.one width)) in
  let same = E.is_equal in
  match expression with
  | E.Binary { f = E.Minus; x = E.Unary { f = E.Minus; x = base; _ };
               y = one; _ }
    when is_number Z.one one -> [ E.unary E.Not base ]
  | E.Binary { f = E.Minus; x = fill; y = base; _ }
    when is_number (Z.pred (Z.shift_left Z.one (E.sizeof base))) fill ->
      [ E.unary E.Not base ]
  | E.Binary { f = E.Plus; x = E.Unary { f = E.Minus; x = base; _ };
               y = fill; _ }
    when is_number (Z.pred (Z.shift_left Z.one (E.sizeof base))) fill ->
      [ E.unary E.Not base ]
  | E.Binary { f = E.Plus; x = fill;
               y = E.Unary { f = E.Minus; x = base; _ }; _ }
    when is_number (Z.pred (Z.shift_left Z.one (E.sizeof base))) fill ->
      [ E.unary E.Not base ]
  | E.Unary { f = E.Minus;
              x = E.Binary { f = E.Plus; x = base; y = one; _ }; _ }
    when is_number Z.one one -> [ E.unary E.Not base ]
  | E.Unary { f = E.Not;
              x = E.Binary { f = E.Minus; x = base; y = one; _ }; _ }
    when is_number Z.one one -> [ E.unary E.Minus base ]
  | E.Unary { f = E.Not; x = E.Unary { f = E.Minus; x = base; _ }; _ } ->
      [ E.binary E.Minus base (integer (E.sizeof base) 1) ]
  | E.Unary { f = E.Not; x = E.Binary { f = E.And; x; y; _ }; _ } ->
      let negate = function E.Unary { f = E.Not; x; _ } -> x
                          | value -> E.unary E.Not value in
      [ E.binary E.Or (negate x) (negate y) ]
  | E.Unary { f = E.Not; x = E.Binary { f = E.Or; x; y; _ }; _ } ->
      let negate = function E.Unary { f = E.Not; x; _ } -> x
                          | value -> E.unary E.Not value in
      [ E.binary E.And (negate x) (negate y) ]
  | E.Unary { f = E.Not; x = E.Unary { f = E.Not; x; _ }; _ }
  | E.Unary { f = E.Minus; x = E.Unary { f = E.Minus; x; _ }; _ } -> [ x ]
  | E.Unary { f; x; _ } -> (
      let composed =
        match f, x with
        | E.Uext outer, E.Unary { f = E.Uext inner; x = base; _ } ->
            [ E.unary (E.Uext (outer + inner)) base ]
        | E.Sext outer, E.Unary { f = E.Sext inner; x = base; _ } ->
            [ E.unary (E.Sext (outer + inner)) base ]
        | E.Restrict { lo = 0; hi },
          E.Unary { f = (E.Uext _ | E.Sext _); x = base; _ }
          when hi < E.sizeof base ->
            [ if hi = E.sizeof base - 1 then base else E.restrict ~lo:0 ~hi base ]
        | E.Restrict { lo = 0; hi },
          E.Binary { f = (E.Plus | E.Minus | E.Mul | E.And | E.Or | E.Xor as op);
                     x = E.Unary { f = (E.Uext _ | E.Sext _); x = left; _ };
                     y = E.Unary { f = (E.Uext _ | E.Sext _); x = right; _ }; _ }
          when E.sizeof left = hi + 1 && E.sizeof right = hi + 1 ->
            [ E.binary op left right ]
        | _ -> []
      in
      match constant_value x with
      | Some value -> composed @ (try [ E.constant (Term.Bv.unary f value) ] with _ -> [])
      | None -> composed)
  | E.Binary { f = E.Minus; x = E.Cst fill;
               y = E.Binary { f = E.Mul; x = E.Cst coefficient; y = body; _ }; _ }
  | E.Binary { f = E.Minus; x = E.Cst fill;
               y = E.Binary { f = E.Mul; x = body; y = E.Cst coefficient; _ }; _ }
    when Bitvector.is_fill fill ->
      [ E.unary E.Not (E.binary E.Mul (E.constant coefficient) body) ]
  | E.Binary { f = E.Plus; x = E.Cst fill;
               y = E.Binary { f = E.Mul; x = E.Cst coefficient; y = body; _ }; _ }
  | E.Binary { f = E.Plus;
               x = E.Binary { f = E.Mul; x = E.Cst coefficient; y = body; _ };
               y = E.Cst fill; _ }
  | E.Binary { f = E.Plus; x = E.Cst fill;
               y = E.Binary { f = E.Mul; x = body; y = E.Cst coefficient; _ }; _ }
  | E.Binary { f = E.Plus;
               x = E.Binary { f = E.Mul; x = body; y = E.Cst coefficient; _ };
               y = E.Cst fill; _ }
    when Bitvector.is_fill fill ->
      let positive = Bitvector.neg coefficient in
      [ E.unary E.Not (E.binary E.Mul (E.constant positive) body) ]
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
      let complement_offsets () =
        match f, x, y with
        | E.Plus, E.Unary { f = E.Not; x = base; _ }, one
          when is_number Z.one one -> [ E.unary E.Minus base ]
        | E.Plus, one, E.Unary { f = E.Not; x = base; _ }
          when is_number Z.one one -> [ E.unary E.Minus base ]
        | E.Minus, E.Unary { f = E.Minus; x = base; _ }, one
          when is_number Z.one one -> [ E.unary E.Not base ]
        | E.Minus, fill, base
          when is_number (Z.pred (Z.shift_left Z.one width)) fill ->
            [ E.unary E.Not base ]
        | _ -> []
      in
      let null_falling_factorial () =
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
        let factor = function
          | E.Binary { f = E.Minus; x = base; y = E.Cst offset; _ } ->
              let value = Bitvector.value_of offset in
              if Z.leq value (Z.of_int 8) then Some (base, Z.to_int value)
              else None
          | base -> Some (base, 0)
        in
        let parsed = List.filter_map factor factors in
        match parsed with
        | [] -> []
        | (base, _) :: _ ->
            let offsets =
              parsed
              |> List.filter_map (fun (other, offset) -> if same base other then Some offset else None)
              |> List.sort_uniq Int.compare
            in
            let degree = List.length factors in
            let rec range from upto = if from = upto then [] else from :: range (from + 1) upto in
            if degree < 2 || degree > 8 || offsets <> range 0 degree then []
            else
              let rec v2_factorial n power total =
                if power > n then total
                else v2_factorial n (power * 2) (total + (n / power))
              in
              let valuation = v2_factorial degree 2 0 in
              let divisor = Z.shift_left Z.one (max 0 (width - valuation)) in
              if Z.equal (Z.erem coefficient divisor) Z.zero then [ zero ] else []
      in
      let mask_compositions () =
        let nested op = function
          | E.Binary { f; x = base; y = E.Cst mask; _ } when f = op -> Some (base, mask)
          | E.Binary { f; x = E.Cst mask; y = base; _ } when f = op -> Some (base, mask)
          | _ -> None
        in
        match f, nested f x, constant_value y with
        | E.And, Some (base, first), Some second ->
            [ E.binary E.And base (E.constant (Bitvector.logand first second)) ]
        | E.Or, Some (base, first), Some second ->
            [ E.binary E.Or base (E.constant (Bitvector.logor first second)) ]
        | E.Xor, Some (base, first), Some second ->
            [ E.binary E.Xor base (E.constant (Bitvector.logxor first second)) ]
        | _ -> []
      in
      let complementary_masks () =
        let masked = function
          | E.Binary { f = E.And; x = base; y = E.Cst mask; _ }
          | E.Binary { f = E.And; x = E.Cst mask; y = base; _ } -> Some (base, mask)
          | _ -> None
        in
        match masked x, masked y with
        | Some (left, left_mask), Some (right, right_mask)
          when same left right
               && Bitvector.equal left_mask (Bitvector.lognot right_mask) -> [ left ]
        | _ -> []
      in
      let branchless_select () =
        let signed_condition = function
          | E.Unary { f = E.Sext _; x = condition; _ } when E.sizeof condition = 1 ->
              Some condition
          | _ -> None
        in
        match f with
        | E.Xor ->
            let select masked fallback =
              match masked with
              | E.Binary { f = E.And; x = E.Binary { f = E.Xor; x = a; y = b; _ };
                           y = mask; _ }
                when same fallback b ->
                  Option.map (fun condition -> E.ite condition a b) (signed_condition mask)
              | _ -> None
            in
            List.filter_map Fun.id [ select x y; select y x ]
        | E.Or ->
            let masked = function
              | E.Binary { f = E.And; x = value; y = mask; _ } -> Some (value, mask)
              | _ -> None
            in
            (match masked x, masked y with
            | Some (a, mask), Some (b, E.Unary { f = E.Not; x = other; _ })
              when same mask other ->
                Option.to_list (Option.map (fun c -> E.ite c a b) (signed_condition mask))
            | _ -> [])
        | E.Plus ->
            let select base = function
              | E.Binary { f = E.And; x = E.Binary { f = E.Minus; x = b; y = a; _ };
                           y = mask; _ }
                when same base a ->
                  Option.map (fun c -> E.ite c b a) (signed_condition mask)
              | _ -> None
            in
            List.filter_map Fun.id [ select x y; select y x ]
        | _ -> []
      in
      let boolean_factoring () =
        let pair = function
          | E.Binary { f = E.And; x; y; _ } -> Some (x, y)
          | _ -> None
        in
        let xor_pair left right =
          match pair left, pair right with
          | Some (a, E.Unary { f = E.Not; x = b; _ }),
            Some (E.Unary { f = E.Not; x = c; _ }, d)
            when same a c && same b d -> Some (E.binary E.Xor a b)
          | Some (E.Unary { f = E.Not; x = b; _ }, a),
            Some (d, E.Unary { f = E.Not; x = c; _ })
            when same a c && same b d -> Some (E.binary E.Xor a b)
          | _ -> None
        in
        let factor_pair left right =
          match pair left, pair right with
          | Some (a, b), Some (c, d) ->
              if same a c then Some (E.binary E.And a (E.binary E.Or b d))
              else if same a d then Some (E.binary E.And a (E.binary E.Or b c))
              else if same b c then Some (E.binary E.And b (E.binary E.Or a d))
              else if same b d then Some (E.binary E.And b (E.binary E.Or a c))
              else None
          | _ -> None
        in
        if f = E.Or then
          List.filter_map Fun.id [ xor_pair x y; xor_pair y x; factor_pair x y ]
        else []
      in
      let shift_mask () =
        match f, x, constant_value y with
        | E.Lsl, E.Binary { f = E.Lsr; x = base; y = amount; _ }, Some left_amount ->
            (match constant_value amount with
            | Some right_amount when Bitvector.equal left_amount right_amount ->
                let count = bounded_count width left_amount in
                if count > 0 && count < width then
                  let low = Z.pred (Z.shift_left Z.one count) in
                  [ E.binary E.And base (constant width (Z.lognot low)) ]
                else []
            | _ -> [])
        | _ -> []
      in
      let identities =
        match f with
        | E.Mul when null_falling_factorial () <> [] -> null_falling_factorial ()
        | E.And when complements x y -> [ zero ]
        | E.And | E.Or | E.Xor when complementary_masks () <> [] -> complementary_masks ()
        | E.Or when boolean_factoring () <> [] -> boolean_factoring ()
        | E.Or | E.Xor when complements x y -> [ fill ]
        | E.Plus when complements x y -> [ fill ]
        | E.Plus when negates x y -> [ zero ]
        | E.Plus | E.Minus when complement_offsets () <> [] -> complement_offsets ()
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
      folded @ mask_compositions () @ branchless_select () @ shift_mask () @ identities
  | E.Ite { c; t; e; _ } ->
      if same t e then [ t ]
      else
        let rec substitute target replacement = function
          | expression when same expression target -> replacement
          | E.Unary { f; x; _ } -> E.unary f (substitute target replacement x)
          | E.Binary { f; x; y; _ } ->
              E.binary f (substitute target replacement x) (substitute target replacement y)
          | E.Ite { c; t; e; _ } ->
              E.ite (substitute target replacement c)
                (substitute target replacement t) (substitute target replacement e)
          | expression -> expression
        in
        let rec fold expression =
          let rebuilt =
            match expression with
            | E.Unary { f; x; _ } -> E.unary f (fold x)
            | E.Binary { f; x; y; _ } -> E.binary f (fold x) (fold y)
            | E.Ite { c; t; e; _ } -> E.ite (fold c) (fold t) (fold e)
            | expression -> expression
          in
          match peepholes evaluate rebuilt with candidate :: _ -> candidate | [] -> rebuilt
        in
        let structural =
          match c, t, e with
          | E.Unary { f = E.Not; x = condition; _ }, _, _ -> [ E.ite condition e t ]
          | E.Binary { f = E.Diff; x; y; _ }, _, _ ->
              [ E.ite (E.binary E.Eq x y) e t ]
          | condition, E.Ite { c = nested; t = yes; _ }, _ when same condition nested ->
              [ E.ite condition yes e ]
          | condition, _, E.Ite { c = nested; e = no; _ } when same condition nested ->
              [ E.ite condition t no ]
          | E.Binary { f = E.Eq; x = variable; y = (E.Cst _ as value); _ }, _, _
          | E.Binary { f = E.Eq; x = (E.Cst _ as value); y = variable; _ }, _, _ ->
              let reduced = fold (substitute variable value t) in
              if same reduced t then [] else [ E.ite c reduced e ]
          | _ -> []
        in
        let branch_width = E.sizeof t in
        let condition_mask =
          if E.sizeof c = 1 then Some (E.unary (E.Sext (branch_width - 1)) c)
          else None
        in
        structural @
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
        | (E.Binary { f = E.Lsl; x; y = E.Cst amount; _ } as atom) ->
            let count = bounded_count width amount in
            if count < width then
              let scale = Z.shift_left Z.one count in
              collect (Z.mul coefficient scale) x
            else add atom coefficient
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

let minterm_ring_expansion ?(opaque_atoms = []) original candidate =
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
      else if List.exists (E.is_equal expression) opaque_atoms then add_atom expression
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
              | Some amount when bounded_count width amount < width ->
                  Option.map
                    (fun expanded_x ->
                      let power =
                        constant width
                          (Z.shift_left Z.one (bounded_count width amount))
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

let minterm_ring_proof ?(opaque_atoms = []) original candidate =
  Option.map
    (fun (equalities, ring_equalities, _, _) -> (equalities, ring_equalities))
    (minterm_ring_expansion ~opaque_atoms original candidate)

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
