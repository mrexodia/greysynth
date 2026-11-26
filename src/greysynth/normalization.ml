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

let is_permutation_poly ~width coefficients =
  if width < 2 then false
  else
    let coefficient degree =
      Option.value (List.nth_opt coefficients degree) ~default:Z.zero
    in
    let odd value = Z.testbit value 0 in
    let sum_with_parity parity =
      List.mapi (fun degree value -> degree, value) coefficients
      |> List.fold_left
           (fun sum (degree, value) ->
             if degree >= 2 && degree mod 2 = parity then Z.add sum value else sum)
           Z.zero
    in
    odd (coefficient 1)
    && not (odd (sum_with_parity 0))
    && not (odd (sum_with_parity 1))

let invert_permutation_poly_newton ~width coefficients =
  if not (is_permutation_poly ~width coefficients) then None
  else
    let modulus = Z.shift_left Z.one width in
    let normalize value =
      let value = Z.erem value modulus in
      if Z.sign value < 0 then Z.add value modulus else value
    in
    let v2_factorial n =
      let rec loop power total =
        if power > n then total else loop (power * 2) (total + (n / power))
      in loop 2 0
    in
    let rec find_degree degree =
      if v2_factorial degree >= width then degree else find_degree (degree + 1)
    in
    let degree = find_degree 1 and raw_degree = 2 * (find_degree 1 - 1) in
    let second = Array.make_matrix (raw_degree + 1) (raw_degree + 1) Z.zero
    and first = Array.make_matrix (degree + 1) (degree + 1) Z.zero in
    second.(0).(0) <- Z.one;
    first.(0).(0) <- Z.one;
    for n = 1 to raw_degree do
      for k = 1 to n do
        second.(n).(k) <- normalize
            (Z.add second.(n - 1).(k - 1)
               (Z.mul (Z.of_int k) second.(n - 1).(k)))
      done
    done;
    for n = 1 to degree do
      for k = 1 to n do
        first.(n).(k) <- normalize
            (Z.sub first.(n - 1).(k - 1)
               (Z.mul (Z.of_int (n - 1)) first.(n - 1).(k)))
      done
    done;
    let reduce power =
      let falling = Array.make (degree + 1) Z.zero in
      Array.iteri
        (fun exponent coefficient ->
          if not (Z.equal coefficient Z.zero) then
            for k = 0 to min exponent degree do
              falling.(k) <- normalize
                  (Z.add falling.(k) (Z.mul coefficient second.(exponent).(k)))
            done)
        power;
      for k = 0 to degree do
        let bits = max 0 (width - v2_factorial k) in
        falling.(k) <-
          if bits = 0 then Z.zero
          else Z.erem falling.(k) (Z.shift_left Z.one bits)
      done;
      let result = Array.make degree Z.zero in
      for k = 0 to degree - 1 do
        if not (Z.equal falling.(k) Z.zero) then
          for exponent = 0 to k do
            result.(exponent) <- normalize
                (Z.add result.(exponent)
                   (Z.mul falling.(k) first.(k).(exponent)))
          done
      done;
      result
    in
    let of_list values =
      let result = Array.make degree Z.zero in
      List.iteri (fun index value -> if index < degree then result.(index) <- normalize value)
        values;
      result
    in
    let add left right =
      Array.init degree (fun index -> normalize (Z.add left.(index) right.(index)))
    and neg value = Array.map (fun coefficient -> normalize (Z.neg coefficient)) value in
    let sub left right = add left (neg right) in
    let mul left right =
      let raw = Array.make (2 * degree - 1) Z.zero in
      Array.iteri (fun i a ->
          if not (Z.equal a Z.zero) then
            Array.iteri (fun j b ->
                if not (Z.equal b Z.zero) then
                  raw.(i + j) <- normalize (Z.add raw.(i + j) (Z.mul a b))) right)
        left;
      reduce raw
    in
    let compose source argument =
      Array.fold_right
        (fun coefficient result ->
          let result = mul result argument in
          result.(0) <- normalize (Z.add result.(0) coefficient);
          result)
        source (Array.make degree Z.zero)
    in
    let source = of_list coefficients in
    let a0 = source.(0) in
    let shifted = Array.copy source in
    shifted.(0) <- Z.zero;
    let derivative = Array.make degree Z.zero in
    for index = 1 to degree - 1 do
      derivative.(index - 1) <- normalize (Z.mul (Z.of_int index) source.(index))
    done;
    let variable = Array.make degree Z.zero in
    variable.(1) <- Z.one;
    let g = ref (Array.copy variable) and h = ref (of_list [ Z.one ]) in
    let steps = ref 0 and covered = ref 1 in
    while !covered < width do incr steps; covered := 2 * !covered done;
    for _ = 1 to !steps do
      let derivative_at_g = compose derivative !g in
      let correction = sub (of_list [ Z.of_int 2 ]) (mul derivative_at_g !h) in
      h := mul !h correction;
      let residual = sub (compose shifted !g) variable in
      g := sub !g (mul !h residual)
    done;
    let affine = of_list [ Z.neg a0; Z.one ] in
    Some (Array.to_list (compose !g affine))

let invert_permutation_poly ~width ~max_degree coefficients =
  if not (is_permutation_poly ~width coefficients) || max_degree < 1 then None
  else if max_degree >= width + 2 then
    invert_permutation_poly_newton ~width coefficients
  else
    let odd value = Z.testbit value 0 in
    let modulus = Z.shift_left Z.one width in
    let normalize value =
      let value = Z.erem value modulus in
      if Z.sign value < 0 then Z.add value modulus else value
    in
    let eval coefficients value =
      List.rev coefficients
      |> List.fold_left (fun result coefficient -> normalize (Z.add coefficient (Z.mul value result))) Z.zero
    in
    let derivative coefficients value =
      coefficients |> List.mapi (fun degree coefficient -> degree, coefficient)
      |> List.fold_left
           (fun result (degree, coefficient) ->
             if degree = 0 then result
             else
               let term =
                 Z.mul (Z.of_int degree) coefficient
                 |> fun coefficient -> Z.mul coefficient (Z.pow value (degree - 1))
               in
               normalize (Z.add result term))
           Z.zero
    in
    let root = ref Z.zero in
    for _ = 1 to width + 1 do
      let slope = derivative coefficients !root in
      if odd slope then
        root := normalize (Z.sub !root (Z.mul (eval coefficients !root) (Z.invert slope modulus)))
    done;
    let poly_mul left right limit =
      let result = Array.make (limit + 1) Z.zero in
      List.iteri (fun i a ->
          List.iteri (fun j b ->
              if i + j <= limit then
                result.(i + j) <- normalize (Z.add result.(i + j) (Z.mul a b))) right) left;
      Array.to_list result
    in
    let compose source inverse limit =
      let result = Array.make (limit + 1) Z.zero in
      let power = ref (Z.one :: List.init limit (fun _ -> Z.zero)) in
      List.iter
        (fun coefficient ->
          List.iteri (fun degree value ->
              result.(degree) <- normalize (Z.add result.(degree) (Z.mul coefficient value))) !power;
          power := poly_mul !power inverse limit)
        source;
      Array.to_list result
    in
    let inverse = ref [ !root ] in
    let slope_inverse = Z.invert (derivative coefficients !root) modulus in
    for degree = 1 to max_degree do
      let padded = !inverse @ [ Z.zero ] in
      let composed = compose coefficients padded degree in
      let current = Option.value (List.nth_opt composed degree) ~default:Z.zero in
      let target = if degree = 1 then Z.one else Z.zero in
      inverse := padded |> List.mapi (fun index value ->
          if index = degree then normalize (Z.mul (Z.sub target current) slope_inverse)
          else value)
    done;
    let probes =
      List.init 256 Z.of_int
      @ List.init width (fun bit -> Z.shift_left Z.one bit)
      @ [ Z.pred modulus ]
    in
    if List.for_all
         (fun value -> Z.equal (eval !inverse (eval coefficients value)) (normalize value))
         probes
    then Some !inverse else None

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

let rec peepholes evaluate expression =
  let width = E.sizeof expression in
  let zero = zeros width and one = integer width 1 in
  let fill = constant width (Z.pred (Z.shift_left Z.one width)) in
  let same = E.is_equal in
  match expression with
  | E.Unary { f = E.Not;
              x = E.Binary { f = E.Minus; x = base; y = one; _ }; _ }
    when is_number Z.one one -> [ E.unary E.Minus base ]
  | E.Unary { f = E.Not; x = E.Unary { f = E.Minus; x = base; _ }; _ } ->
      [ E.binary E.Minus base (integer (E.sizeof base) 1) ]
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

let linear_candidates ?(opaque_atoms = []) ?(max_atoms = !c_normalization_max_atoms)
    ?(semantic_bitwise = false) cost expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let mask = Z.pred modulus in
  let normalize value = Z.logand value mask in
  let atoms = ref [] in
  let saw_nonlinear = ref false in
  let visited = ref 0 in
  let tick () =
    incr visited;
    let visit_limit = max 4096 (16 * (1 lsl min 10 !c_normalization_max_atoms)) in
    if !visited > visit_limit then raise Too_complex;
    if !visited mod 32 = 0 then check_timeout ()
  in
  let atom expression =
    if E.sizeof expression <> width then raise Too_complex;
    let expression, complemented = canonical_bitwise_atom expression in
    let rec lookup index = function
      | [] ->
          if index >= max_atoms then raise Too_complex;
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
    if List.exists (E.is_equal expression) opaque_atoms then atom expression
    else match expression with
    | E.Cst value -> Number (Bitvector.value_of value)
    | E.Unary { f = E.Minus; x; _ } -> Scale (mask, linear x)
    | E.Unary { f = E.Not; x; _ } -> Not (linear x)
    | E.Binary { f = E.Plus; x; y; _ } -> Add (linear x, linear y)
    | E.Binary { f = E.Minus; x; y; _ } -> Sub (linear x, linear y)
    | E.Binary { f = E.Mul; x; y; _ } -> (
        match constant_value x, constant_value y with
        | Some k, _ -> Scale (Bitvector.value_of k, linear y)
        | _, Some k -> Scale (Bitvector.value_of k, linear x)
        | _ -> saw_nonlinear := true; atom expression)
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
    if List.exists (E.is_equal expression) opaque_atoms then atom expression
    else match expression with
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
    if semantic_bitwise && count <= min 6 !c_normalization_max_atoms then (
      let zero = Z.zero and one = Z.one
      and minus_one = mask and minus_two = normalize (Z.of_int (-2)) in
      if Z.equal target.(0) zero
         && Array.for_all (fun value -> Z.equal value zero || Z.equal value one) target
      then
        let truth = Array.map (Z.equal one) target in
        List.iter offer (boolean_candidates truth)
      else if Z.equal target.(0) minus_one
              && Array.for_all
                   (fun value -> Z.equal value minus_one || Z.equal value minus_two)
                   target
      then
        let low_truth = Array.map (Z.equal minus_two) target in
        List.iter (fun boolean -> offer (E.unary E.Not boolean))
          (boolean_candidates low_truth));
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
    let rec obvious_minterm = function
      | E.Var _ | E.Unary { f = E.Not; x = E.Var _; _ } -> true
      | E.Binary { f = E.And; x; y; _ } -> obvious_minterm x && obvious_minterm y
      | _ -> false
    in
    let rec obvious_grouped_sum = function
      | E.Binary { f = E.Plus; x; y; _ } -> obvious_grouped_sum x && obvious_grouped_sum y
      | E.Binary { f = E.Mul; x = E.Cst _; y; _ }
      | E.Binary { f = E.Mul; x = y; y = E.Cst _; _ } -> obvious_minterm y
      | term -> obvious_minterm term
    in
    if not !saw_nonlinear && count <= min 6 !c_normalization_max_atoms
       && List.length distinct <= 8
       && (count <= 4 || cost expression >= 300 || obvious_grouped_sum expression) then (
      let grouped =
        distinct
        |> List.filter (fun value -> not (Z.equal value Z.zero))
        |> List.filter_map (fun value ->
               let truth = Array.map (Z.equal value) target in
               match
                 boolean_candidates truth
                 |> List.sort (fun left right -> Int.compare (cost left) (cost right))
               with
               | boolean :: _ -> Some (scale value boolean)
               | [] -> None)
      in
      match grouped with
      | [] -> ()
      | terms -> offer (build_balanced E.Plus terms));
    if not !saw_nonlinear && count <= min 4 !c_normalization_max_atoms
       && Z.equal target.(0) Z.zero && List.length distinct = 4
    then (
      let nonzero = List.filter (fun value -> not (Z.equal value Z.zero)) distinct in
      List.iter
        (fun first ->
          List.iter
            (fun second ->
              if Z.compare first second < 0 then
                let combined = normalize (Z.add first second) in
                if List.mem combined distinct then (
                  let first_truth = Array.map
                      (fun value -> Z.equal value first || Z.equal value combined) target
                  and second_truth = Array.map
                      (fun value -> Z.equal value second || Z.equal value combined) target in
                  match
                    boolean_candidates first_truth
                    |> List.sort (fun left right -> Int.compare (cost left) (cost right)),
                    boolean_candidates second_truth
                    |> List.sort (fun left right -> Int.compare (cost left) (cost right))
                  with
                  | first_boolean :: _, second_boolean :: _ ->
                      offer
                        (E.binary E.Plus (scale first first_boolean)
                           (scale second second_boolean))
                  | _ -> ()))
            nonzero)
        nonzero);
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

let is_semantically_bitwise cost expression =
  let rec pure = function
    | E.Var _ -> true
    | E.Cst value -> Bitvector.is_zeros value || Bitvector.is_fill value
    | E.Unary { f = E.Not; x; _ } -> pure x
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } -> pure x && pure y
    | _ -> false
  in
  linear_candidates ~max_atoms:6 ~semantic_bitwise:true cost expression
  |> List.filter pure
  |> List.sort (fun left right -> Int.compare (cost left) (cost right))
  |> function candidate :: _ -> Some candidate | [] -> None

let has_nonuniform_bitwise_constant expression =
  let seen = Nodes.create 128 and found = ref false in
  let rec inspect under_bitwise node =
    if not !found && not (Nodes.mem seen node) then (
      Nodes.add seen node ();
      match node with
      | E.Cst value ->
          if under_bitwise
             && not (Bitvector.is_zeros value || Bitvector.is_fill value)
          then found := true
      | E.Unary { f = E.Not; x; _ } -> inspect under_bitwise x
      | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
          inspect true x; inspect true y
      | E.Unary { x; _ } -> inspect under_bitwise x
      | E.Binary { x; y; _ } -> inspect under_bitwise x; inspect under_bitwise y
      | E.Ite { c; t; e; _ } ->
          inspect under_bitwise c; inspect under_bitwise t; inspect under_bitwise e
      | _ -> ())
  in
  inspect false expression;
  !found

let semilinear_mba_candidate cost expression =
  let width = E.sizeof expression in
  if width > 128 || cost expression > 4096
     || Greysynth_utils.Utils.dag_size_bounded ~limit:1024 expression > 1024
     || not (has_nonuniform_bitwise_constant expression)
  then None
  else
    let deadline = Unix.gettimeofday () +. 0.2 in
    let constants = Hashtbl.create 16 and bitwise_constants = Hashtbl.create 16
    and saw_nonuniform = ref false
    and opaque = Nodes.create 8 and linear_seen = Nodes.create 128
    and bitwise_seen = Nodes.create 128 in
    let rec inspect under_bitwise node =
      if Unix.gettimeofday () > deadline then raise Too_complex;
      let seen = if under_bitwise then bitwise_seen else linear_seen in
      if not (Nodes.mem seen node) then (
        Nodes.add seen node ();
        if under_bitwise then
          match node with
          | E.Cst value ->
              let z = Bitvector.value_of value in
              Hashtbl.replace constants z ();
              Hashtbl.replace bitwise_constants z ();
              if not (Bitvector.is_zeros value || Bitvector.is_fill value)
              then saw_nonuniform := true
          | E.Unary { f = E.Not; x; _ } -> inspect true x
          | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
              inspect true x; inspect true y
          | atom ->
              Nodes.replace opaque atom ();
              if Nodes.length opaque > 6 then raise Too_complex
        else
          match node with
          | E.Unary { f = E.Not; x; _ } -> inspect false x
          | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
              inspect true x; inspect true y
          | E.Unary { x; _ } -> inspect false x
          | E.Binary { x; y; _ } -> inspect false x; inspect false y
          | E.Ite { c; t; e; _ } -> inspect false c; inspect false t; inspect false e
          | _ -> ())
    in
    let preflight_ok =
      try inspect false expression; true with Too_complex -> false
    in
    if not preflight_ok || not !saw_nonuniform || Nodes.length opaque > 6
       || Unix.gettimeofday () > deadline
    then None
    else
      let mask = Z.pred (Z.shift_left Z.one width) in
      let normalize value = Z.logand value mask in
      let all_constants = Hashtbl.fold (fun value () result -> value :: result) constants [] in
      let bit_constants =
        Hashtbl.fold (fun value () result -> value :: result) bitwise_constants []
      in
      let base_constants = bit_constants @ all_constants in
      let merged = ref base_constants in
      List.iter
        (fun left ->
          List.iter (fun right -> merged := Z.logor left right :: !merged) base_constants)
        base_constants;
      let take count values =
        let rec loop count = function
          | _ when count = 0 -> []
          | [] -> []
          | head :: tail -> head :: loop (count - 1) tail
        in loop count values
      in
      let bit_base = bit_constants |> List.map normalize |> List.sort_uniq Z.compare in
      let other_base =
        base_constants |> List.map normalize |> List.sort_uniq Z.compare
        |> List.filter (fun value -> not (List.mem value bit_base))
      in
      let base = bit_base @ other_base in
      let extras =
        !merged |> List.map normalize |> List.sort_uniq Z.compare
        |> List.filter (fun value -> not (List.mem value base))
      in
      let constants = take 32 (base @ extras) in
      let variables =
        Sample_evaluator.variables_of_expr expression
        |> List.map (fun (name, size) -> E.var name size name)
      in
      if variables = [] || List.length variables > 5
         || List.exists (fun variable -> E.sizeof variable <> width) variables
      then None
      else
        let variants variable =
          let simple =
            variable :: E.unary E.Not variable ::
            List.concat_map
              (fun value ->
                let constant = constant width value in
                [ E.binary E.And variable constant;
                  E.binary E.Or variable constant;
                  E.binary E.Xor variable constant;
                  E.binary E.Plus variable constant ])
              constants
          in
          let nested, scaled =
            if List.length variables <> 1 then [], []
            else
              (List.concat_map
                 (fun mask_value ->
                   let masked = E.binary E.And variable (constant width mask_value) in
                   List.map
                     (fun offset -> E.binary E.Plus masked (constant width offset))
                     constants)
                 constants,
               List.concat_map
                 (fun body ->
                   List.map
                     (fun coefficient ->
                       E.binary E.Mul (constant width coefficient) body)
                     constants)
                 simple)
          in
          simple @ nested @ scaled |> List.sort_uniq E.compare
        in
        let per_variable = List.map variants variables in
        let candidates = ref [] in
        List.iter (fun variants -> candidates := variants @ !candidates) per_variable;
        let canonical =
          try
            let evaluator = Sample_evaluator.make 1 in
            let evaluate assignment bit =
              let labels = Hashtbl.create (List.length variables) in
              List.iteri
                (fun index variable ->
                  let value =
                    if assignment land (1 lsl index) = 0 then Z.zero
                    else Z.shift_left Z.one bit
                  in
                  Hashtbl.add labels variable (constant width value))
                variables;
              evaluator.eval_label expression 0 labels |> Bitvector.value_of
            in
            let zero = evaluate 0 0 in
            let terms = ref [ constant width zero ] in
            let assignments = 1 lsl List.length variables in
            for assignment = 1 to assignments - 1 do
              let groups : (Z.t * int * Z.t) list ref = ref [] in
              for bit = 0 to width - 1 do
                let delta = normalize (Z.sub (evaluate assignment bit) zero) in
                let low_mask = Z.pred (Z.shift_left Z.one bit) in
                if not (Z.equal (Z.logand delta low_mask) Z.zero) then
                  raise Exit;
                let coefficient = Z.shift_right delta bit in
                let rec merge prefix = function
                  | [] ->
                      groups := List.rev_append prefix
                          [ coefficient, bit, Z.shift_left Z.one bit ]
                  | (previous, lowest, bits) :: rest ->
                      let required = Z.shift_left Z.one (width - bit) in
                      if Z.equal (Z.erem (Z.sub coefficient previous) required) Z.zero then
                        groups := List.rev_append prefix
                            ((previous, lowest, Z.logor bits (Z.shift_left Z.one bit)) :: rest)
                      else merge ((previous, lowest, bits) :: prefix) rest
                in
                merge [] !groups
              done;
              let minterm =
                variables
                |> List.mapi (fun index variable ->
                       if assignment land (1 lsl index) = 0
                       then E.unary E.Not variable else variable)
                |> function
                   | head :: tail -> List.fold_left (E.binary E.And) head tail
                   | [] -> assert false
              in
              List.iter
                (fun (coefficient, _, bits) ->
                  if not (Z.equal coefficient Z.zero) then
                    let masked = E.binary E.And minterm (constant width bits) in
                    let term =
                      if Z.equal coefficient Z.one then masked
                      else E.binary E.Mul (constant width coefficient) masked
                    in
                    terms := term :: !terms)
                !groups
            done;
            let terms = List.filter (fun term -> not (is_number Z.zero term)) !terms in
            Some (match terms with [] -> zeros width | _ -> build_balanced E.Plus terms)
          with _ -> None
        in
        Option.iter (fun candidate -> candidates := candidate :: !candidates) canonical;
        if List.length variables = 1 then (
          let target = Array.init 16 (fun index ->
              !(Config.evaluator).eval expression index |> Bitvector.value_of) in
          !candidates
          |> List.filter (fun candidate -> cost candidate <= 3)
          |> List.iter (fun body ->
                 let values = Array.init 16 (fun index ->
                     !(Config.evaluator).eval body index |> Bitvector.value_of) in
                 Smir_interp.analytical_candidates ~width ~target ~expression:body ~values
                 |> List.iter (fun candidate -> candidates := candidate :: !candidates)));
        (match per_variable with
        | first :: second :: rest ->
            List.iter
              (fun left ->
                List.iter
                  (fun right -> candidates := E.binary E.Plus left right :: !candidates)
                  second)
              first;
            ignore rest
        | _ -> ());
        let best = ref None in
        List.iter
          (fun candidate ->
            if cost candidate < cost expression
               && (match !best with
                   | None -> true
                   | Some previous -> cost candidate < cost previous)
               && Rewrite.samples_agree expression candidate
            then best := Some candidate)
          !candidates;
        !best

let power2_pullout_candidate cost expression =
  let width = E.sizeof expression in
  let factor = function
    | E.Cst value ->
        let value = Bitvector.value_of value in
        if Z.sign value > 0 then
          let amount = Z.trailing_zeros value in
          if amount > 0 then
            let scale = Z.shift_left Z.one amount in
            Some (scale, constant width (Z.shift_right value amount))
          else None
        else None
    | E.Binary { f = E.Mul; x = E.Cst value; y; _ }
    | E.Binary { f = E.Mul; x = y; y = E.Cst value; _ } ->
        let value = Bitvector.value_of value in
        if Z.sign value > 0 && Z.popcount value = 1 then Some (value, y) else None
    | E.Binary { f = E.Lsl; x; y = E.Cst amount; _ } ->
        let amount = bounded_count width amount in
        if amount > 0 && amount < width then Some (Z.shift_left Z.one amount, x) else None
    | _ -> None
  in
  let scale value term =
    if Z.equal value Z.one then term
    else E.binary E.Mul (constant width value) term
  in
  let candidate =
    match expression with
    | E.Binary { f = (E.And | E.Or | E.Xor as operation); x; y; _ } ->
        (match factor x, factor y with
        | Some (left_scale, left), Some (right_scale, right)
          when Z.equal left_scale right_scale ->
            Some (scale left_scale (E.binary operation left right))
        | Some (left_scale, left), _ when operation = E.And ->
            (match y with
            | E.Unary { f = E.Not; x = inner; _ } ->
                (match factor inner with
                | Some (right_scale, right) when Z.equal left_scale right_scale ->
                    Some (scale left_scale (E.binary E.And left (E.unary E.Not right)))
                | _ -> None)
            | E.Cst value ->
                let constant_value = Bitvector.value_of value in
                if Z.equal (Z.erem constant_value left_scale) Z.zero then
                  Some (scale left_scale
                          (E.binary E.And left (constant width (Z.div constant_value left_scale))))
                else None
            | _ -> None)
        | _ -> None)
    | _ -> None
  in
  Option.bind candidate (fun candidate ->
      if cost candidate < cost expression then Some candidate else None)

let demand_bits_candidate cost expression =
  let width = E.sizeof expression in
  let low_mask value =
    let value = Bitvector.value_of value in
    if Z.sign value <= 0 then None
    else
      let plus_one = Z.succ value in
      if Z.popcount plus_one = 1 then
        let bits = Z.trailing_zeros plus_one in
        if bits > 0 && bits < width then Some (bits, value) else None
      else None
  in
  match expression with
  | E.Binary { f = E.And; x = term; y = E.Cst mask; _ }
  | E.Binary { f = E.And; x = E.Cst mask; y = term; _ } ->
      Option.bind (low_mask mask) (fun (bits, mask_value) ->
          let rec narrow = function
            | E.Cst value ->
                constant (Bitvector.size_of value)
                  (Z.logand (Bitvector.value_of value) mask_value)
            | E.Unary { f; x; _ } -> E.unary f (narrow x)
            | E.Binary { f; x; y; _ } -> E.binary f (narrow x) (narrow y)
            | value -> value
          in
          let narrowed = E.binary E.And (narrow term) (constant width mask_value) in
          let zero_candidate =
            match term, bits with
            | E.Binary { f = E.Mul; x = variable;
                         y = E.Binary { f = E.Minus; x = same; y = E.Cst one; _ }; _ }, 1
              when E.is_equal variable same
                   && Z.equal (Bitvector.value_of one) Z.one -> Some (zeros width)
            | E.Binary { f = E.Mul;
                         x = E.Binary { f = E.Minus; x = same; y = E.Cst one; _ };
                         y = variable; _ }, 1
              when E.is_equal variable same
                   && Z.equal (Bitvector.value_of one) Z.one -> Some (zeros width)
            | _ -> None
          in
          let candidate = Option.value zero_candidate ~default:narrowed in
          if cost candidate < cost expression then Some candidate else None)
  | _ -> None

let xor_affine_mask_candidate cost expression =
  let width = E.sizeof expression and modulus = Z.shift_left Z.one (E.sizeof expression) in
  let normalize value = Z.logand value (Z.pred modulus) in
  let rec additive = function
    | E.Binary { f = E.Plus; x; y; _ } -> additive x @ additive y
    | term -> [ term ]
  in
  let constant_term = function E.Cst value -> Some (Bitvector.value_of value) | _ -> None in
  let scaled_variable = function
    | E.Binary { f = E.Mul; x = E.Cst coefficient; y = (E.Var _ as variable); _ }
    | E.Binary { f = E.Mul; x = (E.Var _ as variable); y = E.Cst coefficient; _ } ->
        Some (variable, Bitvector.value_of coefficient)
    | _ -> None
  in
  let scaled_mask = function
    | E.Binary { f = E.Mul; x = E.Cst coefficient;
                 y = E.Binary { f = E.And; x = E.Cst mask; y = (E.Var _ as variable); _ }; _ }
    | E.Binary { f = E.Mul; x = E.Cst coefficient;
                 y = E.Binary { f = E.And; x = (E.Var _ as variable); y = E.Cst mask; _ }; _ }
    | E.Binary { f = E.Mul;
                 x = E.Binary { f = E.And; x = E.Cst mask; y = (E.Var _ as variable); _ };
                 y = E.Cst coefficient; _ }
    | E.Binary { f = E.Mul;
                 x = E.Binary { f = E.And; x = (E.Var _ as variable); y = E.Cst mask; _ };
                 y = E.Cst coefficient; _ } ->
        Some (variable, Bitvector.value_of mask, Bitvector.value_of coefficient)
    | _ -> None
  in
  let terms = additive expression in
  match List.find_map constant_term terms,
        List.find_map scaled_variable terms,
        List.find_map scaled_mask terms with
  | Some offset, Some (variable, coefficient),
    Some (masked_variable, bitmask, masked_coefficient)
    when E.is_equal variable masked_variable
         && Z.equal (normalize masked_coefficient)
              (normalize (Z.neg (Z.mul (Z.of_int 2) coefficient)))
         && Z.equal (normalize offset) (normalize (Z.mul coefficient bitmask)) ->
      let body = E.binary E.Xor variable (constant width bitmask) in
      let candidate =
        if Z.equal coefficient Z.one then body
        else E.binary E.Mul (constant width coefficient) body
      in
      if cost candidate < cost expression then Some candidate else None
  | _ -> None

let known_bits_candidate cost expression =
  let candidate =
    let known = Known_bits.analyze expression in
    match Known_bits.is_constant known with
    | Some value when cost expression > 1 -> Some (constant known.width value)
    | _ ->
        match expression with
        | E.Binary { f = E.And; x = value; y = E.Cst bits; _ }
        | E.Binary { f = E.And; x = E.Cst bits; y = value; _ } ->
            let known = Known_bits.analyze value in
            let removed = Z.logand (Z.pred (Z.shift_left Z.one known.width))
                (Z.lognot (Bitvector.value_of bits)) in
            if Z.equal (Z.logand removed known.zeros) removed then Some value else None
        | E.Binary { f = E.Or; x = value; y = E.Cst bits; _ }
        | E.Binary { f = E.Or; x = E.Cst bits; y = value; _ } ->
            let known = Known_bits.analyze value in
            let bits = Bitvector.value_of bits in
            if Z.equal (Z.logand bits known.ones) bits then Some value else None
        | E.Binary { f = E.And; x; y; _ } ->
            if Known_bits.disjoint (Known_bits.analyze x) (Known_bits.analyze y)
            then Some (zeros (E.sizeof expression)) else None
        | E.Binary { f = E.Plus; x; y; _ } ->
            if Known_bits.disjoint (Known_bits.analyze x) (Known_bits.analyze y)
            then Some (E.binary E.Or x y) else None
        | E.Binary { f = E.Ult; x; y = E.Cst bound; _ } ->
            let known = Known_bits.analyze x in
            let maximum = Known_bits.possible_ones known
            and minimum = known.ones and bound = Bitvector.value_of bound in
            if Z.lt maximum bound then Some (integer (E.sizeof expression) 1)
            else if Z.geq minimum bound then Some (zeros (E.sizeof expression))
            else None
        | E.Binary { f = E.Eq; x; y = E.Cst expected; _ }
        | E.Binary { f = E.Eq; x = E.Cst expected; y = x; _ } ->
            let known = Known_bits.analyze x in
            let expected = Bitvector.value_of expected in
            if not (Z.equal (Z.logand expected known.zeros) Z.zero)
               || not (Z.equal
                         (Z.logand (Z.lognot expected) known.ones) Z.zero)
            then Some (zeros (E.sizeof expression)) else None
        | E.Ite { c; t; e; _ } ->
            (match Known_bits.is_constant (Known_bits.analyze c) with
            | Some value when Z.equal value Z.zero -> Some e
            | Some _ -> Some t
            | None -> None)
        | _ -> None
  in
  Option.bind candidate (fun candidate ->
      if cost candidate < cost expression then Some candidate else None)

let disjoint_component_candidate cost expression =
  let rec additive sign = function
    | E.Binary { f = E.Plus; x; y; _ } -> additive sign x @ additive sign y
    | E.Binary { f = E.Minus; x; y; _ } -> additive sign x @ additive (not sign) y
    | E.Unary { f = E.Minus; x; _ } -> additive (not sign) x
    | term -> [ if sign then term else E.unary E.Minus term ]
  in
  let terms = additive true expression |> Array.of_list in
  if Array.length terms < 2 || Array.length terms > 64 then None
  else
    let variables = Array.map Sample_evaluator.variables_of_expr terms in
    let parent = Array.init (Array.length terms) Fun.id in
    let rec find index =
      if parent.(index) = index then index
      else (parent.(index) <- find parent.(index); parent.(index))
    in
    let union left right =
      let left = find left and right = find right in
      if left <> right then parent.(right) <- left
    in
    for i = 0 to Array.length terms - 1 do
      for j = i + 1 to Array.length terms - 1 do
        if List.exists (fun variable -> List.mem variable variables.(j)) variables.(i)
        then union i j
      done
    done;
    let groups = Hashtbl.create 8 in
    Array.iteri (fun index term ->
        let root = find index in
        Hashtbl.replace groups root
          (term :: Option.value (Hashtbl.find_opt groups root) ~default:[])) terms;
    if Hashtbl.length groups < 2 then None
    else
      let changed = ref false in
      let sum = function
        | [] -> zeros (E.sizeof expression)
        | head :: tail -> List.fold_left (E.binary E.Plus) head tail
      in
      let components =
        Hashtbl.fold
          (fun _ terms result ->
            let component = sum terms in
            let variable_count =
              List.length (Sample_evaluator.variables_of_expr component)
            in
            let simplified =
              if variable_count <= 4 then
                match
                  linear_candidates ~max_atoms:4 cost component
                  |> List.sort (fun left right -> Int.compare (cost left) (cost right))
                with
                | candidate :: _ when cost candidate < cost component ->
                    changed := true; candidate
                | _ -> component
              else component
            in
            simplified :: result)
          groups []
      in
      let candidate = sum components in
      if !changed && cost candidate < cost expression then Some candidate else None

let component_linear_candidates cost expression =
  if cost expression > 256
     || List.length (Sample_evaluator.variables_of_expr expression) > 2
  then []
  else
  let rec additive sign = function
    | E.Binary { f = E.Plus; x; y; _ } -> additive sign x @ additive sign y
    | E.Binary { f = E.Minus; x; y; _ } -> additive sign x @ additive (not sign) y
    | E.Unary { f = E.Minus; x; _ } -> additive (not sign) x
    | term -> [ if sign then term else E.unary E.Minus term ]
  in
  let terms = additive true expression |> Array.of_list in
  if Array.length terms < 3 || Array.length terms > 64 then []
  else
    let opaque = Nodes.create 16 in
    let arithmetic = function
      | E.Binary { f = (E.Plus | E.Minus | E.Mul | E.Lsl); _ }
      | E.Unary { f = E.Minus; _ } -> true
      | _ -> false
    in
    let rec inspect under_bitwise term_index expression =
      if under_bitwise && arithmetic expression then (
        let indices = Option.value (Nodes.find_opt opaque expression) ~default:[] in
        if not (List.mem term_index indices) then
          Nodes.replace opaque expression (term_index :: indices))
      else
        match expression with
        | E.Unary { f = E.Not; x; _ } -> inspect true term_index x
        | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
            inspect true term_index x; inspect true term_index y
        | E.Unary { x; _ } -> inspect under_bitwise term_index x
        | E.Binary { x; y; _ } ->
            inspect under_bitwise term_index x; inspect under_bitwise term_index y
        | E.Ite { c; t; e; _ } ->
            inspect under_bitwise term_index c;
            inspect under_bitwise term_index t;
            inspect under_bitwise term_index e
        | _ -> ()
    in
    Array.iteri (fun index term -> inspect false index term) terms;
    let groups =
      Nodes.fold
        (fun opaque_atom indices result ->
          let indices = List.sort_uniq Int.compare indices in
          if List.length indices >= 2 && List.length indices < Array.length terms
          then (opaque_atom, indices) :: result else result)
        opaque []
      |> List.sort_uniq Stdlib.compare
    in
    let sum = function
      | [] -> zeros (E.sizeof expression)
      | head :: tail -> List.fold_left (E.binary E.Plus) head tail
    in
    groups
    |> List.filter_map (fun (opaque_atom, indices) ->
           let selected = List.map (Array.get terms) indices in
           let component = sum selected in
           let proposals = linear_candidates ~opaque_atoms:[ opaque_atom ] cost component in
           match
             proposals
             |> List.sort (fun left right -> Int.compare (cost left) (cost right))
           with
           | candidate :: _ when cost candidate < cost component ->
               let selected_set = Hashtbl.create (List.length indices) in
               List.iter (fun index -> Hashtbl.add selected_set index ()) indices;
               let remainder =
                 Array.to_list terms
                 |> List.mapi (fun index term -> index, term)
                 |> List.filter_map (fun (index, term) ->
                        if Hashtbl.mem selected_set index then None else Some term)
               in
               let rebuilt = sum (candidate :: remainder) in
               if cost rebuilt >= cost expression then None
               else
                 let equalities, component_ring =
                   Option.value
                     (minterm_ring_proof ~opaque_atoms:[ opaque_atom ] component candidate)
                     ~default:([ component, candidate ], [])
                 in
                 Some (rebuilt, equalities,
                       (expression, sum (component :: remainder)) :: component_ring)
           | _ -> None)

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

let ring_polynomial_candidate ?(max_operations = 50_000)
    ?(max_monomials = 256) ?(max_degree = 8) cost expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let normalize value =
    let value = Z.erem value modulus in
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let operations = ref 0 in
  let add_term monomial coefficient polynomial =
    incr operations;
    if !operations > max_operations || List.length monomial > max_degree then
      raise Ring_candidate_too_complex;
    let old = Option.value (RingPolynomial.find_opt monomial polynomial) ~default:Z.zero in
    let value = normalize (Z.add old coefficient) in
    let result =
      if Z.equal value Z.zero then RingPolynomial.remove monomial polynomial
      else RingPolynomial.add monomial value polynomial
    in
    if RingPolynomial.cardinal result > max_monomials then raise Ring_candidate_too_complex;
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

let minterm_ring_poly_candidate cost expression =
  let width = E.sizeof expression in
  let atom_table = Nodes.create 8 in
  let rec collect_bitwise = function
    | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
    | E.Unary { f = E.Not; x; _ } -> collect_bitwise x
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
        collect_bitwise x; collect_bitwise y
    | atom -> Nodes.replace atom_table atom ()
  and collect_ring = function
    | E.Unary { f = E.Minus; x; _ } -> collect_ring x
    | E.Binary { f = (E.Plus | E.Minus | E.Mul); x; y; _ } ->
        collect_ring x; collect_ring y
    | (E.Unary { f = E.Not; _ }
      | E.Binary { f = (E.And | E.Or | E.Xor); _ }) as bitwise ->
        collect_bitwise bitwise
    | E.Cst _ -> ()
    | atom -> Nodes.replace atom_table atom ()
  in
  collect_ring expression;
  let variables =
    Nodes.fold (fun atom () result -> atom :: result) atom_table []
    |> List.sort E.compare |> Array.of_list
  in
  let count = Array.length variables in
  if count < 2 || count > 3
     || Greysynth_utils.Utils.dag_size_bounded ~limit:1024 expression > 1024
  then None
  else
    let variable_index node =
      let rec find index =
        if index = count then None
        else if E.is_equal variables.(index) node then Some index else find (index + 1)
      in find 0
    in
    let rec pure_bitwise expression =
      match variable_index expression with
      | Some _ -> true
      | None ->
        match expression with
        | E.Cst value -> Bitvector.is_zeros value || Bitvector.is_fill value
        | E.Unary { f = E.Not; x; _ } -> pure_bitwise x
        | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
            pure_bitwise x && pure_bitwise y
        | _ -> false
    in
    let rec truth assignment expression =
      match variable_index expression with
      | Some index -> assignment land (1 lsl index) <> 0
      | None ->
          match expression with
          | E.Cst value -> Bitvector.is_fill value
          | E.Unary { f = E.Not; x; _ } -> not (truth assignment x)
          | E.Binary { f; x; y; _ } ->
              let x = truth assignment x and y = truth assignment y in
              if f = E.And then x && y else if f = E.Or then x || y else x <> y
          | _ -> false
    in
    let minterms =
      Array.init (1 lsl count) (fun assignment ->
          List.init count (fun index ->
              if assignment land (1 lsl index) = 0 then E.unary E.Not variables.(index)
              else variables.(index))
          |> function
             | head :: tail -> List.fold_left (E.binary E.And) head tail
             | [] -> constant width (Z.pred (Z.shift_left Z.one width)))
    in
    let sum = function
      | [] -> zeros width
      | head :: tail -> build_balanced E.Plus (head :: tail)
    in
    let expansion expression =
      if truth 0 expression then
        let excluded =
          List.init ((1 lsl count) - 1) (fun index -> index + 1)
          |> List.filter (fun assignment -> not (truth assignment expression))
          |> List.map (Array.get minterms)
        in
        List.fold_left (E.binary E.Minus)
          (constant width (Z.pred (Z.shift_left Z.one width))) excluded
      else
        List.init ((1 lsl count) - 1) (fun index -> index + 1)
        |> List.filter (fun assignment -> truth assignment expression)
        |> List.map (Array.get minterms) |> sum
    in
    let replacements = Nodes.create 32 and linear_edges = ref [] in
    let nonlinear = ref false in
    let rec substitute expression =
      match Nodes.find_opt replacements expression with
      | Some result -> result
      | None ->
          let result =
            if pure_bitwise expression then (
              let result = expansion expression in
              if not (E.is_equal expression result) then
                linear_edges := (expression, result) :: !linear_edges;
              result)
            else
              match expression with
              | E.Unary { f; x; _ } -> E.unary f (substitute x)
              | E.Binary { f = E.Mul; x; y; _ } ->
                  if Option.is_none (constant_value x) && Option.is_none (constant_value y)
                  then nonlinear := true;
                  E.binary E.Mul (substitute x) (substitute y)
              | E.Binary { f; x; y; _ } -> E.binary f (substitute x) (substitute y)
              | E.Ite { c; t; e; _ } -> E.ite (substitute c) (substitute t) (substitute e)
              | node -> node
          in
          Nodes.add replacements expression result;
          result
    in
    let substituted = substitute expression in
    if not !nonlinear || List.length !linear_edges > 24 then None
    else
      match ring_polynomial_candidate cost substituted with
      | None -> None
      | Some polynomial ->
          let compact =
            linear_candidates ~max_atoms:8 cost polynomial
            |> List.sort (fun left right -> Int.compare (cost left) (cost right))
            |> function head :: _ -> head | [] -> polynomial
          in
          let candidate = compact in
          if cost candidate >= cost expression then None
          else
            Some
              (candidate, List.rev !linear_edges,
               [ substituted, polynomial ],
               if E.is_equal compact polynomial then [] else [ polynomial, compact ])

module AndPolynomial = Map.Make (Int)

let polysim_candidate cost expression =
  let rec has_nonlinear_product = function
    | E.Binary { f = E.Mul; x; y; _ }
      when Option.is_none (constant_value x) && Option.is_none (constant_value y) -> true
    | E.Unary { x; _ } -> has_nonlinear_product x
    | E.Binary { x; y; _ } -> has_nonlinear_product x || has_nonlinear_product y
    | E.Ite { c; t; e; _ } ->
        has_nonlinear_product c || has_nonlinear_product t || has_nonlinear_product e
    | _ -> false
  in
  if not (has_nonlinear_product expression) then None else
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let normalize value =
    let value = Z.erem value modulus in
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let atoms_table = Nodes.create 32 in
  let rec collect_bitwise = function
    | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
    | E.Unary { f = E.Not; x; _ } -> collect_bitwise x
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
        collect_bitwise x; collect_bitwise y
    | atom -> Nodes.replace atoms_table atom ()
  and collect_ring = function
    | E.Unary { f = E.Minus; x; _ } -> collect_ring x
    | E.Binary { f = (E.Plus | E.Minus | E.Mul); x; y; _ } ->
        collect_ring x; collect_ring y
    | (E.Unary { f = E.Not; _ }
      | E.Binary { f = (E.And | E.Or | E.Xor); _ }) as bitwise ->
        collect_bitwise bitwise
    | E.Cst _ -> ()
    | atom -> Nodes.replace atoms_table atom ()
  in
  collect_ring expression;
  let atoms =
    Nodes.fold (fun atom () result -> atom :: result) atoms_table []
    |> List.sort E.compare |> Array.of_list
  in
  let atom_count = Array.length atoms in
  if atom_count < 2 || atom_count > 32
     || Array.exists (fun atom -> E.sizeof atom <> width) atoms
     || Greysynth_utils.Utils.dag_size_bounded ~limit:2048 expression > 2048
  then None
  else
    let atom_index expression =
      let rec find index =
        if index = atom_count then None
        else if E.is_equal atoms.(index) expression then Some index
        else find (index + 1)
      in
      find 0
    in
    let rec pure_bitwise expression =
      match atom_index expression with
      | Some _ -> true
      | None ->
          match expression with
          | E.Cst value -> Bitvector.is_zeros value || Bitvector.is_fill value
          | E.Unary { f = E.Not; x; _ } -> pure_bitwise x
          | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
              pure_bitwise x && pure_bitwise y
          | _ -> false
    in
    let operations = ref 0 and total_monomials = ref 0 in
    let tick () =
      incr operations;
      if !operations > 1_000_000 then raise Ring_candidate_too_complex
    in
    let add_term monomial coefficient polynomial =
      tick ();
      let coefficient = normalize coefficient in
      let old = Option.value (AndPolynomial.find_opt monomial polynomial) ~default:Z.zero in
      let coefficient = normalize (Z.add old coefficient) in
      let result =
        if Z.equal coefficient Z.zero then AndPolynomial.remove monomial polynomial
        else AndPolynomial.add monomial coefficient polynomial
      in
      if AndPolynomial.cardinal result > 64 then raise Ring_candidate_too_complex;
      result
    in
    let poly_constant value = add_term 0 value AndPolynomial.empty in
    let add left right = AndPolynomial.fold add_term left right in
    let neg polynomial =
      AndPolynomial.fold
        (fun monomial coefficient result -> add_term monomial (Z.neg coefficient) result)
        polynomial AndPolynomial.empty
    in
    let sub left right = add left (neg right) in
    let scale coefficient polynomial =
      AndPolynomial.fold
        (fun monomial value result -> add_term monomial (Z.mul coefficient value) result)
        polynomial AndPolynomial.empty
    in
    let mul left right =
      AndPolynomial.fold
        (fun left_monomial left_coefficient result ->
          AndPolynomial.fold
            (fun right_monomial right_coefficient result ->
              add_term (left_monomial lor right_monomial)
                (Z.mul left_coefficient right_coefficient) result)
            right result)
        left AndPolynomial.empty
    in
    let memo = Nodes.create 64 in
    let rec transform expression =
      match Nodes.find_opt memo expression with
      | Some result -> result
      | None ->
          let result =
            match atom_index expression with
            | Some index -> add_term (1 lsl index) Z.one AndPolynomial.empty
            | None ->
                match expression with
                | E.Cst value when Bitvector.is_zeros value -> AndPolynomial.empty
                | E.Cst value when Bitvector.is_fill value -> poly_constant Z.one
                | E.Unary { f = E.Not; x; _ } -> sub (poly_constant Z.one) (transform x)
                | E.Binary { f = E.And; x; y; _ } -> mul (transform x) (transform y)
                | E.Binary { f = E.Or; x; y; _ } ->
                    let x = transform x and y = transform y in
                    sub (add x y) (mul x y)
                | E.Binary { f = E.Xor; x; y; _ } ->
                    let x = transform x and y = transform y in
                    sub (add x y) (scale (Z.of_int 2) (mul x y))
                | _ -> raise Ring_candidate_too_complex
          in
          Nodes.add memo expression result;
          result
    in
    let conjunction monomial =
      let terms = ref [] in
      for index = 0 to atom_count - 1 do
        if monomial land (1 lsl index) <> 0 then terms := atoms.(index) :: !terms
      done;
      match List.rev !terms with
      | head :: tail -> List.fold_left (E.binary E.And) head tail
      | [] -> constant width (Z.pred modulus)
    in
    let scaled coefficient term =
      if Z.equal coefficient Z.one then term
      else if Z.equal coefficient (Z.pred modulus) then E.unary E.Minus term
      else E.binary E.Mul (constant width coefficient) term
    in
    let expansion expression =
      let polynomial = transform expression in
      total_monomials := !total_monomials + AndPolynomial.cardinal polynomial;
      if !total_monomials > 2048 then raise Ring_candidate_too_complex;
      let terms =
        AndPolynomial.fold
          (fun monomial coefficient result ->
            let coefficient = if monomial = 0 then normalize (Z.neg coefficient)
              else coefficient in
            if Z.equal coefficient Z.zero then result
            else
              let term =
                if monomial = 0 then constant width coefficient
                else scaled coefficient (conjunction monomial)
              in
              term :: result)
          polynomial []
      in
      match List.sort E.compare terms with
      | [] -> zeros width
      | terms -> build_balanced E.Plus terms
    in
    let replacements = Nodes.create 64 in
    let linear_edges = ref [] and ring_edges = ref [] and nonlinear = ref false in
    let simplify_factor factor =
      match ring_polynomial_candidate cost factor with
      | Some candidate when cost candidate < cost factor ->
          ring_edges := (factor, candidate) :: !ring_edges;
          candidate
      | _ -> factor
    in
    let rec substitute expression =
      match Nodes.find_opt replacements expression with
      | Some result -> result
      | None ->
          let result =
            if pure_bitwise expression then (
              let result = expansion expression in
              if not (E.is_equal expression result) then
                linear_edges := (expression, result) :: !linear_edges;
              result)
            else
              match expression with
              | E.Unary { f; x; _ } -> E.unary f (substitute x)
              | E.Binary { f = E.Mul; x; y; _ } ->
                  let x = simplify_factor (substitute x)
                  and y = simplify_factor (substitute y) in
                  if Option.is_none (constant_value x) && Option.is_none (constant_value y)
                  then nonlinear := true;
                  E.binary E.Mul x y
              | E.Binary { f; x; y; _ } -> E.binary f (substitute x) (substitute y)
              | E.Ite { c; t; e; _ } -> E.ite (substitute c) (substitute t) (substitute e)
              | node -> node
          in
          Nodes.add replacements expression result;
          result
    in
    try
      let substituted = substitute expression in
      if not !nonlinear || List.length !linear_edges > 64 then None
      else
        match
          ring_polynomial_candidate ~max_operations:200_000
            ~max_monomials:4096 ~max_degree:16 cost substituted
        with
        | None -> None
        | Some polynomial ->
            let compact =
              if atom_count <= 8 then
                linear_candidates ~max_atoms:8 cost polynomial
                |> List.sort (fun left right -> Int.compare (cost left) (cost right))
                |> function head :: _ -> head | [] -> polynomial
              else polynomial
            in
            if cost compact >= cost expression then None
            else
              Some
                (compact, List.rev !linear_edges,
                 List.rev ((substituted, polynomial) :: !ring_edges),
                 if E.is_equal compact polynomial then [] else [ polynomial, compact ])
    with Ring_candidate_too_complex -> None

let nonlinear_poly_candidate cost expression =
  match minterm_ring_poly_candidate cost expression with
  | Some _ as candidate -> candidate
  | None ->
      if cost expression <= 2048
         && Greysynth_utils.Utils.dag_size_bounded ~limit:256 expression <= 256
      then polysim_candidate cost expression
      else None

let pair_complementary_atoms cost expression =
  if cost expression > 4096 then None else
  let width = E.sizeof expression in
  let atoms = Nodes.create 16 in
  let rec bitwise = function
    | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
    | E.Unary { f = E.Not; x; _ } -> bitwise x
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } -> bitwise x; bitwise y
    | atom -> Nodes.replace atoms atom ()
  and inspect = function
    | E.Unary { f = E.Not; _ } as value -> bitwise value
    | E.Binary { f = (E.And | E.Or | E.Xor); _ } as value -> bitwise value
    | E.Unary { x; _ } -> inspect x
    | E.Binary { x; y; _ } -> inspect x; inspect y
    | E.Ite { c; t; e; _ } -> inspect c; inspect t; inspect e
    | _ -> ()
  in
  inspect expression;
  let atoms = Nodes.fold (fun atom () result -> atom :: result) atoms []
    |> List.filter (fun atom -> E.sizeof atom = width)
    |> List.sort E.compare |> Array.of_list in
  if Array.length atoms < 2 || Array.length atoms > 12
     || Greysynth_utils.Utils.dag_size_bounded ~limit:512 expression > 512
  then None
  else
    let replacements = Nodes.create 8 and ring_edges = ref []
    and linear_edges = ref [] in
    let fill = constant width (Z.pred (Z.shift_left Z.one width)) in
    let complement atom = E.unary E.Not atom in
    let negative atom = E.binary E.Minus (E.unary E.Minus atom) (integer width 1) in
    let pair left right =
      if Nodes.mem replacements left || Nodes.mem replacements right then ()
      else
        let sum = E.binary E.Plus left right in
        match ring_polynomial_candidate cost sum with
        | Some candidate when E.is_equal candidate fill ->
            let source, base =
              if cost right > cost (complement left) then right, left
              else if cost left > cost (complement right) then left, right
              else if E.compare left right <= 0 then right, left else left, right
            in
            let algebraic = negative base and replacement = complement base in
            Nodes.add replacements source replacement;
            ring_edges := (source, algebraic) :: !ring_edges;
            linear_edges := (algebraic, replacement) :: !linear_edges
        | _ -> ()
    in
    for i = 0 to Array.length atoms - 1 do
      for j = i + 1 to Array.length atoms - 1 do
        pair atoms.(i) atoms.(j)
      done
    done;
    if Nodes.length replacements = 0 then None
    else
      let memo = Nodes.create 64 in
      let rec rewrite node =
        match Nodes.find_opt replacements node with
        | Some result -> result
        | None ->
            match Nodes.find_opt memo node with
            | Some result -> result
            | None ->
                let result =
                  match node with
                  | E.Unary { f; x; _ } -> E.unary f (rewrite x)
                  | E.Binary { f; x; y; _ } -> E.binary f (rewrite x) (rewrite y)
                  | E.Ite { c; t; e; _ } -> E.ite (rewrite c) (rewrite t) (rewrite e)
                  | value -> value
                in
                Nodes.add memo node result;
                result
      in
      let candidate = rewrite expression in
      if cost candidate >= cost expression then None
      else Some (candidate, List.rev !ring_edges, List.rev !linear_edges)

let correlated_null_candidate cost expression =
  if cost expression > 4096
     || Greysynth_utils.Utils.dag_size_bounded ~limit:512 expression > 512
  then None else
  let ring_edges = ref [] and linear_edges = ref [] and changed = ref false in
  let canonical_memo = Nodes.create 32 in
  let rec canonical_ac node =
    match Nodes.find_opt canonical_memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Unary { f; x; _ } -> E.unary f (canonical_ac x)
          | E.Binary { f = (E.Plus | E.Mul | E.And | E.Or | E.Xor as f); x; y; _ } ->
              let x = canonical_ac x and y = canonical_ac y in
              if E.compare x y <= 0 then E.binary f x y else E.binary f y x
          | E.Binary { f; x; y; _ } -> E.binary f (canonical_ac x) (canonical_ac y)
          | value -> value
        in
        Nodes.add canonical_memo node result;
        result
  in
  let memo = Nodes.create 64 in
  let rec rewrite node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        let rebuilt =
          match node with
          | E.Unary { f; x; _ } -> E.unary f (rewrite x)
          | E.Binary { f; x; y; _ } -> E.binary f (rewrite x) (rewrite y)
          | E.Ite { c; t; e; _ } -> E.ite (rewrite c) (rewrite t) (rewrite e)
          | value -> value
        in
        let result =
          match rebuilt with
          | E.Unary { f = E.Minus;
                      x = E.Binary { f = E.Or; x = left; y = right; _ }; _ } ->
              let original_left = left and original_right = right in
              let left = canonical_ac left and right = canonical_ac right in
              let relation = E.binary E.Plus left right in
              (match ring_polynomial_candidate cost relation with
              | Some zero when E.is_equal zero (zeros (E.sizeof node)) ->
                  let normalized = E.unary E.Minus (E.binary E.Or left right) in
                  let injected = E.binary E.Plus normalized relation in
                  let candidate = E.binary E.And left right in
                  if not (E.is_equal original_left left) then
                    linear_edges := (original_left, left) :: !linear_edges;
                  if not (E.is_equal original_right right) then
                    linear_edges := (original_right, right) :: !linear_edges;
                  ring_edges := (normalized, injected) :: !ring_edges;
                  linear_edges := (injected, candidate) :: !linear_edges;
                  changed := true;
                  candidate
              | _ -> rebuilt)
          | _ -> rebuilt
        in
        Nodes.add memo node result;
        result
  in
  let candidate = rewrite expression in
  if not !changed || cost candidate >= cost expression then None
  else Some (candidate, List.rev !ring_edges, List.rev !linear_edges)

let reduce_univariate_null_polynomial cost expression =
  let width = E.sizeof expression and maximum_degree = 8 in
  let modulus = Z.shift_left Z.one width in
  let normalize value =
    let value = Z.erem value modulus in
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let zero_poly () = Array.make (maximum_degree + 1) Z.zero in
  let add left right = Array.init (maximum_degree + 1)
      (fun degree -> normalize (Z.add left.(degree) right.(degree))) in
  let neg value = Array.map (fun coefficient -> normalize (Z.neg coefficient)) value in
  let mul left right =
    let result = zero_poly () in
    for i = 0 to maximum_degree do
      for j = 0 to maximum_degree - i do
        result.(i + j) <- normalize
            (Z.add result.(i + j) (Z.mul left.(i) right.(j)))
      done
    done;
    result
  in
  let variable = ref None and invalid = ref false in
  let rec parse = function
    | E.Cst value -> let result = zero_poly () in result.(0) <- Bitvector.value_of value; result
    | E.Var _ as value ->
        (match !variable with
        | None -> variable := Some value
        | Some previous when E.is_equal previous value -> ()
        | Some _ -> invalid := true);
        let result = zero_poly () in result.(1) <- Z.one; result
    | E.Unary { f = E.Minus; x; _ } -> neg (parse x)
    | E.Binary { f = E.Plus; x; y; _ } -> add (parse x) (parse y)
    | E.Binary { f = E.Minus; x; y; _ } -> add (parse x) (neg (parse y))
    | E.Binary { f = E.Mul; x; y; _ } -> mul (parse x) (parse y)
    | _ -> invalid := true; zero_poly ()
  in
  let powers = parse expression in
  let degree = ref 0 in
  Array.iteri (fun index coefficient -> if not (Z.equal coefficient Z.zero) then degree := index) powers;
  match !variable with
  | None -> None
  | Some _ when !invalid || !degree < 2 || !degree > maximum_degree -> None
  | Some variable ->
      let stirling = Array.make_matrix (maximum_degree + 1) (maximum_degree + 1) Z.zero in
      stirling.(0).(0) <- Z.one;
      for n = 1 to maximum_degree do
        for k = 1 to n do
          stirling.(n).(k) <- Z.add stirling.(n - 1).(k - 1)
              (Z.mul (Z.of_int k) stirling.(n - 1).(k))
        done
      done;
      let falling_coefficients = Array.make (maximum_degree + 1) Z.zero in
      for k = 0 to !degree do
        for power = k to !degree do
          falling_coefficients.(k) <- normalize
              (Z.add falling_coefficients.(k)
                 (Z.mul powers.(power) stirling.(power).(k)))
        done
      done;
      let falling degree =
        let rec build index result =
          if index = degree then result
          else
            let factor =
              if index = 0 then variable
              else E.binary E.Minus variable (integer width index)
            in
            build (index + 1)
              (match result with None -> Some factor
               | Some product -> Some (E.binary E.Mul product factor))
        in
        Option.get (build 0 None)
      in
      let dropped = ref [] and kept = ref [] in
      for k = 0 to !degree do
        let coefficient = falling_coefficients.(k) in
        if not (Z.equal coefficient Z.zero) then
          let basis = if k = 0 then integer width 1 else falling k in
          let term =
            if Z.equal coefficient Z.one then basis
            else E.binary E.Mul (constant width coefficient) basis
          in
          if k >= 2 then (
            let rec v2 power total =
              if power > k then total else v2 (power * 2) (total + (k / power))
            in
            let divisor = Z.shift_left Z.one (max 0 (width - v2 2 0)) in
            if Z.equal (Z.erem coefficient divisor) Z.zero then dropped := term :: !dropped
            else kept := term :: !kept)
          else kept := term :: !kept
      done;
      if !dropped = [] then None
      else
        let sum = function
          | [] -> zeros width
          | head :: tail -> List.fold_left (E.binary E.Plus) head tail
        in
        let reduced = sum (List.rev !kept) in
        let expanded = sum (List.rev_append !kept !dropped) in
        if cost reduced >= cost expression then None
        else Some (reduced, List.map (fun term -> term, zeros width) !dropped,
                   [ expression, expanded ])

module ModularMonomial = struct
  type t = (E.t * int) list
  let compare left right =
    List.compare
      (fun (left_atom, left_exponent) (right_atom, right_exponent) ->
        let order = E.compare left_atom right_atom in
        if order <> 0 then order else Int.compare left_exponent right_exponent)
      left right
end
module ModularPolynomial = Map.Make (ModularMonomial)

let reduce_modular_polynomial ?(min_degree = 8) ?(allow_atoms = false)
    cost expression =
  let rec pure_ring = function
    | E.Var _ | E.Cst _ -> true
    | E.Unary { f = E.Minus; x; _ } -> pure_ring x
    | E.Binary { f = (E.Plus | E.Minus | E.Mul); x; y; _ } ->
        pure_ring x && pure_ring y
    | _ -> false
  in
  let width = E.sizeof expression in
  let allow_opaque =
    allow_atoms || (cost expression > 2000
    && List.length (Sample_evaluator.variables_of_expr expression) <= 2)
  in
  if width > 128 || (not (pure_ring expression) && not allow_opaque) then None
  else
    let max_degree = 66 and max_monomials = 8192 and max_ops = 1_000_000 in
    let operations = ref 0 in
    let modulus = Z.shift_left Z.one width in
    let normalize value =
      let value = Z.erem value modulus in
      if Z.sign value < 0 then Z.add value modulus else value
    in
    let tick () =
      incr operations;
      if !operations > max_ops then raise Ring_candidate_too_complex;
      if !operations mod 256 = 0 then check_timeout ()
    in
    let total_degree monomial =
      List.fold_left (fun total (_, exponent) -> total + exponent) 0 monomial
    in
    let add_term monomial coefficient polynomial =
      tick ();
      if total_degree monomial > max_degree
         || List.exists (fun (_, exponent) -> exponent < 1 || exponent > max_degree) monomial
      then raise Ring_candidate_too_complex;
      let coefficient = normalize coefficient in
      let old = Option.value (ModularPolynomial.find_opt monomial polynomial) ~default:Z.zero in
      let value = normalize (Z.add old coefficient) in
      let result =
        if Z.equal value Z.zero then ModularPolynomial.remove monomial polynomial
        else ModularPolynomial.add monomial value polynomial
      in
      if ModularPolynomial.cardinal result > max_monomials then
        raise Ring_candidate_too_complex;
      result
    in
    let add left right = ModularPolynomial.fold add_term left right in
    let neg polynomial =
      ModularPolynomial.fold
        (fun monomial coefficient result -> add_term monomial (Z.neg coefficient) result)
        polynomial ModularPolynomial.empty
    in
    let merge_monomials left right =
      let atoms = Nodes.create (List.length left + List.length right) in
      List.iter
        (fun (atom, exponent) ->
          Nodes.replace atoms atom
            (exponent + Option.value (Nodes.find_opt atoms atom) ~default:0))
        (left @ right);
      Nodes.fold (fun atom exponent result -> (atom, exponent) :: result) atoms []
      |> List.sort (fun (left, _) (right, _) -> E.compare left right)
    in
    let mul left right =
      ModularPolynomial.fold
        (fun left_monomial left_coefficient result ->
          ModularPolynomial.fold
            (fun right_monomial right_coefficient result ->
              add_term (merge_monomials left_monomial right_monomial)
                (Z.mul left_coefficient right_coefficient) result)
            right result)
        left ModularPolynomial.empty
    in
    let memo = Nodes.create 128 in
    let has_non_variable_atom = ref false in
    let rec parse expression =
      match Nodes.find_opt memo expression with
      | Some result -> result
      | None ->
          let result =
            match expression with
            | E.Cst value ->
                add_term [] (Bitvector.value_of value) ModularPolynomial.empty
            | E.Unary { f = E.Minus; x; _ } -> neg (parse x)
            | E.Binary { f = E.Plus; x; y; _ } -> add (parse x) (parse y)
            | E.Binary { f = E.Minus; x; y; _ } -> add (parse x) (neg (parse y))
            | E.Binary { f = E.Mul; x; y; _ } -> mul (parse x) (parse y)
            | (E.Var _ as atom) -> ModularPolynomial.singleton [ atom, 1 ] Z.one
            | atom ->
                has_non_variable_atom := true;
                ModularPolynomial.singleton [ atom, 1 ] Z.one
          in
          Nodes.add memo expression result;
          result
    in
    let v2_factorial n =
      let rec loop power total =
        if power > n then total else loop (power * 2) (total + (n / power))
      in loop 2 0
    in
    try
      let power = parse expression in
      let observed_degree =
        ModularPolynomial.fold
          (fun monomial _ maximum -> max maximum (total_degree monomial))
          power 0
      in
      let opaque_allowed =
        allow_atoms || not !has_non_variable_atom
        || (cost expression > 2000
            && List.length (Sample_evaluator.variables_of_expr expression) <= 2)
      in
      if observed_degree < min_degree || not opaque_allowed then None
      else if ModularPolynomial.is_empty power then
        Some (zeros width, [], [ expression, zeros width ])
      else
        let stirling2 = Array.make_matrix (max_degree + 1) (max_degree + 1) Z.zero in
        let stirling1 = Array.make_matrix (max_degree + 1) (max_degree + 1) Z.zero in
        stirling2.(0).(0) <- Z.one;
        stirling1.(0).(0) <- Z.one;
        for n = 1 to max_degree do
          for k = 1 to n do
            stirling2.(n).(k) <- normalize
                (Z.add stirling2.(n - 1).(k - 1)
                   (Z.mul (Z.of_int k) stirling2.(n - 1).(k)));
            stirling1.(n).(k) <- normalize
                (Z.sub stirling1.(n - 1).(k - 1)
                   (Z.mul (Z.of_int (n - 1)) stirling1.(n - 1).(k)))
          done
        done;
        let expand_basis table polynomial =
          ModularPolynomial.fold
            (fun monomial coefficient result ->
              let rec expand result partial scale = function
                | [] -> add_term (List.rev partial) (Z.mul coefficient scale) result
                | (atom, exponent) :: rest ->
                    let accumulated = ref result in
                    for degree = 1 to exponent do
                      let factor = table.(exponent).(degree) in
                      if not (Z.equal factor Z.zero) then
                        accumulated := expand !accumulated ((atom, degree) :: partial)
                            (normalize (Z.mul scale factor)) rest
                    done;
                    !accumulated
              in
              if monomial = [] then add_term [] coefficient result
              else expand result [] Z.one monomial)
            polynomial ModularPolynomial.empty
        in
        let falling = expand_basis stirling2 power in
        let reduced_falling =
          ModularPolynomial.fold
            (fun monomial coefficient result ->
              let valuation =
                List.fold_left
                  (fun total (_, degree) -> total + v2_factorial degree) 0 monomial
              in
              let bits = max 0 (width - valuation) in
              let reduced =
                if bits = 0 then Z.zero
                else
                  let basis_modulus = Z.shift_left Z.one bits in
                  let unsigned = Z.erem coefficient basis_modulus in
                  if Z.gt unsigned (Z.shift_right basis_modulus 1)
                  then Z.sub unsigned basis_modulus else unsigned
              in
              add_term monomial reduced result)
            falling ModularPolynomial.empty
        in
        let reduced_power = expand_basis stirling1 reduced_falling in
        let rec power_expression atom exponent =
          if exponent = 1 then atom
          else if exponent mod 2 = 0 then
            let half = power_expression atom (exponent / 2) in E.binary E.Mul half half
          else E.binary E.Mul atom (power_expression atom (exponent - 1))
        in
        let terms =
          ModularPolynomial.bindings reduced_power
          |> List.map (fun (monomial, coefficient) ->
                 let body =
                   match monomial with
                   | [] -> None
                   | terms ->
                       terms
                       |> List.map (fun (atom, exponent) -> power_expression atom exponent)
                       |> function head :: tail -> Some (List.fold_left (E.binary E.Mul) head tail)
                                   | [] -> None
                 in
                 let signed =
                   if Z.gt coefficient (Z.shift_right modulus 1)
                   then Z.sub coefficient modulus else coefficient
                 in
                 match body with
                 | None -> constant width signed
                 | Some body when Z.equal signed Z.one -> body
                 | Some body when Z.equal signed (Z.neg Z.one) -> E.unary E.Minus body
                 | Some body when Z.sign signed < 0 ->
                     E.unary E.Minus
                       (E.binary E.Mul (constant width (Z.neg signed)) body)
                 | Some body -> E.binary E.Mul (constant width signed) body)
        in
        let candidate =
          match terms with [] -> zeros width | _ -> build_balanced E.Plus terms
        in
        if cost candidate < cost expression then
          Some (candidate, [], [ expression, candidate ])
        else None
    with Ring_candidate_too_complex -> None

let minterm_polynomial_candidate cost expression =
  Option.bind (minterm_ring_expansion expression expression)
    (fun (equalities, ring_equalities, expanded, _) ->
      Option.bind (ring_polynomial_candidate cost expanded) (fun candidate ->
          if cost candidate >= cost expression then None
          else Some (candidate, equalities, (expanded, candidate) :: ring_equalities)))

let factor_group_steps cost expression =
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
           if order <> 0 then order
           else
             let size_order = Int.compare (cost right) (cost left) in
             if size_order = 0 then E.compare left right else size_order)
    |> (fun factors ->
         let rec take count = function
           | _ when count = 0 -> []
           | [] -> []
           | head :: tail -> head :: take (count - 1) tail
         in
         take 6 factors)
  in
  List.filter_map (fun (factor, _) ->
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
        match
          List.find_map
            (fun candidate ->
              if not (Rewrite.samples_agree cofactor candidate) then None
              else
                Option.map (fun proof -> (candidate, proof))
                  (minterm_ring_proof cofactor candidate))
            candidates
        with
        | Some _ as result -> result
        | None -> Some (cofactor, ([], []))
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

let factor_group_candidate cost expression =
  let finish current equalities ring_equalities =
    if E.is_equal current expression then None
    else
      let refinements =
        Option.to_list (ring_polynomial_candidate cost current)
        @ linear_candidates cost current
        |> List.filter (fun candidate ->
               cost candidate < cost current && Rewrite.samples_agree current candidate)
        |> List.sort (fun left right -> Int.compare (cost left) (cost right))
      in
      match refinements with
      | candidate :: _ ->
          let next_equalities, next_ring =
            match minterm_ring_proof current candidate with
            | Some proof -> proof
            | None ->
                (match ring_polynomial_candidate cost current with
                | Some ring when E.is_equal ring candidate -> ([], [ current, candidate ])
                | _ -> ([ current, candidate ], []))
          in
          Some (candidate, equalities @ next_equalities,
                ring_equalities @ next_ring)
      | [] -> Some (current, equalities, ring_equalities)
  in
  let rec loop remaining current equalities ring_equalities =
    let terminal = finish current equalities ring_equalities in
    if remaining = 0 then terminal
    else
      let descendants =
        factor_group_steps cost current
        |> List.filter_map (fun (candidate, next_equalities, next_ring) ->
               if cost candidate >= cost current then None
               else
                 loop (remaining - 1) candidate
                   (equalities @ next_equalities) (ring_equalities @ next_ring))
      in
      List.fold_left
        (fun best candidate ->
          match best with
          | None -> Some candidate
          | Some (previous, _, _) ->
              let expression, _, _ = candidate in
              if cost expression < cost previous then Some candidate else best)
        terminal descendants
  in
  loop 6 expression [] []

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

let complement_linear_candidate cost expression =
  let equalities = ref [] in
  let rec rewrite expression =
    let rebuilt =
      match expression with
      | E.Unary { f; x; _ } -> E.unary f (rewrite x)
      | E.Binary { f; x; y; _ } -> E.binary f (rewrite x) (rewrite y)
      | E.Ite { c; t; e; _ } -> E.ite (rewrite c) (rewrite t) (rewrite e)
      | expression -> expression
    in
    let complement =
      match rebuilt with
      | E.Unary { f = E.Not;
                  x = E.Binary { f = E.Minus; x = base; y = one; _ }; _ }
        when is_number Z.one one -> Some (E.unary E.Minus base)
      | E.Unary { f = E.Not; x = E.Unary { f = E.Minus; x = base; _ }; _ } ->
          Some (E.binary E.Minus base (integer (E.sizeof base) 1))
      | E.Binary { f = E.Plus; x = E.Unary { f = E.Not; x = base; _ }; y = one; _ }
        when is_number Z.one one -> Some (E.unary E.Minus base)
      | E.Binary { f = E.Plus; x = one; y = E.Unary { f = E.Not; x = base; _ }; _ }
        when is_number Z.one one -> Some (E.unary E.Minus base)
      | E.Binary { f = E.Minus; x = E.Unary { f = E.Minus; x = base; _ };
                   y = one; _ }
        when is_number Z.one one -> Some (E.unary E.Not base)
      | _ -> None
    in
    match complement with
    | Some candidate -> equalities := (rebuilt, candidate) :: !equalities; candidate
    | None ->
        (match product_partition_candidate rebuilt with
        | Some (candidate, edges) when cost candidate < cost rebuilt ->
            equalities := edges @ !equalities;
            candidate
        | _ -> rebuilt)
  in
  let transformed = rewrite expression in
  match
    linear_candidates cost transformed
    |> List.sort (fun left right -> Int.compare (cost left) (cost right))
  with
  | candidate :: _ when cost candidate < cost expression ->
      let proof_equalities, ring_equalities =
        Option.value (minterm_ring_proof transformed candidate)
          ~default:([ transformed, candidate ], [])
      in
      Some (candidate, List.rev_append !equalities proof_equalities, ring_equalities)
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

let first_some left right = match left with Some _ -> left | None -> right

let bitsliced_ring_proof original candidate =
  let width = E.sizeof original in
  let masked_variable = function
    | E.Binary { f = E.And; x = (E.Var _ as variable); y = E.Cst mask; _ }
    | E.Binary { f = E.And; x = E.Cst mask; y = (E.Var _ as variable); _ } ->
        Some (variable, Bitvector.value_of mask)
    | _ -> None
  in
  let candidate_parts =
    match candidate with
    | E.Binary { f = E.Xor; x = masked; y = E.Cst constant; _ }
    | E.Binary { f = E.Xor; x = E.Cst constant; y = masked; _ } ->
        Option.map
          (fun (variable, mask) -> variable, mask, Bitvector.value_of constant)
          (masked_variable masked)
    | _ -> None
  in
  Option.bind candidate_parts (fun (variable, candidate_mask, xor_constant) ->
      let masks = ref [ candidate_mask; xor_constant ] in
      let valid = ref true in
      let rec collect = function
        | expression ->
            (match masked_variable expression with
            | Some (other, mask) when E.is_equal variable other -> masks := mask :: !masks
            | Some _ -> valid := false
            | None ->
                match expression with
                | E.Unary { x; _ } -> collect x
                | E.Binary { x; y; _ } -> collect x; collect y
                | E.Ite { c; t; e; _ } -> collect c; collect t; collect e
                | (E.Var _ as other) when not (E.is_equal variable other) -> valid := false
                | _ -> ())
      in
      collect original;
      if not !valid then None
      else
        let signatures = Hashtbl.create width in
        for bit = 0 to width - 1 do
          let signature =
            List.map (fun mask -> Z.testbit mask bit) !masks
            |> List.map string_of_bool |> String.concat ""
          in
          let block = Option.value (Hashtbl.find_opt signatures signature) ~default:Z.zero in
          Hashtbl.replace signatures signature
            (Z.logor block (Z.shift_left Z.one bit))
        done;
        let blocks = Hashtbl.fold (fun _ block result -> block :: result) signatures [] in
        let masked block = E.binary E.And variable (constant width block) in
        let sum = function
          | [] -> zeros width
          | head :: tail -> List.fold_left (E.binary E.Plus) head tail
        in
        let blocks_for mask =
          List.filter (fun block -> not (Z.equal Z.zero (Z.logand block mask))) blocks
        in
        let edges = ref [] and seen = Nodes.create 32 in
        let rec expand = function
          | expression ->
              (match masked_variable expression with
              | Some (other, mask) when E.is_equal variable other ->
                  let expanded = blocks_for mask |> List.map masked |> sum in
                  if not (E.is_equal expression expanded) && not (Nodes.mem seen expression) then (
                    Nodes.add seen expression ();
                    edges := (expression, expanded) :: !edges);
                  expanded
              | _ ->
                  match expression with
                  | E.Unary { f; x; _ } -> E.unary f (expand x)
                  | E.Binary { f; x; y; _ } -> E.binary f (expand x) (expand y)
                  | E.Ite { c; t; e; _ } -> E.ite (expand c) (expand t) (expand e)
                  | expression -> expression)
        in
        let expanded_original = expand original in
        let positive, negative =
          blocks_for candidate_mask
          |> List.partition (fun block -> Z.equal Z.zero (Z.logand block xor_constant))
        in
        let expanded_candidate =
          let base = constant width xor_constant in
          let with_positive =
            List.fold_left (fun result block -> E.binary E.Plus result (masked block))
              base positive
          in
          List.fold_left (fun result block -> E.binary E.Minus result (masked block))
            with_positive negative
        in
        let equalities =
          if E.is_equal candidate expanded_candidate then !edges
          else (candidate, expanded_candidate) :: !edges
        in
        Some (equalities, [ expanded_original, expanded_candidate ]))

type local_candidate = {
  expr : E.t;
  pass : string;
  equalities : (E.t * E.t) list;
  ring_equalities : (E.t * E.t) list;
  poly_equalities : (E.t * E.t) list;
  linear_mba_equalities : (E.t * E.t) list;
  semilinear_mba_equalities : (E.t * E.t) list;
  allow_equal_cost : bool;
}

let local_candidates ~cost ~(constants : Sample_evaluator.t)
    ?(heavy_additive = true) ~ac expression =
  let direct pass ?(allow_equal_cost = false) candidate =
    { expr = candidate; pass; equalities = [ expression, candidate ];
      ring_equalities = []; poly_equalities = []; linear_mba_equalities = [];
      semilinear_mba_equalities = []; allow_equal_cost }
  in
  let ring pass ?(allow_equal_cost = false) candidate =
    { expr = candidate; pass; equalities = [];
      ring_equalities = [ expression, candidate ]; poly_equalities = [];
      linear_mba_equalities = []; semilinear_mba_equalities = []; allow_equal_cost }
  in
  let candidates = ref [] in
  let bitsliced_fast =
    if heavy_additive then bitsliced_candidate cost expression else None
  in
  Option.iter
    (fun candidate ->
      let equalities, ring_equalities =
        Option.value (bitsliced_ring_proof expression candidate)
          ~default:(Option.value (minterm_ring_proof expression candidate)
                      ~default:([], []))
      in
      candidates :=
        { expr = candidate; pass = "bitsliced"; equalities; ring_equalities;
          poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    bitsliced_fast;
  if Option.is_none bitsliced_fast then (
  List.iter (fun candidate -> candidates := direct "peephole" candidate :: !candidates)
    (peepholes constants.eval expression);
  Option.iter
    (fun candidate -> candidates := direct "known-bits" candidate :: !candidates)
    (known_bits_candidate cost expression);
  Option.iter
    (fun candidate ->
      candidates :=
        { expr = candidate; pass = "semilinear-mba"; equalities = [];
          ring_equalities = []; poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = [ expression, candidate ];
          allow_equal_cost = false } :: !candidates)
    (semilinear_mba_candidate cost expression);
  Option.iter
    (fun candidate -> candidates := direct "power2-pullout" candidate :: !candidates)
    (power2_pullout_candidate cost expression);
  Option.iter
    (fun candidate -> candidates := direct "demand-bits" candidate :: !candidates)
    (demand_bits_candidate cost expression);
  if heavy_additive then (
  if ac then
    List.iter
      (fun candidate ->
        let proposal =
          match expression with
          | E.Binary { f = (E.Plus | E.Mul); _ } ->
              ring "ac" ~allow_equal_cost:true candidate
          | _ -> direct "ac" ~allow_equal_cost:true candidate
        in
        candidates := proposal :: !candidates)
      (canonical_candidates expression);
  if cost expression >= 5 then (
    Option.iter
      (fun (candidate, linear_mba_equalities, ring_equalities,
            final_linear_equalities) ->
        candidates :=
          { expr = candidate; pass = "minterm-ring-poly"; equalities = [];
            ring_equalities; poly_equalities = [];
            linear_mba_equalities = linear_mba_equalities @ final_linear_equalities;
            semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
      (if cost expression > 256 then nonlinear_poly_candidate cost expression else None);
    Option.iter
      (fun (candidate, equalities, ring_equalities) ->
        candidates :=
          { expr = candidate; pass = "falling-null"; equalities; ring_equalities;
            poly_equalities = []; linear_mba_equalities = [];
            semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
      (reduce_univariate_null_polynomial cost expression);
    Option.iter
      (fun candidate -> candidates := ring "ring-polynomial" candidate :: !candidates)
      (ring_polynomial_candidate cost expression));
  Option.iter
    (fun (candidate, ring_equalities, linear_mba_equalities) ->
      candidates :=
        { expr = candidate; pass = "complementary-atoms"; equalities = [];
          ring_equalities; poly_equalities = []; linear_mba_equalities;
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (pair_complementary_atoms cost expression);
  Option.iter
    (fun (candidate, ring_equalities, linear_mba_equalities) ->
      candidates :=
        { expr = candidate; pass = "correlated-null"; equalities = [];
          ring_equalities; poly_equalities = []; linear_mba_equalities;
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (correlated_null_candidate cost expression);
  Option.iter
    (fun candidate ->
      candidates :=
        { expr = candidate; pass = "disjoint-components"; equalities = [];
          ring_equalities = []; poly_equalities = [];
          linear_mba_equalities = [ expression, candidate ];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (disjoint_component_candidate cost expression);
  Option.iter
    (fun (candidate, equalities, ring_equalities) ->
      candidates :=
        { expr = candidate; pass = "factor-group"; equalities; ring_equalities;
          poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (factor_group_candidate cost expression);
  Option.iter
    (fun (candidate, equalities, ring_equalities) ->
      candidates :=
        { expr = candidate; pass = "minterm-polynomial"; equalities; ring_equalities;
          poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (minterm_polynomial_candidate cost expression);
  Option.iter
    (fun (candidate, equalities) ->
      candidates :=
        { expr = candidate; pass = "product-partition"; equalities;
          ring_equalities = []; poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (product_partition_candidate expression);
  Option.iter
    (fun candidate ->
      let equalities, ring_equalities =
        Option.value (bitsliced_ring_proof expression candidate)
          ~default:(Option.value (minterm_ring_proof expression candidate)
                      ~default:([], []))
      in
      candidates :=
        { expr = candidate; pass = "bitsliced"; equalities; ring_equalities;
          poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (bitsliced_candidate cost expression);
  if cost expression >= 4 then
    List.iter
      (fun candidate ->
        let variable_count =
          List.length (Sample_evaluator.variables_of_expr expression)
        in
        let equalities, ring_equalities, linear_mba_equalities =
          if variable_count >= 3 then [], [], [ expression, candidate ]
          else
            let equalities, ring_equalities =
              Option.value (minterm_ring_proof expression candidate)
                ~default:(Option.value (complement_product_steps expression candidate)
                            ~default:([ expression, candidate ], []))
            in
            equalities, ring_equalities, []
        in
        candidates :=
          { expr = candidate; pass = "linear-mba"; equalities;
            ring_equalities; poly_equalities = []; linear_mba_equalities;
            semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
      (linear_candidates cost expression));
  );
  let offer_nonmonotonic ?(ring_rule = true) pass candidate =
    let proposal =
      if ring_rule then ring pass ~allow_equal_cost:true candidate
      else direct pass ~allow_equal_cost:true candidate
    in
    candidates := proposal :: !candidates
  in
  (match expression with
  | E.Binary { f = E.Mul; x = term; y = E.Cst scale; _ }
  | E.Binary { f = E.Mul; x = E.Cst scale; y = term; _ } ->
      let value = Bitvector.value_of scale in
      if Z.sign value > 0 && Z.popcount value = 1 then
        let amount = Z.trailing_zeros value in
        if amount >= 1 && amount < E.sizeof term then (
          offer_nonmonotonic ~ring_rule:false "bridge-shift"
            (E.binary E.Lsl term (integer (E.sizeof term) amount));
          if amount = 1 then
            offer_nonmonotonic "bridge-add" (E.binary E.Plus term term))
  | E.Binary { f = E.Lsl; x = term; y = E.Cst amount; _ } ->
      let amount = bounded_count (E.sizeof term) amount in
      if amount >= 1 && amount < E.sizeof term then
        offer_nonmonotonic ~ring_rule:false "bridge-mul"
          (E.binary E.Mul term (constant (E.sizeof term) (Z.shift_left Z.one amount)))
  | _ -> ());
  if cost expression <= 9 then
    (match expression with
    | E.Binary { f = E.Mul; x = factor;
                 y = E.Binary { f = (E.Plus | E.Minus as op); x; y; _ }; _ } ->
        offer_nonmonotonic "expand-distribute"
          (E.binary op (E.binary E.Mul factor x) (E.binary E.Mul factor y))
    | E.Binary { f = E.Mul;
                 x = E.Binary { f = (E.Plus | E.Minus as op); x; y; _ };
                 y = factor; _ } ->
        offer_nonmonotonic "expand-distribute"
          (E.binary op (E.binary E.Mul x factor) (E.binary E.Mul y factor))
    | E.Unary { f = E.Minus; x = E.Binary { f = E.Plus; x; y; _ }; _ } ->
        offer_nonmonotonic "expand-negation"
          (E.binary E.Minus (E.unary E.Minus x) y)
    | E.Unary { f = E.Minus; x = E.Binary { f = E.Minus; x; y; _ }; _ } ->
        offer_nonmonotonic "expand-negation" (E.binary E.Minus y x)
    | _ -> ());
  let seen = Nodes.create 32 in
  List.rev !candidates
  |> List.filter (fun candidate ->
         let allowed =
           candidate.allow_equal_cost
           || cost candidate.expr < cost expression
         in
         if not allowed || E.is_equal candidate.expr expression
            || Nodes.mem seen candidate.expr then false
         else (Nodes.add seen candidate.expr (); true))

let linear_mba_compatible expression =
  let width = E.sizeof expression in
  let memo = Nodes.create 128 in
  let rec inspect node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Var variable -> variable.size = width
          | E.Cst value -> Bitvector.size_of value = width
          | E.Unary { f = (E.Not | E.Minus); x; _ } -> inspect x
          | E.Binary { f = (E.Plus | E.Minus | E.And | E.Or | E.Xor); x; y; _ } ->
              inspect x && inspect y
          | E.Binary { f = E.Mul; x; y; _ } ->
              (Option.is_some (constant_value x) && inspect y)
              || (Option.is_some (constant_value y) && inspect x)
          | E.Binary { f = E.Lsl; x; y = E.Cst _; _ } -> inspect x
          | _ -> false
        in
        Nodes.add memo node result;
        result
  in
  inspect expression

let reduce_quotient_polynomial_dag cost expression =
  let width = E.sizeof expression in
  if width > 128 then None
  else
    let max_monomials = 8192 and max_ops = 2_000_000 and max_visited = 32_768 in
    let operations = ref 0 and visited = ref 0 in
    let modulus = Z.shift_left Z.one width in
    let normalize value =
      let value = Z.erem value modulus in
      if Z.sign value < 0 then Z.add value modulus else value
    in
    let tick () =
      incr operations;
      if !operations > max_ops then raise Ring_candidate_too_complex;
      if !operations mod 512 = 0 then check_timeout ()
    in
    let v2_factorial n =
      let rec loop power total =
        if power > n then total else loop (power * 2) (total + (n / power))
      in loop 2 0
    in
    let rec null_degree degree =
      if v2_factorial degree >= width then degree else null_degree (degree + 1)
    in
    let null_degree = null_degree 1 in
    let max_raw_degree = 2 * (null_degree - 1) in
    let second = Array.make_matrix (max_raw_degree + 1) (max_raw_degree + 1) Z.zero
    and first = Array.make_matrix (null_degree + 1) (null_degree + 1) Z.zero in
    second.(0).(0) <- Z.one;
    first.(0).(0) <- Z.one;
    for n = 1 to max_raw_degree do
      for k = 1 to n do
        second.(n).(k) <- normalize
            (Z.add second.(n - 1).(k - 1)
               (Z.mul (Z.of_int k) second.(n - 1).(k)))
      done
    done;
    for n = 1 to null_degree do
      for k = 1 to n do
        first.(n).(k) <- normalize
            (Z.sub first.(n - 1).(k - 1)
               (Z.mul (Z.of_int (n - 1)) first.(n - 1).(k)))
      done
    done;
    let add_term monomial coefficient polynomial =
      tick ();
      if List.exists
           (fun (_, exponent) -> exponent < 1 || exponent > max_raw_degree)
           monomial
      then raise Ring_candidate_too_complex;
      let coefficient = normalize coefficient in
      let old = Option.value (ModularPolynomial.find_opt monomial polynomial)
          ~default:Z.zero in
      let coefficient = normalize (Z.add old coefficient) in
      let result =
        if Z.equal coefficient Z.zero then ModularPolynomial.remove monomial polynomial
        else ModularPolynomial.add monomial coefficient polynomial
      in
      if ModularPolynomial.cardinal result > max_monomials then
        raise Ring_candidate_too_complex;
      result
    in
    let add left right = ModularPolynomial.fold add_term left right in
    let neg polynomial =
      ModularPolynomial.fold
        (fun monomial coefficient result -> add_term monomial (Z.neg coefficient) result)
        polynomial ModularPolynomial.empty
    in
    let merge left right =
      let exponents = Nodes.create (List.length left + List.length right) in
      List.iter
        (fun (atom, exponent) ->
          Nodes.replace exponents atom
            (exponent + Option.value (Nodes.find_opt exponents atom) ~default:0))
        (left @ right);
      Nodes.fold (fun atom exponent result -> (atom, exponent) :: result) exponents []
      |> List.sort (fun (left, _) (right, _) -> E.compare left right)
    in
    let expand_basis table maximum polynomial =
      ModularPolynomial.fold
        (fun monomial coefficient result ->
          let rec axes partial scale = function
            | [] -> add_term (List.rev partial) (Z.mul coefficient scale)
                      ModularPolynomial.empty
            | (atom, exponent) :: rest ->
                if exponent > maximum then raise Ring_candidate_too_complex;
                let result = ref ModularPolynomial.empty in
                for degree = 1 to exponent do
                  let factor = table.(exponent).(degree) in
                  if not (Z.equal factor Z.zero) then
                    result := add !result
                        (axes ((atom, degree) :: partial)
                           (normalize (Z.mul scale factor)) rest)
                done;
                !result
          in
          add result
            (if monomial = [] then add_term [] coefficient ModularPolynomial.empty
             else axes [] Z.one monomial))
        polynomial ModularPolynomial.empty
    in
    let reduce polynomial =
      let falling = expand_basis second max_raw_degree polynomial in
      let falling =
        ModularPolynomial.fold
          (fun monomial coefficient result ->
            let valuation = List.fold_left
                (fun total (_, degree) -> total + v2_factorial degree) 0 monomial in
            let bits = max 0 (width - valuation) in
            if bits = 0 then result
            else
              let basis_modulus = Z.shift_left Z.one bits in
              let coefficient = Z.erem coefficient basis_modulus in
              let coefficient =
                if Z.gt coefficient (Z.shift_right basis_modulus 1)
                then Z.sub coefficient basis_modulus else coefficient
              in
              add_term monomial coefficient result)
          falling ModularPolynomial.empty
      in
      expand_basis first null_degree falling
    in
    let mul left right =
      let product =
        ModularPolynomial.fold
          (fun lm lc result ->
            ModularPolynomial.fold
              (fun rm rc result -> add_term (merge lm rm) (Z.mul lc rc) result)
              right result)
          left ModularPolynomial.empty
      in
      reduce product
    in
    let memo = Nodes.create 256 in
    let rec parse node =
      match Nodes.find_opt memo node with
      | Some result -> result
      | None ->
          incr visited;
          if !visited > max_visited then raise Ring_candidate_too_complex;
          let result =
            match node with
            | E.Cst value -> add_term [] (Bitvector.value_of value) ModularPolynomial.empty
            | E.Unary { f = E.Minus; x; _ } -> neg (parse x)
            | E.Binary { f = E.Plus; x; y; _ } -> add (parse x) (parse y)
            | E.Binary { f = E.Minus; x; y; _ } ->
                add (parse x) (neg (parse y))
            | E.Binary { f = E.Mul; x; y; _ } -> mul (parse x) (parse y)
            | atom -> ModularPolynomial.singleton [ atom, 1 ] Z.one
          in
          Nodes.add memo node result;
          result
    in
    let rec power atom exponent =
      if exponent = 1 then atom
      else if exponent mod 2 = 0 then
        let half = power atom (exponent / 2) in E.binary E.Mul half half
      else E.binary E.Mul atom (power atom (exponent - 1))
    in
    try
      let polynomial = reduce (parse expression) in
      let terms =
        ModularPolynomial.bindings polynomial
        |> List.map (fun (monomial, coefficient) ->
               let body =
                 match monomial with
                 | [] -> None
                 | factors ->
                     factors |> List.map (fun (atom, exponent) -> power atom exponent)
                     |> function head :: tail -> Some (List.fold_left (E.binary E.Mul) head tail)
                                 | [] -> None
               in
               let signed =
                 if Z.gt coefficient (Z.shift_right modulus 1)
                 then Z.sub coefficient modulus else coefficient
               in
               match body with
               | None -> constant width signed
               | Some body when Z.equal signed Z.one -> body
               | Some body when Z.equal signed (Z.neg Z.one) -> E.unary E.Minus body
               | Some body when Z.sign signed < 0 ->
                   E.unary E.Minus
                     (E.binary E.Mul (constant width (Z.neg signed)) body)
               | Some body -> E.binary E.Mul (constant width signed) body)
      in
      let candidate =
        match terms with [] -> zeros width | _ -> build_balanced E.Plus terms
      in
      if cost candidate < cost expression
      then Some (candidate, [], [ expression, candidate ]) else None
    with Ring_candidate_too_complex -> None

let polysim_poly_mod2w cost expression =
  let width = E.sizeof expression in
  if cost expression > 32_768
     || Greysynth_utils.Utils.dag_size_bounded ~limit:8192 expression > 8192
  then None
  else
    let atom_table = Nodes.create 8 in
    let rec collect_bitwise = function
      | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
      | E.Unary { f = E.Not; x; _ } -> collect_bitwise x
      | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
          collect_bitwise x; collect_bitwise y
      | atom -> Nodes.replace atom_table atom ()
    and collect_ring = function
      | E.Unary { f = E.Minus; x; _ } -> collect_ring x
      | E.Binary { f = (E.Plus | E.Minus | E.Mul); x; y; _ } ->
          collect_ring x; collect_ring y
      | (E.Unary { f = E.Not; _ }
        | E.Binary { f = (E.And | E.Or | E.Xor); _ }) as bitwise ->
          collect_bitwise bitwise
      | E.Cst _ -> ()
      | atom -> Nodes.replace atom_table atom ()
    in
    collect_ring expression;
    let atoms =
      Nodes.fold (fun atom () result -> atom :: result) atom_table []
      |> List.filter (fun atom -> E.sizeof atom = width)
      |> List.sort E.compare |> Array.of_list
    in
    let count = Array.length atoms in
    if count < 1 || count > 4 then None
    else
      let atom_index expression =
        let rec find index =
          if index = count then None
          else if E.is_equal atoms.(index) expression then Some index
          else find (index + 1)
        in
        find 0
      in
      let rec pure_bitwise expression =
        match atom_index expression with
        | Some _ -> true
        | None ->
            match expression with
            | E.Cst value -> Bitvector.is_zeros value || Bitvector.is_fill value
            | E.Unary { f = E.Not; x; _ } -> pure_bitwise x
            | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
                pure_bitwise x && pure_bitwise y
            | _ -> false
      in
      let rec truth assignment expression =
        match atom_index expression with
        | Some index -> assignment land (1 lsl index) <> 0
        | None ->
            match expression with
            | E.Cst value -> Bitvector.is_fill value
            | E.Unary { f = E.Not; x; _ } -> not (truth assignment x)
            | E.Binary { f; x; y; _ } ->
                let x = truth assignment x and y = truth assignment y in
                if f = E.And then x && y
                else if f = E.Or then x || y else x <> y
            | _ -> false
      in
      let modulus = Z.shift_left Z.one width in
      let mask = Z.pred modulus in
      let normalize value = Z.logand value mask in
      let conjunction subset =
        let selected = ref [] in
        for index = 0 to count - 1 do
          if subset land (1 lsl index) <> 0 then
            selected := atoms.(index) :: !selected
        done;
        match List.rev !selected with
        | head :: tail -> List.fold_left (E.binary E.And) head tail
        | [] -> constant width mask
      in
      let scaled coefficient term =
        if Z.equal coefficient Z.one then term
        else if Z.equal coefficient mask then E.unary E.Minus term
        else E.binary E.Mul (constant width coefficient) term
      in
      let expansion bitwise =
        let assignments = 1 lsl count in
        let coefficients =
          Array.init assignments (fun assignment ->
              if truth assignment bitwise then Z.one else Z.zero)
        in
        for bit = 0 to count - 1 do
          for subset = 0 to assignments - 1 do
            if subset land (1 lsl bit) <> 0 then
              coefficients.(subset) <-
                Z.sub coefficients.(subset) coefficients.(subset lxor (1 lsl bit))
          done
        done;
        let terms = ref [] in
        Array.iteri
          (fun subset coefficient ->
            let coefficient = normalize
                (if subset = 0 then Z.neg coefficient else coefficient)
            in
            if not (Z.equal coefficient Z.zero) then
              let term =
                if subset = 0 then constant width coefficient
                else scaled coefficient (conjunction subset)
              in
              terms := term :: !terms)
          coefficients;
        match List.sort E.compare !terms with
        | [] -> zeros width
        | terms -> build_balanced E.Plus terms
      in
      let memo = Nodes.create 128 and linear_edges = ref [] and changed = ref false in
      let rec substitute node =
        match Nodes.find_opt memo node with
        | Some result -> result
        | None ->
            let result =
              if pure_bitwise node then (
                let candidate = expansion node in
                if not (E.is_equal node candidate) then (
                  changed := true;
                  linear_edges := (node, candidate) :: !linear_edges);
                candidate)
              else
                match node with
                | E.Unary { f; x; _ } -> E.unary f (substitute x)
                | E.Binary { f; x; y; _ } -> E.binary f (substitute x) (substitute y)
                | E.Ite { c; t; e; _ } -> E.ite (substitute c) (substitute t) (substitute e)
                | value -> value
            in
            Nodes.add memo node result;
            result
      in
      let substituted = substitute expression in
      if not !changed then None
      else
        match reduce_quotient_polynomial_dag cost substituted with
        | None -> None
        | Some (reduced, equalities, poly_equalities) ->
            let compact =
              linear_candidates ~max_atoms:8 cost reduced
              |> List.sort (fun left right -> Int.compare (cost left) (cost right))
              |> function candidate :: _ -> candidate | [] -> reduced
            in
            if cost compact >= cost expression then None
            else
              Some
                (compact, List.rev !linear_edges, equalities, poly_equalities,
                 if E.is_equal compact reduced then [] else [ reduced, compact ])

let probe_variables expression maximum =
  let width = E.sizeof expression in
  let variables =
    Sample_evaluator.variables_of_expr expression
    |> List.map (fun (name, size) -> E.var name size name)
  in
  if variables = [] || List.length variables > maximum
     || List.exists (fun variable -> E.sizeof variable <> width) variables
  then None else Some (width, Array.of_list variables)

let probe_evaluate expression variables values =
  let labels = Hashtbl.create (Array.length variables) in
  Array.iteri
    (fun index variable ->
      Hashtbl.add labels variable (constant (E.sizeof variable) values.(index)))
    variables;
  (Sample_evaluator.make 1).eval_label expression 0 labels |> Bitvector.value_of

let probe_semantic_linear_mba cost expression =
  if cost expression < 5
     || Greysynth_utils.Utils.dag_size_bounded ~limit:2048 expression > 2048
  then None
  else
    Option.bind (probe_variables expression 4) (fun (width, variables) ->
        let count = Array.length variables and modulus = Z.shift_left Z.one width in
        let normalize value = Z.logand value (Z.pred modulus) in
        try
          let assignments = 1 lsl count in
          let values =
            Array.init assignments (fun assignment ->
                let inputs = Array.init count (fun index ->
                    if assignment land (1 lsl index) = 0 then Z.zero else Z.one) in
                probe_evaluate expression variables inputs)
          in
          for bit = 0 to count - 1 do
            for subset = 0 to assignments - 1 do
              if subset land (1 lsl bit) <> 0 then
                values.(subset) <- normalize
                    (Z.sub values.(subset) values.(subset lxor (1 lsl bit)))
            done
          done;
          let terms = ref [] in
          Array.iteri
            (fun subset coefficient ->
              let coefficient = normalize coefficient in
              if not (Z.equal coefficient Z.zero) then
                let body =
                  if subset = 0 then None
                  else
                    Array.to_list variables
                    |> List.mapi (fun index variable -> index, variable)
                    |> List.filter_map (fun (index, variable) ->
                           if subset land (1 lsl index) = 0 then None else Some variable)
                    |> function
                       | head :: tail -> Some (List.fold_left (E.binary E.And) head tail)
                       | [] -> None
                in
                let term =
                  match body with
                  | None -> constant width coefficient
                  | Some body when Z.equal coefficient Z.one -> body
                  | Some body when Z.equal coefficient (Z.pred modulus) -> E.unary E.Minus body
                  | Some body -> E.binary E.Mul (constant width coefficient) body
                in
                terms := term :: !terms)
            values;
          let raw =
            match !terms with [] -> zeros width | terms -> build_balanced E.Plus terms
          in
          let candidate =
            raw :: linear_candidates ~max_atoms:4 cost raw
            |> List.filter (fun candidate -> cost candidate < cost expression)
            |> List.sort (fun left right -> Int.compare (cost left) (cost right))
            |> List.find_opt (fun candidate -> Rewrite.samples_agree expression candidate)
          in
          candidate
        with _ -> None)

let solve_twice width value =
  let modulus = Z.shift_left Z.one width in
  let normalize value = Z.logand value (Z.pred modulus) in
  let value = normalize value in
  if Z.testbit value 0 then []
  else
    let half = Z.shift_right modulus 1 in
    let base = Z.erem (Z.shift_right value 1) half in
    [ base; Z.add base half ]

let probe_low_width_exact cost expression =
  let width = E.sizeof expression in
  if width > 8 || cost expression < 5 then None
  else
    Option.bind (probe_variables expression 1) (fun (_, variables) ->
        let variable = variables.(0) and count = 1 lsl width in
        try
          let values = Array.init count Z.of_int in
          let target = Array.map
              (fun value -> probe_evaluate expression variables [| value |]) values in
          Smir_interp.analytical_candidates ~width ~target ~expression:variable ~values
          |> List.filter (fun candidate -> cost candidate < cost expression)
          |> List.sort (fun left right -> Int.compare (cost left) (cost right))
          |> List.find_opt (fun candidate -> Rewrite.samples_agree expression candidate)
        with _ -> None)

let probe_semantic_poly cost expression =
  if cost expression < 5 || E.sizeof expression > 64
     || Greysynth_utils.Utils.dag_size_bounded ~limit:2048 expression > 2048
  then None
  else
    Option.bind (probe_variables expression 2) (fun (width, variables) ->
        let modulus = Z.shift_left Z.one width and mask = Z.pred (Z.shift_left Z.one width) in
        let norm value = Z.logand value mask in
        let eval inputs = probe_evaluate expression variables (Array.of_list inputs) in
        let centered coefficient =
          if Z.gt coefficient (Z.shift_right modulus 1) then Z.sub coefficient modulus
          else coefficient
        in
        let scaled coefficient body =
          let coefficient = centered (norm coefficient) in
          if Z.equal coefficient Z.zero then None
          else if Z.equal coefficient Z.one then Some body
          else if Z.equal coefficient (Z.neg Z.one) then Some (E.unary E.Minus body)
          else if Z.sign coefficient < 0 then
            Some (E.unary E.Minus (E.binary E.Mul (constant width (Z.neg coefficient)) body))
          else Some (E.binary E.Mul (constant width coefficient) body)
        in
        let sum terms =
          match List.filter_map Fun.id terms with
          | [] -> zeros width
          | head :: tail -> List.fold_left (E.binary E.Plus) head tail
        in
        let candidates = ref [] in
        (try
           if Array.length variables = 1 then (
             let x = variables.(0) in
             let f0 = eval [ Z.zero ] and f1 = eval [ Z.one ]
             and f2 = eval [ Z.of_int 2 ] and f3 = eval [ Z.of_int 3 ] in
             let d2 = norm (Z.add f2 (Z.sub f0 (Z.mul (Z.of_int 2) f1))) in
             let d3 = norm
                 (Z.add (Z.sub f3 (Z.mul (Z.of_int 3) f2))
                    (Z.sub (Z.mul (Z.of_int 3) f1) f0)) in
             let inv3 = Z.invert (Z.of_int 3) (Z.shift_right modulus 1) in
             solve_twice width d3
             |> List.iter (fun half_c3 ->
                    let c3 = norm (Z.mul half_c3 inv3) in
                    solve_twice width (norm (Z.sub d2 (Z.mul (Z.of_int 6) c3)))
                    |> List.iter (fun c2 ->
                           let c1 = norm (Z.sub f1 (Z.add f0 (Z.add c2 c3))) in
                           let x2 = E.binary E.Mul x x in
                           let x3 = E.binary E.Mul x2 x in
                           candidates := sum
                               [ scaled c3 x3; scaled c2 x2; scaled c1 x;
                                 if Z.equal f0 Z.zero then None else Some (constant width f0) ]
                             :: !candidates)) )
           else (
             let x = variables.(0) and y = variables.(1) in
             let f00 = eval [ Z.zero; Z.zero ]
             and f10 = eval [ Z.one; Z.zero ] and f20 = eval [ Z.of_int 2; Z.zero ]
             and f01 = eval [ Z.zero; Z.one ] and f02 = eval [ Z.zero; Z.of_int 2 ]
             and f11 = eval [ Z.one; Z.one ] in
             let d20 = norm (Z.add f20 (Z.sub f00 (Z.mul (Z.of_int 2) f10)))
             and d02 = norm (Z.add f02 (Z.sub f00 (Z.mul (Z.of_int 2) f01))) in
             let cxy = norm (Z.add f11 (Z.sub f00 (Z.add f10 f01))) in
             List.iter
               (fun cxx ->
                 List.iter
                   (fun cyy ->
                     let cx = norm (Z.sub f10 (Z.add f00 cxx))
                     and cy = norm (Z.sub f01 (Z.add f00 cyy)) in
                     candidates := sum
                         [ scaled cxx (E.binary E.Mul x x);
                           scaled cyy (E.binary E.Mul y y);
                           scaled cxy (E.binary E.Mul x y);
                           scaled cx x; scaled cy y;
                           if Z.equal f00 Z.zero then None else Some (constant width f00) ]
                       :: !candidates)
                   (solve_twice width d02))
               (solve_twice width d20));
           !candidates
           |> List.filter (fun candidate -> cost candidate < cost expression)
           |> List.sort (fun left right -> Int.compare (cost left) (cost right))
           |> List.find_opt (fun candidate -> Rewrite.samples_agree expression candidate)
         with _ -> None))

let dag_bottom_up_simplify ?(minimal = false) expression =
  let memo = Nodes.create 256 in
  let constants = Sample_evaluator.make 1 in
  let cost = Greysynth_utils.Utils.size_of_expr in
  let rec visit node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        check_timeout ();
        let semantic_child child =
          if minimal then child else
          match is_semantically_bitwise cost child with
          | Some candidate
            when Rewrite.accepts_compositional ~pass:"dag-semantic-bitwise"
                   ~equalities:[] ~linear_mba_equalities:[ child, candidate ]
                   child candidate -> candidate
          | _ -> child
        in
        let rebuilt =
          match node with
          | E.Unary { f = E.Not; x; _ } -> E.unary E.Not (semantic_child (visit x))
          | E.Unary { f; x; _ } -> E.unary f (visit x)
          | E.Binary { f = (E.And | E.Or | E.Xor as f); x; y; _ } ->
              E.binary f (semantic_child (visit x)) (semantic_child (visit y))
          | E.Binary { f; x; y; _ } -> E.binary f (visit x) (visit y)
          | E.Ite { c; t; e; _ } -> E.ite (visit c) (visit t) (visit e)
          | _ -> node
        in
        let result = ref rebuilt in
        (match nonlinear_poly_candidate cost !result with
        | Some (candidate, linear_mba_equalities, ring_equalities,
                final_linear_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-minterm-ring-poly"
                 ~equalities:[] ~ring_equalities
                 ~linear_mba_equalities:(linear_mba_equalities @ final_linear_equalities)
                 !result candidate -> result := candidate
        | _ -> ());
        if not minimal then (
        (match xor_affine_mask_candidate cost !result with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-xor-affine-mask"
                 ~equalities:[] ~semilinear_mba_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        (match known_bits_candidate cost !result with
        | Some candidate when Rewrite.accepts ~pass:"dag-known-bits" !result candidate ->
            result := candidate
        | _ -> ());
        if cost !result >= 5 && cost !result <= 64 then (
          let probes =
            [ probe_low_width_exact cost !result;
              probe_semantic_linear_mba cost !result;
              probe_semantic_poly cost !result ]
            |> List.filter_map Fun.id
            |> List.sort (fun left right -> Int.compare (cost left) (cost right))
          in
          match probes with
          | candidate :: _
            when Rewrite.accepts ~pass:"dag-semantic-probe" !result candidate ->
              result := candidate
          | _ -> ());
        (match semilinear_mba_candidate cost !result with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-semilinear-mba"
                 ~equalities:[] ~semilinear_mba_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        (match power2_pullout_candidate cost !result with
        | Some candidate when Rewrite.accepts ~pass:"dag-power2-pullout" !result candidate ->
            result := candidate
        | _ -> ());
        (match demand_bits_candidate cost !result with
        | Some candidate when Rewrite.accepts ~pass:"dag-demand-bits" !result candidate ->
            result := candidate
        | _ -> ());
        (match pair_complementary_atoms cost !result with
        | Some (candidate, ring_equalities, linear_mba_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-complementary-atoms"
                 ~equalities:[] ~ring_equalities ~linear_mba_equalities
                 !result candidate -> result := candidate
        | _ -> ());
        (match correlated_null_candidate cost !result with
        | Some (candidate, ring_equalities, linear_mba_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-correlated-null"
                 ~equalities:[] ~ring_equalities ~linear_mba_equalities
                 !result candidate -> result := candidate
        | _ -> ()));
        let accept_linear candidate =
          Rewrite.accepts_compositional ~pass:"dag-linear-mba"
            ~equalities:[] ~linear_mba_equalities:[ !result, candidate ]
            !result candidate
        in
        if cost !result >= 3
           && List.length (Sample_evaluator.variables_of_expr !result) <= 8
           && linear_mba_compatible !result
        then
          (match
             linear_candidates ~max_atoms:8 cost !result
             |> List.sort (fun left right -> Int.compare (cost left) (cost right))
           with
          | candidate :: _ when accept_linear candidate -> result := candidate
          | _ -> ());
        (match reduce_modular_polynomial cost !result with
        | Some (candidate, equalities, poly_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-poly-mod2w"
                 ~equalities ~poly_equalities !result candidate -> result := candidate
        | _ -> ());
        (match ring_polynomial_candidate cost !result with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-ring-mod2w"
                 ~equalities:[] ~ring_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        (match peepholes constants.eval !result with
        | candidate :: _ when Rewrite.accepts ~pass:"dag-peephole" !result candidate ->
            result := candidate
        | _ -> ());
        Nodes.add memo node !result;
        !result
  in
  visit expression

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

exception Soft_normalization_stop

let run ?deadline expression =
  let check_timeout () =
    Config.check_timeout ();
    match deadline with
    | Some limit when Unix.gettimeofday () >= limit -> raise Soft_normalization_stop
    | _ -> ()
  in
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
           let early_null =
             match reduce_univariate_null_polynomial cost original with
             | Some (candidate, equalities, ring_equalities)
               when Rewrite.accepts_compositional ~pass:"falling-null"
                      ~equalities ~ring_equalities original candidate -> Some candidate
             | _ ->
                 peepholes constants.eval original
                 |> List.find_opt (fun candidate ->
                        is_number Z.zero candidate
                        && cost candidate < cost original
                        && Rewrite.accepts ~pass:"falling-null" original candidate)
           in
           let early_minterm =
             if Option.is_some early_null || cost original < 11 then None
             else
               Sample_evaluator.variables_of_expr original
               |> List.map (fun (name, width) -> E.var name width name)
               |> List.filter (fun candidate -> cost candidate < cost original)
               |> List.find_opt (accept_minterm "minterm-ring-mba")
           in
           (match early_null, early_minterm with
           | Some candidate, _ | None, Some candidate -> current := visit candidate
           | None, None ->
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
                   (match
                      first_some
                        (bitsliced_ring_proof original candidate)
                        (minterm_ring_proof original candidate)
                    with
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
                   if List.length (Sample_evaluator.variables_of_expr !current) >= 3
                      && linear_mba_compatible !current
                      && Rewrite.accepts_compositional ~pass:"linear-mba-mod2w"
                           ~equalities:[]
                           ~linear_mba_equalities:[ !current, candidate ]
                           !current candidate
                   then true
                   else if not (Rewrite.samples_agree !current candidate) then
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
         with
         | Soft_normalization_stop -> ()
         | Timeout_exception -> g_has_timedout := true);
        Nodes.replace results original !current;
        !current
  in
  let expression =
    if !c_mba_oracle = "none" || !c_mba_oracle_calls = 0 then expression
    else
      try oracle_visit expression with Soft_normalization_stop -> expression
  in
  let root_bitsliced =
    if cost expression > 512 then None
    else
      match bitsliced_candidate cost expression with
      | Some candidate when Rewrite.samples_agree expression candidate ->
          (match
             first_some
               (bitsliced_ring_proof expression candidate)
               (minterm_ring_proof expression candidate)
           with
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
