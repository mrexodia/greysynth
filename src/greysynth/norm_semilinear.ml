(* MSiMBA semi-linear masks, known-bits consumers, pullout, and slice identities.
Unsupported arithmetic stays opaque and all candidates are proof-gated. *)

include Norm_linear

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

let gf2_masked_xor_candidate cost expression =
  let width = E.sizeof expression in
  if width > 128 || cost expression < 11 || cost expression > 65_536
     || Greysynth_utils.Utils.dag_size_bounded ~limit:8192 expression > 8192
  then None
  else
    let mask = Z.pred (Z.shift_left Z.one width) in
    let memo = Nodes.create 256 and simplified = ref false in
    let merge left right =
      List.fold_left
        (fun result (atom, bits) ->
          let rec update prefix = function
            | [] -> List.rev ((atom, bits) :: prefix)
            | (old, value) :: rest when E.is_equal atom old ->
                let value = Z.logxor value bits in
                List.rev_append prefix
                  (if Z.equal value Z.zero then rest else (old, value) :: rest)
            | item :: rest -> update (item :: prefix) rest
          in update [] result)
        left right
    in
    let active (constant, terms) =
      List.fold_left (fun value (_, bits) -> Z.logor value bits) constant terms
    in
    let rec parse node =
      match Nodes.find_opt memo node with
      | Some result -> result
      | None ->
          let result =
            match node with
            | E.Cst value -> Bitvector.value_of value, []
            | E.Unary { f = E.Not; x; _ } ->
                let constant, terms = parse x in
                simplified := true; Z.logxor constant mask, terms
            | E.Binary { f = E.Xor; x; y; _ } ->
                let cx, tx = parse x and cy, ty = parse y in
                simplified := true; Z.logxor cx cy, merge tx ty
            | E.Binary { f = E.And; x; y = E.Cst bits; _ }
            | E.Binary { f = E.And; x = E.Cst bits; y = x; _ } ->
                let bits = Bitvector.value_of bits in
                let constant, terms = parse x in
                simplified := true;
                Z.logand constant bits,
                List.filter_map (fun (atom, value) ->
                    let value = Z.logand value bits in
                    if Z.equal value Z.zero then None else Some (atom, value)) terms
            | E.Binary { f = E.Or; x; y = E.Cst bits; _ }
            | E.Binary { f = E.Or; x = E.Cst bits; y = x; _ } ->
                let bits = Bitvector.value_of bits and constant, terms = parse x in
                let keep = Z.logxor mask bits in
                simplified := true;
                Z.logor (Z.logand constant keep) bits,
                List.filter_map (fun (atom, value) ->
                    let value = Z.logand value keep in
                    if Z.equal value Z.zero then None else Some (atom, value)) terms
            | E.Binary { f = (E.Or | E.And as operation); x; y; _ } ->
                let left = parse x and right = parse y in
                if Z.equal (Z.logand (active left) (active right)) Z.zero then (
                  simplified := true;
                  if operation = E.And then Z.zero, []
                  else let cx, tx = left and cy, ty = right in Z.logxor cx cy, merge tx ty)
                else Z.zero, [ node, mask ]
            | atom -> Z.zero, [ atom, mask ]
          in
          if List.length (snd result) > 64 then raise Too_complex;
          Nodes.add memo node result; result
    in
    try
      let constant_value, terms = parse expression in
      if not !simplified then None
      else
        let values =
          List.map (fun (atom, bits) ->
              if Z.equal bits mask then atom
              else E.binary E.And atom (constant width bits)) terms
        in
        let values = if Z.equal constant_value Z.zero then values
          else constant width constant_value :: values in
        let candidate = match values with
          | [] -> zeros width | [ value ] -> value
          | head :: tail -> List.fold_left (E.binary E.Xor) head tail
        in
        if cost candidate < cost expression then Some candidate else None
    with Too_complex -> None

let semilinear_mba_candidate_with_atoms ?(opaque_atoms = [])
    ?has_nonuniform cost expression =
  let width = E.sizeof expression in
  let has_nonuniform () =
    match has_nonuniform with
    | Some result -> result
    | None -> has_nonuniform_bitwise_constant expression
  in
  if width > 128 || cost expression > 4096
     || Greysynth_utils.Utils.dag_size_bounded ~limit:1024 expression > 1024
     || not (has_nonuniform ())
  then None
  else
    let deadline = Unix.gettimeofday () +. 0.2 in
    let constants = Hashtbl.create 16 and bitwise_constants = Hashtbl.create 16
    and saw_nonuniform = ref false
    and opaque = Nodes.create 8 and linear_seen = Nodes.create 128
    and bitwise_seen = Nodes.create 128 in
    let add_opaque atom =
      Nodes.replace opaque atom ();
      if Nodes.length opaque > 6 then raise Too_complex
    in
    let add_slice_mask hi =
      let value = Z.pred (Z.shift_left Z.one (hi + 1)) in
      Hashtbl.replace constants value ();
      Hashtbl.replace bitwise_constants value ();
      if not (Z.equal value Z.zero) && not (Z.equal value (Z.pred (Z.shift_left Z.one width)))
      then saw_nonuniform := true
    in
    let valid_slice amount hi inner =
      amount > 0 && hi + 1 + amount = E.sizeof inner
    in
    let rec inspect under_bitwise node =
      if Unix.gettimeofday () > deadline then raise Too_complex;
      let seen = if under_bitwise then bitwise_seen else linear_seen in
      if not (Nodes.mem seen node) then (
        Nodes.add seen node ();
        if List.exists (E.is_equal node) opaque_atoms then add_opaque node
        else if under_bitwise then
          match node with
          | E.Cst value ->
              let z = Bitvector.value_of value in
              Hashtbl.replace constants z ();
              Hashtbl.replace bitwise_constants z ();
              if not (Bitvector.is_zeros value || Bitvector.is_fill value)
              then saw_nonuniform := true
          | E.Unary { f = E.Not; x; _ } -> inspect true x
          | E.Unary { f = E.Uext amount;
                      x = E.Unary { f = E.Restrict { lo = 0; hi }; x = inner; _ }; _ }
            when valid_slice amount hi inner ->
              add_slice_mask hi;
              inspect true inner
          | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
              inspect true x; inspect true y
          | atom -> add_opaque atom
        else
          match node with
          | E.Unary { f = E.Not; x; _ }
          | E.Unary { f = E.Minus; x; _ } -> inspect false x
          | E.Unary { f = E.Uext amount;
                      x = E.Unary { f = E.Restrict { lo = 0; hi }; x = inner; _ }; _ }
            when valid_slice amount hi inner ->
              add_slice_mask hi;
              inspect true inner
          | E.Unary { f = (E.Uext _ | E.Sext _ | E.Restrict _); _ } as atom ->
              add_opaque atom
          | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
              inspect true x; inspect true y
          | E.Binary { f = (E.Plus | E.Minus); x; y; _ } ->
              inspect false x; inspect false y
          | E.Binary { f = E.Mul; x = E.Cst _; y; _ }
          | E.Binary { f = E.Mul; x = y; y = E.Cst _; _ }
          | E.Binary { f = E.Lsl; x = y; y = E.Cst _; _ } -> inspect false y
          | atom -> add_opaque atom)
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
        Nodes.fold (fun atom () result -> atom :: result) opaque []
        |> List.sort E.compare
      in
      if variables = [] || List.length variables > 4
         || List.exists (fun atom -> E.sizeof atom <> width) variables
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
                  E.binary E.Plus variable constant;
                  E.binary E.Minus constant variable;
                  E.binary E.Plus (E.unary E.Not variable) constant ])
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

let semilinear_mba_candidate cost expression =
  let has_nonuniform = has_nonuniform_bitwise_constant expression in
  match semilinear_mba_candidate_with_atoms
          ~has_nonuniform cost expression with
  | Some _ as result -> result
  | None when not has_nonuniform -> None
  | None ->
      let frequencies = Nodes.create 128 and expanded = Nodes.create 128 in
      let rec count node =
        Nodes.replace frequencies node
          (1 + Option.value (Nodes.find_opt frequencies node) ~default:0);
        if not (Nodes.mem expanded node) then (
          Nodes.add expanded node ();
          match node with
          | E.Unary { x; _ } -> count x
          | E.Binary { x; y; _ } -> count x; count y
          | E.Ite { c; t; e; _ } -> count c; count t; count e
          | _ -> ())
      in
      count expression;
      let rec take count = function
        | _ when count = 0 -> []
        | [] -> []
        | head :: tail -> head :: take (count - 1) tail
      in
      let opaque_atoms =
        Nodes.fold
          (fun node frequency result ->
            if frequency >= 2 && E.sizeof node = E.sizeof expression
               && cost node >= 3
               && (match node with
                   | E.Cst _ -> false
                   | E.Binary { f = (E.And | E.Or | E.Xor);
                                x = E.Cst _; _ }
                   | E.Binary { f = (E.And | E.Or | E.Xor);
                                y = E.Cst _; _ } -> false
                   | _ -> true)
            then node :: result else result)
          frequencies []
        |> List.sort (fun left right -> Int.compare (cost right) (cost left))
        |> take 4
      in
      if opaque_atoms = [] then None
      else semilinear_mba_candidate_with_atoms ~opaque_atoms
          ~has_nonuniform cost expression

let abstract_slice_candidate expression =
  let low_mask bits = Z.pred (Z.shift_left Z.one bits) in
  match expression with
  | E.Unary { f = E.Restrict { lo = 0; hi };
              x = E.Binary { f = E.Lsl; x = _base; y = E.Cst amount; _ }; _ }
    when Z.gt (Bitvector.value_of amount) (Z.of_int hi) ->
      Some (zeros (hi + 1))
  | E.Binary { f = E.And;
               x = E.Unary { f = E.Uext amount;
                     x = E.Unary { f = E.Restrict { lo = 0; hi }; _ }; _ };
               y = E.Cst bits; _ }
  | E.Binary { f = E.And; x = E.Cst bits;
               y = E.Unary { f = E.Uext amount;
                     x = E.Unary { f = E.Restrict { lo = 0; hi }; _ }; _ }; _ }
    when amount > 0
         && Z.equal
              (Z.logand (Bitvector.value_of bits) (low_mask (hi + 1))) Z.zero ->
      Some (zeros (E.sizeof expression))
  | E.Unary { f = E.Restrict { lo = 0; hi };
              x = E.Binary { f = (E.Or | E.Xor | E.Plus);
                    x = base; y = E.Cst bits; _ }; _ }
    when Z.equal
           (Z.logand (Bitvector.value_of bits) (low_mask (hi + 1))) Z.zero ->
      Some (E.restrict ~lo:0 ~hi base)
  | E.Unary { f = E.Restrict { lo = 0; hi };
              x = E.Binary { f = (E.Or | E.Xor | E.Plus);
                    x = E.Cst bits; y = base; _ }; _ }
    when Z.equal
           (Z.logand (Bitvector.value_of bits) (low_mask (hi + 1))) Z.zero ->
      Some (E.restrict ~lo:0 ~hi base)
  | E.Unary { f = E.Restrict { lo = 0; hi };
              x = E.Binary { f = E.And; x = base; y = E.Cst bits; _ }; _ }
    when Z.equal
           (Z.logand (Bitvector.value_of bits) (low_mask (hi + 1)))
           (low_mask (hi + 1)) ->
      Some (E.restrict ~lo:0 ~hi base)
  | E.Unary { f = E.Restrict { lo = 0; hi };
              x = E.Binary { f = E.And; x = E.Cst bits; y = base; _ }; _ }
    when Z.equal
           (Z.logand (Bitvector.value_of bits) (low_mask (hi + 1)))
           (low_mask (hi + 1)) ->
      Some (E.restrict ~lo:0 ~hi base)
  | E.Unary { f = E.Restrict { lo = 0; hi };
              x = E.Unary { f = E.Uext _; x = base; _ }; _ }
    when E.sizeof base >= hi + 1 ->
      Some (if E.sizeof base = hi + 1 then base else E.restrict ~lo:0 ~hi base)
  | _ -> None

let bit0_parity_candidate cost expression =
  let shifted = function
    | E.Binary { f = (E.Plus | E.Minus); x = base; y = E.Cst offset; _ } ->
        Some (base, Z.testbit (Bitvector.value_of offset) 0)
    | E.Binary { f = E.Plus; x = E.Cst offset; y = base; _ } ->
        Some (base, Z.testbit (Bitvector.value_of offset) 0)
    | _ -> None
  in
  let parity_base base odd = if odd then E.unary E.Not base else base in
  let candidate =
    match expression with
    | E.Binary { f = E.Or; x = mask; y = shifted_term; _ }
      when is_number (Z.pred (Z.pred (Z.shift_left Z.one (E.sizeof expression)))) mask ->
        Option.map (fun (base, odd) -> E.binary E.Or mask (parity_base base odd))
          (shifted shifted_term)
    | E.Binary { f = E.And; x = one; y = shifted_term; _ }
      when is_number Z.one one ->
        Option.map (fun (base, odd) -> E.binary E.And one (parity_base base odd))
          (shifted shifted_term)
    | E.Unary { f = E.Uext amount;
                x = E.Unary { f = E.Restrict { lo = 0; hi = 0 };
                      x = shifted_term; _ }; _ } ->
        Option.map
          (fun (base, odd) ->
            E.unary (E.Uext amount)
              (E.restrict ~lo:0 ~hi:0 (parity_base base odd)))
          (shifted shifted_term)
    | _ -> None
  in
  Option.bind candidate (fun candidate ->
      if cost candidate < cost expression then Some candidate else None)

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
          let memo = Nodes.create 64 in
          let rec narrow node =
            match Nodes.find_opt memo node with
            | Some result -> result
            | None ->
                let result =
                  match node with
                  | E.Cst value ->
                      constant (Bitvector.size_of value)
                        (Z.logand (Bitvector.value_of value) mask_value)
                  | E.Unary { f; x; _ } -> E.unary f (narrow x)
                  | E.Binary { f; x; y; _ } -> E.binary f (narrow x) (narrow y)
                  | value -> value
                in
                Nodes.add memo node result;
                result
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

let mask_lift_candidate cost expression =
  let bridge base bits =
    let width = E.sizeof base in
    E.binary E.And base (constant width (Z.pred (Z.shift_left Z.one bits)))
  in
  let candidate =
    match expression with
    | E.Unary { f = E.Uext amount;
                x = E.Unary { f = E.Restrict { lo = 0; hi };
                      x = E.Unary { f = E.Not;
                            x = E.Unary { f = E.Uext inner_amount;
                                  x = E.Unary {
                                    f = E.Restrict { lo = 0; hi = inner_hi };
                                    x = base; _ }; _ }; _ }; _ }; _ }
      when hi = inner_hi && amount = inner_amount
           && hi + 1 + amount = E.sizeof base && amount > 0 ->
        Some (bridge (E.unary E.Not base) (hi + 1))
    | E.Unary { f = E.Uext amount;
                x = E.Unary { f = E.Restrict { lo = 0; hi }; x = base; _ }; _ }
      when hi + 1 + amount = E.sizeof base && amount > 0 ->
        Some (bridge base (hi + 1))
    | _ -> None
  in
  Option.bind candidate (fun candidate ->
      if cost candidate < cost expression then Some candidate else None)

let complementary_slice_candidate _cost expression =
  if Greysynth_utils.Utils.dag_size_bounded ~limit:2048 expression > 2048 then None
  else
    let equalities = ref [] and memo = Nodes.create 64
    and positive_extensions = Nodes.create 32 and seen = Nodes.create 128 in
    let rec collect node =
      if not (Nodes.mem seen node) then (
        Nodes.add seen node ();
        (match node with
        | E.Unary { f = E.Uext amount; x; _ } ->
            Nodes.replace positive_extensions (E.unary (E.Uext amount) x) ();
            collect x
        | E.Unary { x; _ } -> collect x
        | E.Binary { x; y; _ } -> collect x; collect y
        | E.Ite { c; t; e; _ } -> collect c; collect t; collect e
        | _ -> ()))
    in
    collect expression;
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
            | E.Unary { f = E.Uext amount;
                        x = E.Unary { f = E.Restrict { lo = 0; hi };
                              x = E.Unary { f = E.Not; x = base; _ }; _ }; _ }
              when amount > 0 && hi + 1 + amount = E.sizeof base ->
                let positive =
                  E.unary (E.Uext amount) (E.restrict ~lo:0 ~hi base)
                in
                let replacement =
                  E.binary E.Minus
                    (constant (E.sizeof base) (Z.pred (Z.shift_left Z.one (hi + 1))))
                    positive
                in
                equalities := (rebuilt, replacement) :: !equalities;
                replacement
            | E.Unary { f = E.Uext amount;
                        x = E.Unary { f = E.Not; x = low; _ }; _ }
              when amount > 0
                   && Nodes.mem positive_extensions (E.unary (E.Uext amount) low) ->
                let positive = E.unary (E.Uext amount) low in
                let replacement =
                  E.binary E.Minus
                    (constant (E.sizeof rebuilt)
                       (Z.pred (Z.shift_left Z.one (E.sizeof low))))
                    positive
                in
                equalities := (rebuilt, replacement) :: !equalities;
                replacement
            | _ -> rebuilt
          in
          Nodes.add memo node result;
          result
    in
    let substituted = rewrite expression in
    if !equalities = [] then None
    else
      Some (substituted, List.rev !equalities, [])

let nonlinear_product_identity_candidate expression =
  let same = E.is_equal
  and expression_cost = Greysynth_utils.Utils.size_of_expr expression in
  let commutative operation left right = function
    | E.Binary { f; x; y; _ } when f = operation ->
        (same x left && same y right) || (same x right && same y left)
    | _ -> false
  in
  let affine_complements left right =
    let width = E.sizeof left and modulus = Z.shift_left Z.one (E.sizeof left) in
    let normalize value = Z.logand value (Z.pred modulus) in
    let add_term atom coefficient terms =
      let rec merge prefix = function
        | [] -> List.rev ((atom, normalize coefficient) :: prefix)
        | (old_atom, old) :: rest when same atom old_atom ->
            List.rev_append prefix ((old_atom, normalize (Z.add old coefficient)) :: rest)
        | item :: rest -> merge (item :: prefix) rest
      in
      merge [] terms
    in
    let rec affine scale node (constant, terms) =
      match node with
      | E.Cst value ->
          normalize (Z.add constant (Z.mul scale (Bitvector.value_of value))), terms
      | E.Unary { f = E.Minus; x; _ } -> affine (Z.neg scale) x (constant, terms)
      | E.Binary { f = E.Plus; x; y; _ } ->
          affine scale y (affine scale x (constant, terms))
      | E.Binary { f = E.Minus; x; y; _ } ->
          affine (Z.neg scale) y (affine scale x (constant, terms))
      | atom -> constant, add_term atom scale terms
    in
    if E.sizeof right <> width then false
    else
      let constant, terms = affine Z.one right (affine Z.one left (Z.zero, [])) in
      Z.equal (normalize constant) (Z.pred modulus)
      && List.for_all (fun (_, coefficient) -> Z.equal coefficient Z.zero) terms
  in
  let complement_info base complement =
    match complement with
    | E.Unary { f = E.Not; x; _ } when same base x ->
        Some (complement, [], [])
    | _ when expression_cost <= 4096 && affine_complements base complement ->
        let width = E.sizeof base in
        let canonical = E.binary E.Minus (E.unary E.Minus base) (integer width 1) in
        Some (E.unary E.Not base,
              [ canonical, E.unary E.Not base ], [ complement, canonical ])
    | _ -> None
  in
  let parse_cross = function
    | E.Binary { f = E.Mul; x; y; _ } ->
        let operands actual =
          match actual with
          | E.Binary { f = E.And; x; y; _ } ->
              [ x, y, actual, []; y, x, actual, [] ]
          | E.Unary { f = E.Uext amount;
                      x = E.Binary { f = E.And; x; y; _ }; _ } ->
              let lift variable mask =
                let wide_variable = E.unary (E.Uext amount) variable in
                let wide_masks =
                  match mask with
                  | E.Unary { f = E.Not; x = E.Cst value; _ } ->
                      [ E.unary E.Not
                          (constant (E.sizeof actual) (Bitvector.value_of value)) ]
                  | E.Cst value ->
                      let direct =
                        constant (E.sizeof actual) (Bitvector.value_of value)
                      and complemented_base =
                        constant (E.sizeof actual)
                          (Bitvector.value_of (Bitvector.lognot value))
                      in
                      [ direct; E.unary E.Not complemented_base ]
                  | _ -> [ E.unary (E.Uext amount) mask ]
                in
                List.concat_map (fun wide_mask ->
                    let canonical = E.binary E.And wide_variable wide_mask in
                    [ wide_variable, wide_mask, canonical, [ actual, canonical ];
                      wide_mask, wide_variable, canonical, [ actual, canonical ] ])
                  wide_masks
              in
              (match x, y with
              | (E.Cst _ | E.Unary { f = E.Not; x = E.Cst _; _ }), variable ->
                  lift variable x
              | variable, (E.Cst _ | E.Unary { f = E.Not; x = E.Cst _; _ }) ->
                  lift variable y
              | _ -> [])
          | _ -> []
        in
        let replace_complement actual old_value new_value =
          match actual with
          | E.Binary { f = E.And; x; y; _ } ->
              E.binary E.And
                (if same x old_value then new_value else x)
                (if same y old_value then new_value else y)
          | _ -> actual
        in
        let parse first second =
          operands first
          |> List.find_map (fun (a, b_complement, first_base, first_lifted) ->
                 operands second
                 |> List.find_map
                      (fun (b, a_complement, second_base, second_lifted) ->
                        match complement_info b b_complement,
                              complement_info a a_complement with
                        | Some (not_b, linear_b, ring_b),
                          Some (not_a, linear_a, ring_a) ->
                            let first_canonical =
                              replace_complement first_base b_complement not_b
                            and second_canonical =
                              replace_complement second_base a_complement not_a
                            in
                            Some (a, b, first_canonical, second_canonical,
                                  first_lifted @ second_lifted,
                                  linear_a @ linear_b, ring_a @ ring_b)
                        | _ -> None))
        in
        (match parse x y with Some _ as result -> result | None -> parse y x)
    | _ -> None
  in
  let lifted_constant_intersection a b actual =
    let cast = function
      | E.Unary { f = E.Uext amount; x; _ } -> Some (`Unsigned, amount, x)
      | E.Unary { f = E.Sext amount; x; _ } -> Some (`Signed, amount, x)
      | _ -> None
    in
    match cast a, b, actual with
    | Some (kind, amount_a, low_a), E.Cst wide_mask,
      E.Unary { f = E.Uext amount;
                x = E.Binary { f = E.And; x; y; _ }; _ }
      when amount = amount_a ->
        let low_mask =
          match x, y with
          | E.Cst value, other when same other low_a -> Some value
          | other, E.Cst value when same other low_a -> Some value
          | _ -> None
        in
        Option.bind low_mask (fun value ->
            let low_width = E.sizeof low_a in
            let low_bits = Z.pred (Z.shift_left Z.one low_width) in
            let low_value = Bitvector.value_of value
            and wide_value = Bitvector.value_of wide_mask in
            let matches =
              match kind with
              | `Unsigned -> Z.equal low_value (Z.logand wide_value low_bits)
              | `Signed -> Z.equal low_value wide_value
            in
            if matches then Some [ actual, E.binary E.And a b ] else None)
    | _ -> None
  in
  let rec lifted_intersection a b actual =
    if commutative E.And a b actual then Some []
    else
      match a, b, actual with
      | E.Unary { f = E.Uext amount_a; x = low_a; _ },
        E.Unary { f = E.Uext amount_b; x = low_b; _ },
        E.Unary { f = E.Uext amount; x = low_and; _ }
        when amount = amount_a && amount = amount_b
             && commutative E.And low_a low_b low_and ->
          Some [ actual, E.binary E.And a b ]
      | (E.Unary { f = (E.Uext _ | E.Sext _); _ }), E.Cst _, _ ->
          lifted_constant_intersection a b actual
      | E.Cst _, (E.Unary { f = (E.Uext _ | E.Sext _); _ }), _ ->
          lifted_intersection b a actual
      | _ -> None
  in
  let parse_regular a b = function
    | E.Binary { f = E.Mul; x; y; _ } ->
        if commutative E.Or a b y then
          Option.map (fun equalities -> x, y, equalities)
            (lifted_intersection a b x)
        else if commutative E.Or a b x then
          Option.map (fun equalities -> y, x, equalities)
            (lifted_intersection a b y)
        else None
    | _ -> None
  in
  let substitute_equalities equalities root =
    let replacements = Nodes.create 16 and memo = Nodes.create 32
    and active = Nodes.create 16 in
    List.iter (fun (left, right) -> Nodes.replace replacements left right) equalities;
    let rec visit node =
      if Nodes.mem active node then node
      else
        match Nodes.find_opt memo node with
        | Some result -> result
        | None ->
            Nodes.add active node ();
            Fun.protect
              ~finally:(fun () -> Nodes.remove active node)
              (fun () ->
                let direct =
                  match Nodes.find_opt replacements node with
                  | Some replacement when not (E.is_equal replacement node) ->
                      Some replacement
                  | _ -> None
                in
                let rebuilt =
                  match direct with
                  | Some replacement -> visit replacement
                  | None ->
                      match node with
                      | E.Unary { f; x; _ } -> E.unary f (visit x)
                      | E.Binary { f; x; y; _ } -> E.binary f (visit x) (visit y)
                      | E.Ite { c; t; e; _ } -> E.ite (visit c) (visit t) (visit e)
                      | value -> value
                in
                let result =
                  match Nodes.find_opt replacements rebuilt with
                  | Some replacement when not (E.is_equal replacement rebuilt) ->
                      visit replacement
                  | _ -> rebuilt
                in
                Nodes.add memo node result;
                result)
    in
    visit root
  in
  let build make_candidate cross regular =
    match parse_cross cross with
    | Some (a, b, first, second, cross_lifted,
            complement_linear, complement_ring) ->
        Option.map
          (fun (_intersection, union, lifted_equalities) ->
            let u = E.binary E.And a b in
            let first_replacement = E.binary E.Minus a u
            and second_replacement = E.binary E.Minus b u
            and union_replacement =
              E.binary E.Minus (E.binary E.Plus a b) u
            in
            let intersection_equalities =
              if lifted_equalities = [] then [ _intersection, u ] else []
            in
            let equalities =
              [ first, first_replacement; second, second_replacement;
                union, union_replacement ]
              @ intersection_equalities @ complement_linear
            in
            let product = E.binary E.Mul a b in
            let candidate = make_candidate product in
            let substituted =
              substitute_equalities
                (cross_lifted @ lifted_equalities @ equalities @ complement_ring)
                expression
            in
            (candidate, cross_lifted @ lifted_equalities, equalities, [],
             complement_ring @ [ substituted, candidate ]))
          (parse_regular a b regular)
    | None -> None
  in
  let build_constants make_candidate cross regular =
    let and_constant = function
      | (E.Binary { f = E.And; x = term; y = E.Cst value; _ } as actual)
      | (E.Binary { f = E.And; x = E.Cst value; y = term; _ } as actual) ->
          Some (term, value, actual)
      | _ -> None
    in
    let parse = function
      | E.Binary { f = E.Mul; x; y; _ } ->
          let try_pair plain complemented =
            match and_constant plain, and_constant complemented with
            | Some (a, complement, first),
              Some (E.Unary { f = E.Not; x = other; _ }, base, second)
              when same a other && Bitvector.equal complement (Bitvector.lognot base) ->
                Some (a, E.constant base, first, second)
            | _ -> None
          in
          (match try_pair x y with Some _ as result -> result | None -> try_pair y x)
      | _ -> None
    in
    match parse cross with
    | Some (a, b, first, second) ->
        Option.map
          (fun (intersection, union, lifted_equalities) ->
            let u = E.binary E.And a b in
            let first_replacement = E.binary E.Minus a u
            and second_replacement = E.binary E.Minus b u
            and union_replacement = E.binary E.Minus (E.binary E.Plus a b) u in
            let intersection_equalities =
              if lifted_equalities = [] then [ intersection, u ] else []
            in
            let semilinear_equalities =
              [ first, first_replacement; second, second_replacement;
                union, union_replacement ] @ intersection_equalities
            in
            let product = E.binary E.Mul a b in
            let candidate = make_candidate product in
            let substituted =
              substitute_equalities
                (lifted_equalities @ semilinear_equalities) expression
            in
            (candidate, lifted_equalities, [], semilinear_equalities,
             [ substituted, candidate ]))
          (parse_regular a b regular)
    | None -> None
  in
  let rec additive sign node result =
    if List.length result > 8 then result
    else
      match node with
      | E.Binary { f = E.Plus; x; y; _ } ->
          additive sign y (additive sign x result)
      | E.Binary { f = E.Minus; x; y; _ } ->
          additive (not sign) y (additive sign x result)
      | E.Unary { f = E.Minus; x; _ } -> additive (not sign) x result
      | term -> (sign, term) :: result
  in
  let terms = List.rev (additive true expression []) in
  let rebuild terms =
    match terms with
    | [] -> zeros (E.sizeof expression)
    | (sign, term) :: rest ->
        let initial = if sign then term else E.unary E.Minus term in
        List.fold_left (fun total (positive, value) ->
            E.binary (if positive then E.Plus else E.Minus) total value)
          initial rest
  in
  let rec scan_left index = function
    | [] -> None
    | (sign, left) :: rest ->
        let rec scan_right offset = function
          | [] -> None
          | (other_sign, right) :: tail when sign = other_sign ->
              let make_candidate product =
                terms
                |> List.mapi (fun position item ->
                       if position = index then Some (sign, product)
                       else if position = index + offset + 1 then None
                       else Some item)
                |> List.filter_map Fun.id |> rebuild
              in
              let result =
                match build make_candidate left right with
                | Some _ as result -> result
                | None ->
                    (match build make_candidate right left with
                    | Some _ as result -> result
                    | None ->
                        (match build_constants make_candidate left right with
                        | Some _ as result -> result
                        | None -> build_constants make_candidate right left))
              in
              (match result with
              | Some _ -> result
              | None -> scan_right (offset + 1) tail)
          | _ :: tail -> scan_right (offset + 1) tail
        in
        (match scan_right 0 rest with
        | Some _ as result -> result
        | None -> scan_left (index + 1) rest)
  in
  if List.length terms > 8 then None else scan_left 0 terms

let known_bits_candidate cost expression =
  let candidate =
    let known = Known_bits.analyze expression in
    match Known_bits.is_constant known with
    | Some value when cost expression > 1 -> Some (constant known.width value)
    | _ ->
        let bit0 value =
          let known = Known_bits.analyze value in
          if Z.testbit known.zeros 0 then Some false
          else if Z.testbit known.ones 0 then Some true else None
        in
        let is_minus_two value bits =
          Z.equal (Bitvector.value_of bits)
            (Z.pred (Z.pred (Z.shift_left Z.one (E.sizeof value))))
        in
        let and_minus_two value bits =
          if not (is_minus_two value bits) then None
          else match bit0 value with
            | Some false -> Some value
            | Some true -> Some (E.binary E.Minus value (integer (E.sizeof value) 1))
            | None -> None
        and and_one value one =
          if not (Z.equal (Bitvector.value_of one) Z.one) then None
          else match bit0 value with
            | Some false -> Some (zeros (E.sizeof value)) | _ -> None
        and or_minus_two value bits =
          if not (is_minus_two value bits) then None
          else match bit0 value with Some false -> Some (E.constant bits) | _ -> None
        and xor_one value one =
          if not (Z.equal (Bitvector.value_of one) Z.one) then None
          else match bit0 value with
            | Some true -> Some (E.binary E.Minus value (integer (E.sizeof value) 1))
            | Some false -> Some (E.binary E.Plus value (integer (E.sizeof value) 1))
            | None -> None
        in
        match expression with
        | E.Binary { f = E.And; x = value; y = E.Cst bits; _ }
        | E.Binary { f = E.And; x = E.Cst bits; y = value; _ } ->
            (match and_minus_two value bits with
            | Some _ as result -> result
            | None ->
                (match and_one value bits with
                | Some _ as result -> result
                | None ->
                let known = Known_bits.analyze value in
                let removed = Z.logand (Z.pred (Z.shift_left Z.one known.width))
                    (Z.lognot (Bitvector.value_of bits)) in
                if Z.equal (Z.logand removed known.zeros) removed
                then Some value else None))
        | E.Binary { f = E.Or; x = value; y = E.Cst bits; _ }
        | E.Binary { f = E.Or; x = E.Cst bits; y = value; _ } ->
            (match or_minus_two value bits with
            | Some _ as result -> result
            | None ->
                let known = Known_bits.analyze value in
                let bits_value = Bitvector.value_of bits in
                if Z.equal (Z.logand bits_value known.ones) bits_value
                then Some value else None)
        | E.Binary { f = E.Xor; x = value; y = E.Cst one; _ }
        | E.Binary { f = E.Xor; x = E.Cst one; y = value; _ } -> xor_one value one
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
