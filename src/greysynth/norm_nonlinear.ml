(* PolySim/BitTrans nonlinear MBA reduction, quotient polynomials, grouping, and recovery.
All algebraic outputs are untrusted until Rewrite_proof replay succeeds. *)

include Norm_poly

module AndPolynomial = Map.Make (Int)

let polysim_candidate cost expression =
  let nonlinear_memo = Nodes.create 128 in
  let rec has_nonlinear_product node =
    match Nodes.find_opt nonlinear_memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Binary { f = E.Mul; x; y; _ }
            when Option.is_none (constant_value x)
                 && Option.is_none (constant_value y) -> true
          | E.Unary { x; _ } -> has_nonlinear_product x
          | E.Binary { x; y; _ } ->
              has_nonlinear_product x || has_nonlinear_product y
          | E.Ite { c; t; e; _ } ->
              has_nonlinear_product c || has_nonlinear_product t
              || has_nonlinear_product e
          | _ -> false
        in
        Nodes.add nonlinear_memo node result;
        result
  in
  if not (has_nonlinear_product expression) then None else
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let normalize value =
    let value = Z.erem value modulus in
    if Z.sign value < 0 then Z.add value modulus else value
  in
  let atoms_table = Nodes.create 32 and collected_bitwise = Nodes.create 128
  and collected_ring = Nodes.create 128 in
  let rec collect_bitwise node =
    if not (Nodes.mem collected_bitwise node) then (
      Nodes.add collected_bitwise node ();
      match node with
    | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
    | E.Unary { f = E.Not; x; _ } -> collect_bitwise x
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
        collect_bitwise x; collect_bitwise y
    | atom -> Nodes.replace atoms_table atom ());
  and collect_ring node =
    if not (Nodes.mem collected_ring node) then (
      Nodes.add collected_ring node ();
      match node with
    | E.Unary { f = E.Minus; x; _ } -> collect_ring x
    | E.Binary { f = (E.Plus | E.Minus | E.Mul); x; y; _ } ->
        collect_ring x; collect_ring y
    | (E.Unary { f = E.Not; _ }
      | E.Binary { f = (E.And | E.Or | E.Xor); _ }) as bitwise ->
        collect_bitwise bitwise
    | E.Cst _ -> ()
    | atom -> Nodes.replace atoms_table atom ())
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
    let pure_memo = Nodes.create 128 in
    let rec pure_bitwise expression =
      match Nodes.find_opt pure_memo expression with
      | Some result -> result
      | None ->
          let result =
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
          Nodes.add pure_memo expression result;
          result
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

let partial_linear_sum_candidate cost expression =
  if Greysynth_utils.Utils.dag_size_bounded ~limit:1024 expression > 1024 then None
  else
    let rec additive sign = function
      | E.Binary { f = E.Plus; x; y; _ } -> additive sign x @ additive sign y
      | E.Binary { f = E.Minus; x; y; _ } -> additive sign x @ additive (not sign) y
      | E.Unary { f = E.Minus; x; _ } -> additive (not sign) x
      | E.Binary { f = E.Mul;
                   x = E.Binary { f = (E.Plus | E.Minus as op); x; y; _ };
                   y = factor; _ }
      | E.Binary { f = E.Mul; x = factor;
                   y = E.Binary { f = (E.Plus | E.Minus as op); x; y; _ }; _ } ->
          let left = E.binary E.Mul factor x and right = E.binary E.Mul factor y in
          if op = E.Plus then additive sign left @ additive sign right
          else additive sign left @ additive (not sign) right
      | term -> [ if sign then term else E.unary E.Minus term ]
    in
    let rec nonlinear = function
      | E.Binary { f = E.Mul; x; y; _ }
        when Option.is_none (constant_value x) && Option.is_none (constant_value y) -> true
      | E.Unary { x; _ } -> nonlinear x
      | E.Binary { x; y; _ } -> nonlinear x || nonlinear y
      | E.Ite { c; t; e; _ } -> nonlinear c || nonlinear t || nonlinear e
      | _ -> false
    in
    let terms = additive true expression in
    if List.length terms < 3 || List.length terms > 64 then None
    else
      let nonlinear_terms, linear_terms =
        List.partition nonlinear terms
      in
      if nonlinear_terms = [] || linear_terms = [] then None
      else
        let sum = function
          | [] -> zeros (E.sizeof expression)
          | head :: tail -> List.fold_left (E.binary E.Plus) head tail
        in
        let nonlinear_sum = sum nonlinear_terms and linear_sum = sum linear_terms in
        let best_linear source =
          linear_candidates ~max_atoms:6 cost source
          |> List.filter (fun candidate -> Rewrite.samples_agree source candidate)
          |> List.sort (fun left right -> Int.compare (cost left) (cost right))
          |> function candidate :: _ when cost candidate < cost source -> Some candidate
                    | _ -> None
        in
        let linear_ring = ring_polynomial_candidate cost linear_sum in
        let options = ref [] in
        Option.iter
          (fun candidate ->
            options := (candidate, [], [ linear_sum, candidate ]) :: !options)
          (best_linear linear_sum);
        Option.iter
          (fun ring ->
            options := (ring, [ linear_sum, ring ], []) :: !options;
            Option.iter
              (fun candidate ->
                options := (candidate, [ linear_sum, ring ], [ ring, candidate ]) :: !options)
              (best_linear ring))
          linear_ring;
        let simplified_linear, linear_ring_edges, linear_equalities =
          match
            !options
            |> List.sort (fun (left, _, _) (right, _, _) ->
                   Int.compare (cost left) (cost right))
          with
          | best :: _ -> best
          | [] -> linear_sum, [], []
        in
        let simplified_nonlinear =
          Option.value (ring_polynomial_candidate cost nonlinear_sum)
            ~default:nonlinear_sum
        in
        let partitioned = E.binary E.Plus nonlinear_sum linear_sum in
        let candidate = E.binary E.Plus simplified_nonlinear simplified_linear in
        if cost candidate >= cost expression then None
        else
          let ring_equalities = ref [ expression, partitioned ] in
          if not (E.is_equal simplified_nonlinear nonlinear_sum) then
            ring_equalities := (nonlinear_sum, simplified_nonlinear) :: !ring_equalities;
          ring_equalities := linear_ring_edges @ !ring_equalities;
          Some (candidate, List.rev !ring_equalities, linear_equalities)

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
