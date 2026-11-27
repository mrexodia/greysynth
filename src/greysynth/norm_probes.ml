(* Bounded semantic probes, local candidate portfolios, and quotient-DAG recovery.
Finite observations are filters only; universal proof remains mandatory. *)

open Config
include Norm_nonlinear

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
    (fun candidate ->
      candidates := direct "constant-cast" ~allow_equal_cost:true candidate :: !candidates)
    (constant_cast_fold_candidate constants.eval expression);
  Option.iter
    (fun candidate ->
      candidates := direct "restrict-factor" ~allow_equal_cost:true candidate :: !candidates)
    (restrict_factoring_candidate expression);
  Option.iter
    (fun candidate ->
      candidates := direct "abstract-slice" ~allow_equal_cost:true candidate :: !candidates)
    (abstract_slice_candidate expression);
  Option.iter
    (fun (candidate, equalities, ring_equalities) ->
      candidates :=
        { expr = candidate; pass = "complementary-slice"; equalities;
          ring_equalities; poly_equalities = []; linear_mba_equalities = [];
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (complementary_slice_refine_candidate cost expression);
  Option.iter
    (fun candidate -> candidates := direct "mask-lift" candidate :: !candidates)
    (mask_lift_candidate cost expression);
  Option.iter
    (fun candidate -> candidates := direct "known-bits" candidate :: !candidates)
    (known_bits_candidate cost expression);
  Option.iter
    (fun candidate -> candidates := direct "bit0-parity" candidate :: !candidates)
    (bit0_parity_candidate cost expression);
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
  Option.iter
    (fun (candidate, equalities, linear_mba_equalities,
          semilinear_mba_equalities, ring_equalities) ->
      candidates :=
        { expr = candidate; pass = "product-peel"; equalities;
          ring_equalities; poly_equalities = []; linear_mba_equalities;
          semilinear_mba_equalities; allow_equal_cost = false } :: !candidates)
    (nonlinear_product_identity_candidate expression);
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
    (fun (candidate, ring_equalities, linear_mba_equalities) ->
      candidates :=
        { expr = candidate; pass = "partial-linear-sum"; equalities = [];
          ring_equalities; poly_equalities = []; linear_mba_equalities;
          semilinear_mba_equalities = []; allow_equal_cost = false } :: !candidates)
    (partial_linear_sum_candidate cost expression);
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
            raw
            :: (linear_candidates ~max_atoms:4 cost raw
                @ Option.to_list (disjoint_component_candidate cost raw))
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

let probe_opaque_atoms ?(max_cost = 512) cost expression =
  if cost expression < 9 || cost expression > max_cost
     || Greysynth_utils.Utils.dag_size_bounded ~limit:256 expression > 256
  then None
  else
    let width = E.sizeof expression and frequencies = Nodes.create 128
    and expanded = Nodes.create 128 in
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
    let shell = function
      | E.Cst _ -> true
      | E.Unary { f = (E.Not | E.Minus); _ } -> true
      | E.Binary { f = (E.Plus | E.Minus | E.And | E.Or | E.Xor); _ } -> true
      | E.Binary { f = E.Mul; x; y; _ } ->
          Option.is_some (constant_value x) || Option.is_some (constant_value y)
      | E.Binary { f = E.Lsl; y; _ } -> Option.is_some (constant_value y)
      | _ -> false
    in
    let bitwise_or_shift = function
      | E.Unary { f = E.Not; _ }
      | E.Binary { f = (E.And | E.Or | E.Xor | E.Lsl); _ } -> true
      | _ -> false
    in
    let has_shell_bits = Nodes.create 128 in
    let rec has_bitwise_or_shift node =
      match Nodes.find_opt has_shell_bits node with
      | Some result -> result
      | None ->
          let child child =
            E.sizeof child = E.sizeof node && has_bitwise_or_shift child
          in
          let result =
            if bitwise_or_shift node then true
            else
              match node with
              | E.Unary { f = E.Minus; x; _ } -> child x
              | E.Binary { f = (E.Plus | E.Minus | E.Mul); x; y; _ } ->
                  child x || child y
              | _ -> false
          in
          Nodes.add has_shell_bits node result;
          result
    in
    let attempt mode =
      let atoms = Nodes.create 8 in
      let rec collect ~inside_bw is_root node =
        let frequency =
          Option.value (Nodes.find_opt frequencies node) ~default:0
        in
        let repeated =
          mode = `Shared && not is_root && cost node >= 3 && frequency >= 2
        and arithmetic_boundary =
          mode = `Arithmetic && not is_root
          && not (has_bitwise_or_shift node)
          && (inside_bw || (cost node >= 3 && frequency >= 2))
        in
        if E.sizeof node <> width then Nodes.replace atoms node ()
        else if arithmetic_boundary || repeated || not (shell node) then
          Nodes.replace atoms node ()
        else
          let inside_bw = inside_bw || bitwise_or_shift node in
          match node with
          | E.Cst _ -> ()
          | E.Unary { x; _ } -> collect ~inside_bw false x
          | E.Binary { f = E.Mul; x; y; _ } ->
              (match constant_value x, constant_value y with
              | Some _, _ -> collect ~inside_bw false y
              | _, Some _ -> collect ~inside_bw false x
              | _ -> Nodes.replace atoms node ())
          | E.Binary { x; y; _ } ->
              collect ~inside_bw false x; collect ~inside_bw false y
          | _ -> Nodes.replace atoms node ()
      in
      collect ~inside_bw:false true expression;
      let atoms = Nodes.fold (fun atom () result -> atom :: result) atoms []
        |> List.filter (fun atom -> E.sizeof atom = width)
        |> List.sort E.compare |> Array.of_list in
      let count = Array.length atoms in
      if count = 0 || count > 3 then None
      else
        let replacements = Nodes.create count and inverse = Nodes.create count in
        Array.iteri (fun index atom ->
            let name = Printf.sprintf "$greysynth.opaque.%d" index in
            let variable = E.var name width name in
            Nodes.add replacements atom variable;
            Nodes.add inverse variable atom) atoms;
        let substituted = Nodes.create 64 and restored = Nodes.create 64 in
        let rec substitute node =
          match Nodes.find_opt replacements node with
          | Some variable -> variable
          | None ->
              (match Nodes.find_opt substituted node with
              | Some result -> result
              | None ->
                  let result =
                    match node with
                    | E.Unary { f; x; _ } -> E.unary f (substitute x)
                    | E.Binary { f; x; y; _ } ->
                        E.binary f (substitute x) (substitute y)
                    | E.Ite { c; t; e; _ } ->
                        E.ite (substitute c) (substitute t) (substitute e)
                    | value -> value
                  in
                  Nodes.add substituted node result;
                  result)
        and restore node =
          match Nodes.find_opt inverse node with
          | Some atom -> atom
          | None ->
              (match Nodes.find_opt restored node with
              | Some result -> result
              | None ->
                  let result =
                    match node with
                    | E.Unary { f; x; _ } -> E.unary f (restore x)
                    | E.Binary { f; x; y; _ } -> E.binary f (restore x) (restore y)
                    | E.Ite { c; t; e; _ } -> E.ite (restore c) (restore t) (restore e)
                    | value -> value
                  in
                  Nodes.add restored node result;
                  result)
        in
        let abstract_expression = substitute expression in
        if cost abstract_expression <= 3 then None
        else
          let variables = Array.init count (fun index ->
              let name = Printf.sprintf "$greysynth.opaque.%d" index in
              E.var name width name) in
          try
            let assignments = 1 lsl count and modulus = Z.shift_left Z.one width in
            let normalize value = Z.logand value (Z.pred modulus) in
            let coefficients = Array.init assignments (fun assignment ->
                let values = Array.init count (fun index ->
                    if assignment land (1 lsl index) = 0 then Z.zero else Z.one) in
                probe_evaluate abstract_expression variables values) in
            for bit = 0 to count - 1 do
              for subset = 0 to assignments - 1 do
                if subset land (1 lsl bit) <> 0 then
                  coefficients.(subset) <- normalize
                      (Z.sub coefficients.(subset)
                         coefficients.(subset lxor (1 lsl bit)))
              done
            done;
            let terms = ref [] in
            Array.iteri (fun subset coefficient ->
                let coefficient = normalize coefficient in
                if not (Z.equal coefficient Z.zero) then
                  let body =
                    if subset = 0 then None
                    else
                      Array.to_list variables
                      |> List.mapi (fun index variable -> index, variable)
                      |> List.filter_map (fun (index, variable) ->
                             if subset land (1 lsl index) = 0 then None else Some variable)
                      |> function head :: tail -> Some (List.fold_left (E.binary E.And) head tail)
                                  | [] -> None
                  in
                  let term = match body with
                    | None -> constant width coefficient
                    | Some body when Z.equal coefficient Z.one -> body
                    | Some body -> E.binary E.Mul (constant width coefficient) body
                  in terms := term :: !terms) coefficients;
            let raw = match !terms with
              | [] -> zeros width
              | head :: tail -> List.fold_left (E.binary E.Plus) head tail
            in
            let offset body value =
              if Z.equal value Z.zero then body
              else E.binary E.Plus body (constant width value)
            in
            let analytical =
              if count <> 1 then []
              else
                let values =
                  [| Z.zero; Z.one; Z.of_int 2; Z.of_int 3; Z.of_int 7;
                     Z.of_int 17; Z.of_int 63; Z.of_int 255 |]
                  |> Array.map normalize
                in
                let target = Array.map (fun value ->
                    probe_evaluate abstract_expression variables [| value |]) values
                in
                Smir_interp.analytical_candidates ~width ~target
                  ~expression:variables.(0) ~values
            in
            let binary_templates =
              if count <> 2 then []
              else
                let x = variables.(0) and y = variables.(1)
                and c0 = normalize coefficients.(0) in
                [ E.binary E.Plus x y; E.binary E.Minus x y;
                  E.binary E.Minus y x; E.binary E.Or x y;
                  E.binary E.And x y; E.binary E.Xor x y ]
                |> List.map (fun body -> offset body c0)
            in
            let abstract_candidates =
              raw :: (linear_candidates ~max_atoms:3 cost raw
                      @ analytical @ binary_templates)
            in
            let full_width_value sample_index variable_index =
              let rec fill shift state result =
                if shift >= width then normalize result
                else
                  let state =
                    Z.logand
                      (Z.add
                         (Z.mul state (Z.of_string "0x5851f42d4c957f2d"))
                         (Z.of_string "0x14057b7ef767814f"))
                      (Z.pred (Z.shift_left Z.one 64))
                  in
                  fill (shift + 64) state
                    (Z.logor result (Z.shift_left state shift))
              in
              let seed = Z.of_int
                  ((sample_index + 1) * 65537 + (variable_index + 3) * 104729)
              in
              fill 0 seed Z.zero
            in
            let agrees candidate =
              let rec loop sample_index =
                if sample_index = 24 then true
                else
                  let values = Array.init count (fun variable_index ->
                      full_width_value sample_index variable_index) in
                  Z.equal (probe_evaluate abstract_expression variables values)
                    (probe_evaluate candidate variables values)
                  && loop (sample_index + 1)
              in
              loop 0
            in
            abstract_candidates
            |> List.filter (fun candidate -> agrees candidate)
            |> List.map restore
            |> List.filter (fun candidate -> cost candidate < cost expression)
            |> List.filter (Rewrite.samples_agree expression)
            |> List.sort (fun left right -> Int.compare (cost left) (cost right))
            |> function candidate :: _ -> Some candidate | [] -> None
          with _ -> None
    in
    match attempt `Arithmetic with
    | Some _ as result -> result
    | None ->
        (match attempt `Shared with
        | Some _ as result -> result
        | None -> attempt `Operator)
