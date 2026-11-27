(* Sparse commutative-ring and initial modular-polynomial normalization machinery.
The module only proposes candidates certified by decidable or SMT proof edges. *)

open Config
include Norm_semilinear

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

let complementary_slice_refine_candidate cost expression =
  Option.bind (complementary_slice_candidate cost expression)
    (fun (substituted, equalities, _) ->
      let ring = ring_polynomial_candidate cost substituted in
      let candidates = substituted :: Option.to_list ring in
      match
        candidates
        |> List.filter (fun candidate -> cost candidate < cost expression)
        |> List.sort (fun left right -> Int.compare (cost left) (cost right))
      with
      | candidate :: _ ->
          let ring_equalities =
            match ring with
            | Some ring when E.is_equal ring candidate -> [ substituted, ring ]
            | _ -> []
          in
          Some (candidate, equalities, ring_equalities)
      | [] -> None)

let minterm_ring_poly_candidate cost expression =
  let width = E.sizeof expression in
  let atom_table = Nodes.create 8 and collected_bitwise = Nodes.create 128
  and collected_ring = Nodes.create 128 in
  let rec collect_bitwise node =
    if not (Nodes.mem collected_bitwise node) then (
      Nodes.add collected_bitwise node ();
      match node with
    | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
    | E.Unary { f = E.Not; x; _ } -> collect_bitwise x
    | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
        collect_bitwise x; collect_bitwise y
    | atom -> Nodes.replace atom_table atom ());
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
    | atom -> Nodes.replace atom_table atom ())
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
    let pure_memo = Nodes.create 128 in
    let rec pure_bitwise expression =
      match Nodes.find_opt pure_memo expression with
      | Some result -> result
      | None ->
          let result =
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
          Nodes.add pure_memo expression result;
          result
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
