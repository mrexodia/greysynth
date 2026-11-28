(* SiMBA/GAMBA linear-MBA truth-table and Boolean reconstruction over Z/(2^w).
Candidates are untrusted until independently accepted and replayed. *)

open Config
include Norm_peepholes

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

let demorgan_not expression =
  let cost = Greysynth_utils.Utils.size_of_expr in
  let choose candidates =
    List.fold_left (fun best candidate ->
        if cost candidate < cost best then candidate else best)
      (List.hd candidates) (List.tl candidates)
  in
  let rec visit depth expression =
    let direct = E.unary E.Not expression in
    if depth >= 12 then direct
    else
      match expression with
      | E.Unary { f = E.Not; x; _ } -> x
      | E.Binary { f = E.And; x; y; _ } ->
          choose [ direct; E.binary E.Or (visit (depth + 1) x) (visit (depth + 1) y) ]
      | E.Binary { f = E.Or; x; y; _ } ->
          choose [ direct; E.binary E.And (visit (depth + 1) x) (visit (depth + 1) y) ]
      | E.Binary { f = E.Xor; x; y; _ } ->
          choose [ direct; E.binary E.Xor (visit (depth + 1) x) y;
                   E.binary E.Xor x (visit (depth + 1) y) ]
      | E.Cst value when Bitvector.is_zeros value ->
          E.constant (Bitvector.fill (Bitvector.size_of value))
      | E.Cst value when Bitvector.is_fill value ->
          E.constant (Bitvector.zeros (Bitvector.size_of value))
      | _ -> direct
  in
  visit 0 expression

let not_pushdown_candidate cost expression =
  if cost expression > 64 then None
  else match expression with
    | E.Unary { f = E.Not; x; _ } ->
        let candidates =
          demorgan_not x ::
          (match x with
          | E.Binary { f = E.Minus; x = left; y = right; _ } ->
              [ E.binary E.Plus right (demorgan_not left) ]
          | _ -> [])
        in
        (candidates
         |> List.filter (fun candidate -> cost candidate < cost expression)
         |> List.sort (fun left right -> Int.compare (cost left) (cost right))
         |> function candidate :: _ -> Some candidate | [] -> None)
    | _ -> None

let rec linear_candidates_with_rings ?(opaque_atoms = [])
    ?(max_atoms = !c_normalization_max_atoms) ?(semantic_bitwise = false)
    ?(ring_bridges = true) ?(bitwise_stops = true) cost expression =
  let width = E.sizeof expression in
  let modulus = Z.shift_left Z.one width in
  let mask = Z.pred modulus in
  let normalize value = Z.logand value mask in
  let ring_edges = ref [] and replacements = Nodes.create 32 in
  let record_ring original rewritten =
    if not (E.is_equal original rewritten) then (
      ring_edges := (original, rewritten) :: !ring_edges;
      Nodes.replace replacements original rewritten)
  in
  let scalar_expression coefficient base =
    let coefficient = normalize coefficient in
    if Z.equal coefficient Z.zero then zeros width
    else if Z.equal coefficient Z.one then base
    else if Z.equal coefficient mask then E.unary E.Minus base
    else E.binary E.Mul (constant width coefficient) base
  in
  let extract_product_scalar root =
    let steps = ref 0 in
    let rec collect coefficient factors = function
      | E.Cst value -> normalize (Z.mul coefficient (Bitvector.value_of value)), factors
      | E.Unary { f = E.Minus; x; _ } -> collect (Z.neg coefficient) factors x
      | E.Binary { f = E.Mul; x; y; _ } ->
          incr steps;
          if !steps > 64 then raise Too_complex;
          let coefficient, factors = collect coefficient factors x in
          collect coefficient factors y
      | factor -> coefficient, factor :: factors
    in
    let coefficient, factors = collect Z.one [] root in
    let factors = List.rev factors in
    if List.length factors < 2 then None
    else
      let sorted = List.sort E.compare factors in
      let reordered = List.exists2 (fun left right -> not (E.is_equal left right))
          factors sorted in
      if Z.equal (normalize coefficient) Z.one && not reordered then None
      else
        let base = build_balanced E.Mul sorted in
        let rewritten = scalar_expression coefficient base in
        Some (normalize coefficient, base, rewritten)
  in
  let canonical_ac_atom original =
    if not ring_bridges then original else
    let rec flatten operation acc = function
      | E.Binary { f; x; y; _ } when f = operation ->
          flatten operation (flatten operation acc x) y
      | value -> value :: acc
    in
    match original with
    | E.Binary { f = (E.Plus | E.Mul as operation); _ } ->
        let terms = flatten operation [] original |> List.sort E.compare in
        if List.length terms > 4 then original
        else
          let canonical = build_balanced operation terms in
          record_ring original canonical;
          canonical
    | _ -> original
  in
  let bitwise_linear_atoms = Nodes.create 32
  and linear_candidates_seen = Nodes.create 32 in
  let scan_linear_seen = Nodes.create 128 and scan_bitwise_seen = Nodes.create 128
  and scan_count = ref 0 in
  let scaled_shift = function
    | (E.Binary { f = E.Lsl; x; y = E.Cst count; _ } as original) ->
        let count = Bitvector.value_of count in
        if Z.gt count Z.zero && Z.lt count (Z.of_int width) then
          let coefficient = constant width (Z.shift_left Z.one (Z.to_int count)) in
          Some (original, canonical_ac_atom (E.binary E.Mul coefficient x))
        else None
    | _ -> None
  in
  let linear_position = function
    | E.Unary { f = E.Minus; _ }
    | E.Binary { f = (E.Plus | E.Minus | E.Mul | E.Lsl); _ } -> true
    | _ -> false
  in
  let rec scan_bitwise node =
    if !scan_count < 64 && not (Nodes.mem scan_bitwise_seen node) then (
      incr scan_count;
      Nodes.add scan_bitwise_seen node ();
      match node with
      | E.Cst value when Bitvector.is_zeros value || Bitvector.is_fill value -> ()
      | E.Unary { f = E.Not; x; _ } -> scan_bitwise x
      | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
          scan_bitwise x; scan_bitwise y
      | value when linear_position value ->
          Nodes.replace bitwise_linear_atoms (canonical_ac_atom value) ();
          Option.iter (fun (_, scaled) ->
              Nodes.replace bitwise_linear_atoms scaled ()) (scaled_shift value)
      | _ -> ())
  and scan_linear node =
    if !scan_count < 64 && not (Nodes.mem scan_linear_seen node) then (
      incr scan_count;
      Nodes.add scan_linear_seen node ();
      let add_linear value =
        if linear_position value then
          Nodes.replace linear_candidates_seen (canonical_ac_atom value) ()
      in
      match node with
      | E.Cst _ -> ()
      | E.Unary { f = E.Minus; x; _ } -> add_linear node; scan_linear x
      | E.Unary { f = E.Not; _ } -> scan_bitwise node
      | E.Binary { f = (E.Plus | E.Minus); x; y; _ } ->
          add_linear node; scan_linear x; scan_linear y
      | E.Binary { f = E.Mul; x; y; _ } ->
          (match constant_value x, constant_value y with
          | Some _, _ -> add_linear node; scan_linear y
          | _, Some _ -> add_linear node; scan_linear x
          | _ ->
              (match if ring_bridges then extract_product_scalar node else None with
              | Some (_, base, _) -> Nodes.replace linear_candidates_seen base ()
              | None -> add_linear node))
      | E.Binary { f = E.Lsl; x; y; _ } ->
          add_linear node;
          Option.iter (fun (_, scaled) ->
              Nodes.replace linear_candidates_seen scaled ()) (scaled_shift node);
          (match constant_value y with Some _ -> scan_linear x | None -> ())
      | E.Binary { f = (E.And | E.Or | E.Xor); _ } -> scan_bitwise node
      | _ -> ())
  in
  if bitwise_stops then scan_linear expression;
  let has_boundary_overlap =
    bitwise_stops
    && Nodes.fold
         (fun atom () found -> found || Nodes.mem linear_candidates_seen atom)
         bitwise_linear_atoms false
  in
  let is_bitwise_linear_atom expression =
    has_boundary_overlap
    && (Nodes.mem bitwise_linear_atoms expression
        || Nodes.mem bitwise_linear_atoms (canonical_ac_atom expression))
  in
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
    let expression = canonical_ac_atom expression in
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
  let linear_memo = Nodes.create 128 and boolean_memo = Nodes.create 128 in
  let rec linear expression =
    match Nodes.find_opt linear_memo expression with
    | Some result -> result
    | None ->
        tick ();
        let result =
          if List.exists (E.is_equal expression) opaque_atoms then atom expression
          else match expression with
          | E.Binary { f = E.Mul; x; y; _ } -> (
              match constant_value x, constant_value y with
              | Some k, _ ->
                  if is_bitwise_linear_atom expression then atom expression
                  else Scale (Bitvector.value_of k, linear y)
              | _, Some k ->
                  if is_bitwise_linear_atom expression then atom expression
                  else Scale (Bitvector.value_of k, linear x)
              | _ ->
                  (match if ring_bridges then extract_product_scalar expression else None with
                  | Some (coefficient, base, rewritten) ->
                      record_ring expression rewritten;
                      saw_nonlinear := true;
                      Scale (coefficient, atom base)
                  | None -> saw_nonlinear := true; atom expression))
          | _ when is_bitwise_linear_atom expression -> atom expression
          | E.Cst value -> Number (Bitvector.value_of value)
          | E.Unary { f = E.Minus; x; _ } -> Scale (mask, linear x)
          | E.Unary { f = E.Not; x; _ } -> Not (linear x)
          | E.Binary { f = E.Plus; x; y; _ } -> Add (linear x, linear y)
          | E.Binary { f = E.Minus; x; y; _ } -> Sub (linear x, linear y)
          | E.Binary { f = E.Lsl; x; y; _ } -> (
              match constant_value y with
              | Some count ->
                  if is_bitwise_linear_atom expression then atom expression
                  else
                    (match scaled_shift expression with
                    | Some (_, scaled) when Nodes.mem bitwise_linear_atoms scaled ->
                        record_ring expression scaled;
                        atom scaled
                    | _ ->
                        let count = bounded_count width count in
                        if count >= width then Number Z.zero
                        else Scale (Z.shift_left Z.one count, linear x))
              | None -> atom expression)
          | _ -> boolean expression
        in
        Nodes.add linear_memo expression result;
        result
  and boolean expression =
    match Nodes.find_opt boolean_memo expression with
    | Some result -> result
    | None ->
        tick ();
        let result =
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
        Nodes.add boolean_memo expression result;
        result
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
      if cost candidate < cost expression then results := candidate :: !results;
      let companion =
        match candidate with
        | E.Binary { f = E.Plus; x = E.Cst value; y = body; _ }
          when Z.equal (Bitvector.value_of value) Z.one ->
            Some (E.unary E.Minus (demorgan_not body))
        | E.Binary { f = E.Plus; x = body; y = E.Cst value; _ }
          when Z.equal (Bitvector.value_of value) Z.one ->
            Some (E.unary E.Minus (demorgan_not body))
        | E.Binary { f = E.Minus; x = E.Cst value; y = body; _ }
          when Z.equal (Bitvector.value_of value) mask ->
            Some (demorgan_not body)
        | _ -> None
      in
      Option.iter (fun value ->
          if cost value < cost expression then results := value :: !results)
        companion
    in
    let scale coefficient value =
      if Z.equal coefficient Z.zero then zeros width
      else if Z.equal coefficient Z.one then value
      else if Z.equal coefficient mask then E.unary E.Minus value
      else E.binary E.Mul value (constant width coefficient)
    in
    let offer_linear_sum offset terms =
      let terms = List.filter (fun (coefficient, _) ->
          not (Z.equal (normalize coefficient) Z.zero)) terms in
      let build values =
        let negative, positive =
          List.partition (fun (coefficient, _) ->
              Z.equal (normalize coefficient) mask) values
        in
        let positive =
          (if Z.equal (normalize offset) Z.zero then []
           else [ constant width (normalize offset) ])
          @ List.map (fun (coefficient, body) ->
                scale (normalize coefficient) body) positive
        in
        let base = match positive with
          | [] -> None | [ value ] -> Some value
          | values -> Some (build_balanced E.Plus values)
        in
        match base, List.map snd negative with
        | None, [] -> zeros width
        | None, head :: tail ->
            List.fold_left (fun total body -> E.binary E.Minus total body)
              (E.unary E.Minus head) tail
        | Some value, negatives ->
            List.fold_left (fun total body -> E.binary E.Minus total body)
              value negatives
      in
      offer (build terms);
      if not (Z.equal (normalize offset) Z.zero) then
        List.iteri (fun index (coefficient, body) ->
            if Z.equal (normalize coefficient) (normalize offset) then
              let absorbed =
                scale (normalize (Z.neg offset)) (demorgan_not body)
              in
              let remaining =
                terms |> List.mapi (fun i term -> i, term)
                |> List.filter_map (fun (i, term) ->
                       if i = index then None else Some term)
                |> List.map (fun (c, value) -> scale (normalize c) value)
              in
              offer (match remaining with
                | [] -> absorbed
                | values -> build_balanced E.Plus (absorbed :: values)))
          terms
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
      let shannon = ref [] in
      if count = 3 && cost expression <= 128 then (
        let synth2 u v bits =
          match bits with
          | 0 -> zeros width
          | 15 -> constant width mask
          | 10 -> u | 12 -> v
          | 5 -> demorgan_not u | 3 -> demorgan_not v
          | 8 -> E.binary E.And u v
          | 14 -> E.binary E.Or u v
          | 6 -> E.binary E.Xor u v
          | 9 -> demorgan_not (E.binary E.Xor u v)
          | 2 -> E.binary E.And u (demorgan_not v)
          | 4 -> E.binary E.And (demorgan_not u) v
          | 11 -> E.binary E.Or u (demorgan_not v)
          | 13 -> E.binary E.Or (demorgan_not u) v
          | 7 -> demorgan_not (E.binary E.And u v)
          | 1 -> demorgan_not (E.binary E.Or u v)
          | _ -> zeros width
        in
        for pivot = 0 to 2 do
          let remaining = List.init 3 Fun.id |> List.filter ((<>) pivot) in
          let u_index = List.nth remaining 0 and v_index = List.nth remaining 1 in
          let pattern pivot_value =
            let bits = ref 0 in
            for assignment = 0 to 3 do
              let original =
                (if pivot_value then 1 lsl pivot else 0)
                lor (if assignment land 1 <> 0 then 1 lsl u_index else 0)
                lor (if assignment land 2 <> 0 then 1 lsl v_index else 0)
              in
              if truth.(original) then bits := !bits lor (1 lsl assignment)
            done;
            !bits
          in
          let f0 = pattern false and f1 = pattern true in
          let pivot_atom = atoms.(pivot) and u = atoms.(u_index) and v = atoms.(v_index) in
          let s0 = synth2 u v f0 and s1 = synth2 u v f1 in
          if f1 = 0 then
            shannon := E.binary E.And (demorgan_not pivot_atom) s0 :: !shannon;
          if f0 = 0 then
            shannon := E.binary E.And pivot_atom s1 :: !shannon;
          if f1 = 15 then
            shannon := E.binary E.Or pivot_atom s0 :: !shannon;
          if f0 = 15 then
            shannon := E.binary E.Or (demorgan_not pivot_atom) s1 :: !shannon;
          if f1 = (15 lxor f0) then
            shannon := E.binary E.Xor pivot_atom s0 :: !shannon
        done);
      [ combine E.Or (zeros width) minterms;
        combine E.And (constant width mask) clauses;
        anf ] @ !shannon
      |> List.sort_uniq E.compare
    in
    let distinct =
      Array.to_list target |> List.sort_uniq Z.compare
    in
    let active =
      List.init count Fun.id
      |> List.filter (fun bit ->
             let changed = ref false in
             for assignment = 0 to Array.length target - 1 do
               if assignment land (1 lsl bit) = 0
                  && not (Z.equal target.(assignment)
                            target.(assignment lor (1 lsl bit)))
               then changed := true
             done;
             !changed)
    in
    if List.length active <= 4 && List.length distinct = 2
    then (
      let active = Array.of_list active and active_count = List.length active in
      let assignments = 1 lsl active_count in
      let original_assignment assignment =
        let result = ref 0 in
        Array.iteri (fun projected original ->
            if assignment land (1 lsl projected) <> 0 then
              result := !result lor (1 lsl original)) active;
        !result
      in
      let reduced = Array.init assignments (fun assignment ->
          target.(original_assignment assignment)) in
      let v0 = target.(0) in
      let v1 =
        List.find (fun value -> not (Z.equal value v0)) distinct
      in
      let truth = Array.map (Z.equal v1) reduced in
      let literal assignment projected =
        let atom = atoms.(active.(projected)) in
        if assignment land (1 lsl projected) = 0 then E.unary E.Not atom else atom
      in
      let minterms =
        List.init assignments Fun.id
        |> List.filter (Array.get truth)
        |> List.map (fun assignment ->
               List.init active_count (literal assignment)
               |> build_balanced E.And)
      and clauses =
        List.init assignments Fun.id
        |> List.filter (fun assignment -> not truth.(assignment))
        |> List.map (fun assignment ->
               List.init active_count (fun projected ->
                   let atom = atoms.(active.(projected)) in
                   if assignment land (1 lsl projected) = 0 then atom
                   else E.unary E.Not atom)
               |> build_balanced E.Or)
      in
      let coefficients = Array.copy truth in
      for bit = 0 to active_count - 1 do
        for subset = 0 to assignments - 1 do
          if subset land (1 lsl bit) <> 0 then
            coefficients.(subset) <-
              coefficients.(subset) <> coefficients.(subset lxor (1 lsl bit))
        done
      done;
      let anf =
        List.init assignments Fun.id
        |> List.filter (Array.get coefficients)
        |> List.map (fun subset ->
               if subset = 0 then constant width mask
               else
                 Array.to_list active
                 |> List.mapi (fun projected original -> projected, atoms.(original))
                 |> List.filter_map (fun (projected, atom) ->
                        if subset land (1 lsl projected) = 0 then None else Some atom)
                 |> build_balanced E.And)
        |> build_balanced E.Xor
      in
      let booleans = ref
        [ (match minterms with [] -> zeros width | terms -> build_balanced E.Or terms);
          (match clauses with [] -> constant width mask | terms -> build_balanced E.And terms);
          anf ]
      in
      if active_count = 3 && cost expression <= 128 then (
        let synth2 u v bits =
          match bits with
          | 0 -> zeros width | 15 -> constant width mask
          | 10 -> u | 12 -> v | 5 -> demorgan_not u | 3 -> demorgan_not v
          | 8 -> E.binary E.And u v | 14 -> E.binary E.Or u v
          | 6 -> E.binary E.Xor u v | 9 -> demorgan_not (E.binary E.Xor u v)
          | 2 -> E.binary E.And u (demorgan_not v)
          | 4 -> E.binary E.And (demorgan_not u) v
          | 11 -> E.binary E.Or u (demorgan_not v)
          | 13 -> E.binary E.Or (demorgan_not u) v
          | 7 -> demorgan_not (E.binary E.And u v)
          | 1 -> demorgan_not (E.binary E.Or u v)
          | _ -> zeros width
        in
        for pivot = 0 to 2 do
          let remaining = List.init 3 Fun.id |> List.filter ((<>) pivot) in
          let ui = List.nth remaining 0 and vi = List.nth remaining 1 in
          let pattern pivot_value =
            let bits = ref 0 in
            for assignment = 0 to 3 do
              let original =
                (if pivot_value then 1 lsl pivot else 0)
                lor (if assignment land 1 <> 0 then 1 lsl ui else 0)
                lor (if assignment land 2 <> 0 then 1 lsl vi else 0)
              in
              if truth.(original) then bits := !bits lor (1 lsl assignment)
            done;
            !bits
          in
          let f0 = pattern false and f1 = pattern true in
          let p = atoms.(active.(pivot))
          and u = atoms.(active.(ui)) and v = atoms.(active.(vi)) in
          let s0 = synth2 u v f0 and s1 = synth2 u v f1 in
          if f1 = 0 then booleans := E.binary E.And (demorgan_not p) s0 :: !booleans;
          if f0 = 0 then booleans := E.binary E.And p s1 :: !booleans;
          if f1 = 15 then booleans := E.binary E.Or p s0 :: !booleans;
          if f0 = 15 then booleans := E.binary E.Or (demorgan_not p) s1 :: !booleans;
          if f1 = (15 lxor f0) then booleans := E.binary E.Xor p s0 :: !booleans
        done);
      List.iter (fun boolean ->
          let delta0 = normalize (Z.sub v1 v0) in
          let weighted0 = scale delta0 boolean in
          offer (if Z.equal v0 Z.zero then weighted0
                 else E.binary E.Plus (constant width v0) weighted0);
          let boolean1 =
            if count = 3 && cost expression <= 128 then demorgan_not boolean
            else E.unary E.Not boolean
          in
          let delta1 = normalize (Z.sub v0 v1) in
          let offset1 = normalize (Z.sub (Z.add v0 v0) v1) in
          let weighted1 = scale delta1 boolean1 in
          offer (if Z.equal offset1 Z.zero then weighted1
                 else E.binary E.Plus (constant width offset1) weighted1)) !booleans);
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
        List.iter
          (fun boolean ->
            offer (if count = 3 && cost expression <= 128 then demorgan_not boolean
                   else E.unary E.Not boolean))
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
    if not !saw_nonlinear && count <= min 4 !c_normalization_max_atoms then (
      let offset = target.(0) in
      let shifted = Array.map (fun value -> normalize (Z.sub value offset)) target in
      let shifted_distinct =
        Array.to_list shifted |> List.sort_uniq Z.compare
      in
      let add_offset candidate =
        if Z.equal offset Z.zero then candidate
        else E.binary E.Plus (constant width offset) candidate
      in
      let indicator value =
        let truth = Array.map (Z.equal value) shifted in
        boolean_candidates truth
        |> List.sort (fun left right -> Int.compare (cost left) (cost right))
        |> function candidate :: _ -> Some candidate | [] -> None
      in
      (match shifted_distinct with
      | [ zero; first; second ] when Z.equal zero Z.zero ->
          (match indicator first, indicator second with
          | Some first_boolean, Some second_boolean ->
              offer_linear_sum offset
                [ first, first_boolean; second, second_boolean ];
              if Z.equal (normalize (Z.add first second)) Z.zero then
                offer (add_offset
                  (scale first (E.binary E.Minus first_boolean second_boolean)))
          | _ -> ())
      | [ zero; first; second; combined ] when Z.equal zero Z.zero ->
          if Z.equal combined (normalize (Z.add first second)) then
            let first_truth = Array.map
                (fun value -> Z.equal value first || Z.equal value combined) shifted
            and second_truth = Array.map
                (fun value -> Z.equal value second || Z.equal value combined) shifted in
            (match
               boolean_candidates first_truth
               |> List.sort (fun left right -> Int.compare (cost left) (cost right)),
               boolean_candidates second_truth
               |> List.sort (fun left right -> Int.compare (cost left) (cost right))
             with
            | first_boolean :: _, second_boolean :: _ ->
                offer_linear_sum offset
                  [ first, first_boolean; second, second_boolean ]
            | _ -> ())
      | _ -> ());
      if count = 2 then (
        let v10 = shifted.(1) and v01 = shifted.(2) and v11 = shifted.(3) in
        let cx = normalize (Z.sub v11 v01)
        and cy = normalize (Z.sub v11 v10)
        and cor = normalize (Z.sub (Z.add v10 v01) v11) in
        offer_linear_sum offset
          [ cx, atoms.(0); cy, atoms.(1);
            cor, E.binary E.Or atoms.(0) atoms.(1) ];
        let cand = normalize (Z.sub (Z.sub v11 v10) v01) in
        offer_linear_sum offset
          [ v10, atoms.(0); v01, atoms.(1);
            cand, E.binary E.And atoms.(0) atoms.(1) ])
    );
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
    let signed coefficient =
      let coefficient = normalize coefficient in
      if Z.testbit coefficient (width - 1) then Z.sub coefficient modulus
      else coefficient
    in
    let monomial subset =
      if subset = 0 then constant width Z.one
      else
        Array.to_list atoms
        |> List.mapi (fun index atom -> index, atom)
        |> List.filter_map (fun (index, atom) ->
               if subset land (1 lsl index) = 0 then None else Some atom)
        |> build_balanced E.And
    in
    let buckets = ref [] in
    let add_bucket magnitude positive term =
      let rec merge prefix = function
        | [] ->
            buckets := List.rev_append prefix
                [ magnitude, (if positive then [ term ] else []),
                  (if positive then [] else [ term ]) ]
        | (old, positives, negatives) :: rest when Z.equal old magnitude ->
            buckets := List.rev_append prefix
                ((old,
                  (if positive then term :: positives else positives),
                  (if positive then negatives else term :: negatives)) :: rest)
        | item :: rest -> merge (item :: prefix) rest
      in
      merge [] !buckets
    in
    Array.iteri (fun subset coefficient ->
        let coefficient = signed coefficient in
        if not (Z.equal coefficient Z.zero) then
          add_bucket (Z.abs coefficient) (Z.sign coefficient > 0) (monomial subset))
      coefficients;
    let sum_terms = function
      | [] -> zeros width
      | [ value ] -> value
      | values -> build_balanced E.Plus values
    in
    let grouped =
      List.map
        (fun (magnitude, positives, negatives) ->
          let positive = sum_terms positives and negative = sum_terms negatives in
          let body =
            if negatives = [] then positive
            else if positives = [] then E.unary E.Minus negative
            else E.binary E.Minus positive negative
          in
          scale magnitude body)
        !buckets
    in
    if grouped <> [] then offer (sum_terms grouped);
    let nonzero_signed =
      Array.to_list coefficients |> List.map signed
      |> List.filter (fun value -> not (Z.equal value Z.zero))
    in
    if not (Z.equal coefficients.(0) Z.zero)
       && List.length nonzero_signed <= 4
    then (
      let terms = ref [] in
      Array.iteri (fun subset coefficient ->
          if subset <> 0 && not (Z.equal coefficient Z.zero) then
            terms := (signed coefficient, monomial subset) :: !terms)
        coefficients;
      offer_linear_sum (signed coefficients.(0)) !terms);
    let gcd =
      List.fold_left (fun result value -> Z.gcd result (Z.abs value))
        Z.zero nonzero_signed
    in
    if Z.gt gcd Z.one
       && List.for_all (fun value -> Z.leq (Z.abs value) (Z.of_int 65536)) nonzero_signed
    then (
      let inner_terms = ref [] in
      Array.iteri (fun subset coefficient ->
          let coefficient = signed coefficient in
          if not (Z.equal coefficient Z.zero) then
            inner_terms := scale (normalize (Z.div coefficient gcd)) (monomial subset)
                           :: !inner_terms)
        coefficients;
      if !inner_terms <> [] then offer (scale gcd (sum_terms !inner_terms)));
    let memo = Nodes.create 128 and active = Nodes.create 32 in
    let rec substitute node =
      if Nodes.mem active node then node
      else
        match Nodes.find_opt memo node with
        | Some result -> result
        | None ->
            Nodes.add active node ();
            Fun.protect
              ~finally:(fun () -> Nodes.remove active node)
              (fun () ->
                let result =
                  match Nodes.find_opt replacements node with
                  | Some replacement when not (E.is_equal replacement node) ->
                      substitute replacement
                  | _ ->
                      match node with
                      | E.Unary { f; x; _ } -> E.unary f (substitute x)
                      | E.Binary { f; x; y; _ } ->
                          E.binary f (substitute x) (substitute y)
                      | E.Ite { c; t; e; _ } ->
                          E.ite (substitute c) (substitute t) (substitute e)
                      | value -> value
                in
                Nodes.add memo node result;
                result)
    in
    let rewritten_source = substitute expression
    and ring_edges = List.rev !ring_edges in
    let proposals =
      List.map (fun candidate -> candidate, ring_edges, rewritten_source) !results
    in
    if has_boundary_overlap then
      let sort proposals =
        proposals
        |> List.sort_uniq (fun (left, _, _) (right, _, _) -> E.compare left right)
        |> List.sort (fun (left, _, _) (right, _, _) ->
               let order = Int.compare (cost left) (cost right) in
               if order = 0 then E.compare left right else order)
      in
      let proposals = sort proposals in
      if (match proposals with (candidate, _, _) :: _ -> cost candidate <= 7 | [] -> false)
      then proposals
      else
        let standard =
          linear_candidates_with_rings ~opaque_atoms ~max_atoms ~semantic_bitwise
            ~ring_bridges ~bitwise_stops:false cost expression
        in
        let merged = sort (proposals @ standard) in
        if merged <> [] || not ring_bridges then merged
        else
          linear_candidates_with_rings ~opaque_atoms ~max_atoms ~semantic_bitwise
            ~ring_bridges:false ~bitwise_stops:false cost expression
          |> sort
    else proposals
  with Too_complex ->
    if bitwise_stops then
      let standard =
        linear_candidates_with_rings ~opaque_atoms ~max_atoms ~semantic_bitwise
          ~ring_bridges ~bitwise_stops:false cost expression
      in
      if standard <> [] || not ring_bridges then standard
      else
        linear_candidates_with_rings ~opaque_atoms ~max_atoms ~semantic_bitwise
          ~ring_bridges:false ~bitwise_stops:false cost expression
    else []

let linear_candidates ?opaque_atoms ?max_atoms ?semantic_bitwise cost expression =
  linear_candidates_with_rings ?opaque_atoms ?max_atoms ?semantic_bitwise
    ~ring_bridges:false ~bitwise_stops:false cost expression
  |> List.map (fun (candidate, _, _) -> candidate)

let is_semantically_bitwise cost expression =
  let memo = Nodes.create 32 in
  let rec pure node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Var _ -> true
          | E.Cst value -> Bitvector.is_zeros value || Bitvector.is_fill value
          | E.Unary { f = E.Not; x; _ } -> pure x
          | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
              pure x && pure y
          | _ -> false
        in
        Nodes.add memo node result;
        result
  in
  linear_candidates ~max_atoms:6 ~semantic_bitwise:true cost expression
  |> List.filter pure
  |> List.sort (fun left right -> Int.compare (cost left) (cost right))
  |> function candidate :: _ -> Some candidate | [] -> None
