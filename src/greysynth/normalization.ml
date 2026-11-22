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
      let identities =
        match f with
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
      else (match constant_value c with
        | Some condition -> [ if Bitvector.is_zeros condition then e else t ]
        | None -> [])
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
        | atom -> add atom coefficient
      in
      collect Z.one expression;
      let terms =
        Nodes.fold
          (fun atom coefficient terms ->
            let coefficient = normalize coefficient in
            if Z.equal coefficient Z.zero then terms
            else
              let term =
                if Z.equal coefficient Z.one then atom
                else if Z.equal coefficient (Z.pred modulus) then E.unary E.Minus atom
                else E.binary E.Mul atom (const coefficient)
              in
              term :: terms)
          coefficients []
      in
      let terms = if Z.equal !offset Z.zero then terms else const !offset :: terms in
      [ (match sorted terms with [] -> zeros width | terms -> build_balanced E.Plus terms) ]
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
    if !visited > 256 then raise Too_complex;
    if !visited mod 32 = 0 then check_timeout ()
  in
  let atom expression =
    if E.sizeof expression <> width then raise Too_complex;
    let rec lookup index = function
      | [] ->
          if index >= 4 then raise Too_complex;
          atoms := !atoms @ [ expression ];
          Atom index
      | previous :: rest ->
          if E.is_equal previous expression then Atom index
          else lookup (index + 1) rest
    in
    lookup 0 !atoms
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
    | [ low; high ] when count <= 4 ->
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
let product_partition_candidate expression =
  let same = E.is_equal in
  let commutative op left right = function
    | E.Binary { f; x; y; _ } when f = op ->
        (same x left && same y right) || (same x right && same y left)
    | _ -> false
  in
  let product left right = commutative E.Mul left right in
  let union left right = commutative E.Or left right in
  let try_order first second =
    match first with
    | E.Binary { f = E.Mul; x = factor; y = other; _ } ->
        let try_factors m1 union_term =
          match m1 with
          | E.Binary { f = E.And; x; y; _ } when union x y union_term ->
              let m2 = E.binary E.And x (E.unary E.Not y) in
              let m3 = E.binary E.And (E.unary E.Not x) y in
              if not (product m2 m3 second) then None
              else
                let add = E.binary E.Plus and mul = E.binary E.Mul in
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
                   [ x, x_parts; y, y_parts; union_term, all_parts;
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
  match expression with
  | E.Binary { f = E.Plus; x; y; _ } ->
      (match try_order x y with Some result -> Some result | None -> try_order y x)
  | _ -> None

let run expression =
  let results = Nodes.create 128 in
  let sizes = Nodes.create 128 in
  let constants = Sample_evaluator.make 1 in
  let rec cost expression =
    match Nodes.find_opt sizes expression with
    | Some value -> value
    | None ->
        let open Greysynth_utils.Utils in
        let value =
          match expression with
          | E.Unary { f; x; _ } ->
              let weight =
                match !cost_model, f with
                | Legacy, (E.Uext _ | E.Sext _ | E.Restrict _) -> 0
                | Readability, (E.Uext _ | E.Sext _ | E.Restrict _) -> 2
                | _ -> 1
              in
              weight + cost x
          | E.Binary { f; x; y; _ } ->
              let weight =
                match !cost_model, f with
                | Instruction, (E.Udiv | E.Sdiv | E.Umod | E.Smod) -> 8
                | Instruction, E.Mul -> 2
                | Readability, (E.Udiv | E.Sdiv | E.Umod | E.Smod | E.Concat) -> 3
                | _ -> 1
              in
              weight + cost x + cost y
          | E.Ite { c; t; e; _ } ->
              (match !cost_model with Instruction -> 3 | Readability -> 4 | _ -> 1)
              + cost c + cost t + cost e
          | _ -> 1
        in
        Nodes.add sizes expression value;
        value
  in
  let rec visit original =
    if !g_has_timedout then original
    else match Nodes.find_opt results original with
    | Some result -> result
    | None ->
        let current = ref original in
        (try
           check_timeout ();
           current := (match original with
             | E.Unary { f; x; _ } -> E.unary f (visit x)
             | E.Binary { f; x; y; _ } ->
                 let x = visit x in let y = visit y in E.binary f x y
             | E.Ite { c; t; e; _ } ->
                 let c = visit c in let t = visit t in let e = visit e in E.ite c t e
             | _ -> original);
           if not !g_has_timedout then (
             let decomposed =
               match product_partition_candidate !current with
               | Some (candidate, equalities)
                 when cost candidate < cost !current
                      && Rewrite.accepts_compositional ~pass:"polynomial"
                           ~equalities !current candidate ->
                   Some candidate
               | _ -> None
             in
             match decomposed with
             | Some candidate -> current := candidate; current := visit candidate
             | None ->
                 let candidates = peepholes constants.eval !current
                     @ (if !c_ac_normalization then canonical_candidates !current else [])
                     @ (if cost !current >= 4 then linear_candidates cost !current else []) in
                 let candidates = List.filter (fun candidate -> cost candidate < cost !current) candidates in
                 let candidates = List.sort_uniq (fun a b ->
                     let order = Int.compare (cost a) (cost b) in
                     if order = 0 then E.compare a b else order) candidates in
                 match List.find_opt (Rewrite.accepts ~pass:"normalize" !current) candidates with
                 | Some candidate -> current := candidate; current := visit candidate
                 | None -> ())
         with Timeout_exception -> g_has_timedout := true);
        Nodes.replace results original !current;
        !current
  in
  visit expression
