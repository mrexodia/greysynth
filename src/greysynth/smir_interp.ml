module E = Sexpr.Expr

let constant width value = E.constant (Bitvector.create value width)
let normalize mask value = Z.logand value mask
let all2 predicate left right =
  Array.length left = Array.length right
  && Array.for_all2 predicate left right

let analytical_candidates ~width ~target ~expression ~values =
  if width <= 0 || width > 64 || Array.length target < 1
     || Array.length target <> Array.length values
  then []
  else
    let modulus = Z.shift_left Z.one width and mask = Z.pred (Z.shift_left Z.one width) in
    let norm = normalize mask in
    let check f = Array.for_all2 (fun value wanted -> Z.equal (f value) wanted) values target in
    let candidates = ref [] in
    let offer candidate = candidates := candidate :: !candidates in
    let scale coefficient =
      if Z.equal coefficient Z.one then expression
      else E.binary E.Mul (constant width coefficient) expression
    in
    if all2 Z.equal values target then offer expression;
    if Array.for_all (Z.equal target.(0)) target then offer (constant width target.(0));
    let add_c = norm (Z.sub target.(0) values.(0)) in
    if check (fun value -> norm (Z.add value add_c)) then
      offer (if Z.equal add_c Z.zero then expression
             else E.binary E.Plus expression (constant width add_c));
    let xor_c = Z.logxor target.(0) values.(0) in
    if check (fun value -> Z.logxor value xor_c) then
      offer (if Z.equal xor_c Z.zero then expression
             else E.binary E.Xor expression (constant width xor_c));
    let odd_index = ref None in
    Array.iteri (fun index value -> if !odd_index = None && Z.testbit value 0 then odd_index := Some index) values;
    Option.iter
      (fun index ->
        let coefficient = norm (Z.mul target.(index) (Z.invert values.(index) modulus)) in
        if check (fun value -> norm (Z.mul coefficient value)) then offer (scale coefficient))
      !odd_index;
    let z_y = Array.fold_left Z.logor Z.zero target
    and o_y = Array.fold_left Z.logand mask target
    and z_e = Array.fold_left Z.logor Z.zero values
    and o_e = Array.fold_left Z.logand mask values in
    let c_and = Z.logor z_y (Z.logxor mask z_e)
    and c_or = Z.logand o_y (Z.logxor mask o_e) in
    if check (fun value -> Z.logor (Z.logand value c_and) c_or) then (
      let masked =
        if Z.equal c_and mask then expression
        else E.binary E.And expression (constant width c_and)
      in
      offer (if Z.equal c_or Z.zero then masked
             else E.binary E.Or masked (constant width c_or)));
    let affine = ref None in
    for i = 0 to Array.length values - 1 do
      for j = i + 1 to Array.length values - 1 do
        if !affine = None then
          let delta = norm (Z.sub values.(i) values.(j)) in
          if Z.testbit delta 0 then
            let a = norm (Z.mul (Z.sub target.(i) target.(j)) (Z.invert delta modulus)) in
            let b = norm (Z.sub target.(i) (Z.mul a values.(i))) in
            if check (fun value -> norm (Z.add (Z.mul a value) b)) then affine := Some (a, b)
      done
    done;
    Option.iter
      (fun (a, b) ->
        let body = scale a in
        offer (if Z.equal b Z.zero then body else E.binary E.Plus body (constant width b)))
      !affine;
    let quadratic = ref None in
    let n = min 16 (Array.length values) in
    for i = 0 to 0 do
      for j = 0 to n - 1 do
        for k = 0 to n - 1 do
          if !quadratic = None && i <> j && i <> k && j <> k then begin
            let d1 = norm (Z.sub values.(j) values.(i))
            and d2 = norm (Z.sub values.(k) values.(i)) in
            if not (Z.equal d2 Z.zero) && Z.testbit d1 0
               && Z.trailing_zeros d2 = 1
            then begin
              let half = Z.shift_right modulus 1 in
              let a1 = norm
                  (Z.mul (Z.sub target.(j) target.(i)) (Z.invert d1 modulus)) in
              let d2_half = Z.erem (Z.shift_right d2 1) half in
              let y2_delta = norm (Z.sub target.(k) target.(i)) in
              if not (Z.testbit y2_delta 0) && Z.testbit d2_half 0 then begin
                let a2 = Z.erem
                    (Z.mul (Z.shift_right y2_delta 1) (Z.invert d2_half half)) half in
                let delta_x = Z.erem (Z.sub values.(k) values.(j)) half in
                if Z.testbit delta_x 0 then begin
                  let c2_base =
                    Z.erem (Z.mul (Z.sub a2 a1) (Z.invert delta_x half)) half in
                  List.iter
                    (fun c2 ->
                      if !quadratic = None then begin
                        let c1 = norm
                            (Z.sub a1 (Z.mul c2 (Z.add values.(j) values.(i)))) in
                        let c0 = norm
                            (Z.sub target.(i)
                               (Z.add (Z.mul c2 (Z.mul values.(i) values.(i)))
                                  (Z.mul c1 values.(i)))) in
                        if check (fun value ->
                            norm (Z.add c0 (Z.add (Z.mul c1 value)
                                      (Z.mul c2 (Z.mul value value)))))
                        then quadratic := Some (c2, c1, c0)
                      end)
                    [ c2_base; Z.add c2_base half ]
                end
              end
            end
          end
        done
      done
    done;
    Option.iter
      (fun (c2, c1, c0) ->
        let square = E.binary E.Mul expression expression in
        let term coefficient body =
          if Z.equal coefficient Z.zero then None
          else if Z.equal coefficient Z.one then Some body
          else Some (E.binary E.Mul (constant width coefficient) body)
        in
        let terms = List.filter_map Fun.id
            [ term c2 square; term c1 expression;
              if Z.equal c0 Z.zero then None else Some (constant width c0) ] in
        match terms with
        | [] -> offer (constant width Z.zero)
        | head :: tail -> offer (List.fold_left (E.binary E.Plus) head tail))
      !quadratic;
    let rotate_right value amount =
      norm (Z.logor (Z.shift_right value amount) (Z.shift_left value (width - amount))) in
    let logical_left value amount = norm (Z.shift_left value amount) in
    let logical_right value amount = Z.shift_right value amount in
    let arithmetic_right value amount =
      let signed = if Z.testbit value (width - 1) then Z.sub value modulus else value in
      norm (Z.shift_right signed amount)
    in
    let shifted = ref false in
    for amount = 1 to width - 1 do
      let amount_expr = constant width (Z.of_int amount) in
      if not !shifted && check (fun value -> rotate_right value amount) then (
        offer (E.binary E.Ror expression amount_expr); shifted := true);
      if check (fun value -> logical_left value amount) then
        offer (E.binary E.Lsl expression amount_expr);
      if check (fun value -> logical_right value amount) then
        offer (E.binary E.Lsr expression amount_expr);
      if check (fun value -> arithmetic_right value amount) then
        offer (E.binary E.Asr expression amount_expr)
    done;
    !candidates |> List.sort_uniq E.compare

let eval_binary operation left right =
  let width = Bitvector.size_of left in
  let count = Bitvector.value_of right in
  match operation with
  | E.Lsl | E.Lsr | E.Asr ->
      if Z.geq count (Z.of_int width) then
        if operation = E.Asr && Bitvector.is_neg left then Bitvector.fill width
        else Bitvector.zeros width
      else
        let amount = Z.to_int count in
        if operation = E.Lsl then Bitvector.shift_left left amount
        else if operation = E.Lsr then Bitvector.shift_right left amount
        else Bitvector.shift_right_signed left amount
  | E.Ror -> Bitvector.rotate_right left (Z.to_int (Z.rem count (Z.of_int width)))
  | _ -> Term.Bv.binary operation left right

let values_of (problem : Synth_backends.problem) expression =
  let input_index = Hashtbl.create (Array.length problem.inputs) in
  Array.iteri (fun index (input : Synth_backends.input) -> Hashtbl.add input_index input.name index)
    problem.inputs;
  let rec eval sample = function
    | E.Cst value -> value
    | E.Var variable -> sample.Synth_backends.args.(Hashtbl.find input_index variable.name)
    | E.Unary { f; x; _ } -> Term.Bv.unary f (eval sample x)
    | E.Binary { f; x; y; _ } -> eval_binary f (eval sample x) (eval sample y)
    | E.Ite { c; t; e; _ } -> if Bitvector.is_zeros (eval sample c) then eval sample e else eval sample t
    | E.Load _ -> raise Exit
  in
  try Some (Array.map (fun sample -> Bitvector.value_of (eval sample expression)) problem.samples)
  with _ -> None

let synthesize_exact (problem : Synth_backends.problem) =
  if problem.output_size <= 0 || problem.output_size > 64 || Array.length problem.samples < 8 then None
  else
    let started = Unix.gettimeofday () and deadline = Unix.gettimeofday () +. 0.025 in
    let target = Array.map (fun sample -> Bitvector.value_of sample.Synth_backends.res) problem.samples in
    let width = problem.output_size in
    let variables = Array.to_list problem.inputs
      |> List.map (fun (input : Synth_backends.input) -> E.var input.name input.size input.name) in
    let cores = ref [] and next_id = ref 0 and count = ref 0 in
    let seen = Hashtbl.create 2048 in
    let add size expression =
      if !count < 1500 && Unix.gettimeofday () < deadline && not (Hashtbl.mem seen expression) then (
        Hashtbl.add seen expression !next_id; incr next_id; incr count;
        cores := (size, expression) :: !cores)
    in
    List.iter (add 1) variables;
    List.iter (fun variable -> add 2 (E.unary E.Not variable); add 2 (E.unary E.Minus variable)) variables;
    let commutative = [ E.Plus; E.Mul; E.And; E.Or; E.Xor ] in
    let binary = [ E.Plus; E.Minus; E.Mul; E.And; E.Or; E.Xor ] in
    List.iteri
      (fun i left ->
        List.iteri
          (fun j right ->
            if E.sizeof left = E.sizeof right then
              List.iter
                (fun operation ->
                  if not (List.mem operation commutative) || i <= j then
                    if not ((operation = E.Xor || operation = E.Minus) && i = j) then
                      add 3 (E.binary operation left right))
                binary)
          variables)
      variables;
    let size3 = !cores |> List.filter (fun (size, _) -> size = 3) |> List.map snd in
    List.iter (fun core -> add 4 (E.unary E.Not core); add 4 (E.unary E.Minus core)) size3;
    if List.length variables <= 3 then
      List.iter
        (fun left ->
          List.iter
            (fun right ->
              if E.sizeof left = E.sizeof right then
                List.iter (fun operation -> add 5 (E.binary operation left right)) binary)
            variables)
        size3;
    let ordered = List.sort (fun (ls, le) (rs, re) ->
        let order = Int.compare ls rs in if order = 0 then E.compare le re else order) !cores in
    let best = ref None in
    let consider candidate =
      if Synth_backends.well_formed problem candidate then
        match values_of problem candidate with
        | Some values when all2 Z.equal values target ->
            (match !best with
            | None -> best := Some candidate
            | Some previous when Greysynth_utils.Utils.size_of_expr candidate
                                 < Greysynth_utils.Utils.size_of_expr previous ->
                best := Some candidate
            | _ -> ())
        | _ -> ()
    in
    let rec loop = function
      | [] -> ()
      | _ when Unix.gettimeofday () >= deadline -> ()
      | (_, core) :: rest ->
          (if E.sizeof core = problem.output_size then
             match values_of problem core with
             | None -> ()
             | Some values ->
                 analytical_candidates ~width ~target ~expression:core ~values
                 |> List.iter consider);
          loop rest
    in
    loop ordered;
    ignore started;
    !best
