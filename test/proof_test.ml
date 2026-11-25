module E = Libterm.Sexpr.Expr
module P = Rewrite_proof
module U = Greysynth_utils.Utils
module J = Yojson.Basic.Util
let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var name width = E.var name width name
let field name = J.member name
let status json = J.to_string (field "verification" json)
let expect wanted json =
  require (status json = wanted)
    (Printf.sprintf "expected %s, got %s" wanted (Yojson.Basic.to_string json))
let certificate original candidate edges =
  let builder = P.create original in
  List.iter (fun (left, right) -> P.record builder ~pass:"test" left right) edges;
  P.finish builder candidate
let ring_certificate original candidate =
  let builder = P.create original in
  P.record_ring builder ~pass:"ring-test" original candidate;
  P.finish builder candidate
let poly_certificate original candidate =
  let builder = P.create original in
  P.record_poly builder ~pass:"poly-test" original candidate;
  P.finish builder candidate
let linear_mba_certificate original candidate =
  let builder = P.create original in
  P.record_linear_mba builder ~pass:"linear-mba-test" original candidate;
  P.finish builder candidate
let update name value = function
  | `Assoc fields -> `Assoc ((name, value) :: List.remove_assoc name fields)
  | _ -> failwith "object expected"
let map_first_node change json =
  match field "nodes" json with
  | `List (first :: rest) -> update "nodes" (`List (change first :: rest)) json
  | _ -> failwith "nodes expected"
let available =
  Option.is_some Libsolver.bitwuzla_c || Option.is_some Libsolver.bitwuzla_cxx
  || Option.is_some Libsolver.z3

let () =
  let x = var "x" 8 and y = var "y" 8 in
  let load = E.load 1 Machine.LittleEndian x Libterm.Sexpr.Memory.root in
  let load_rejected =
    try ignore (P.create load); false
    with Failure message -> String.length message > 0
  in
  require load_rejected "memory load entered the pure-expression proof graph";
  U.reset_solver_session ();
  let yes, _, _ = U.are_equivalent_seconds x x (Some 1.) in
  let no, _, model =
    U.are_equivalent_seconds ~show_counter_example:true x
      (E.binary E.Plus x (c 8 1)) (Some 1.)
  in
  let timeout, _, _ = U.are_equivalent_seconds x x (Some 0.) in
  let yes_after_reset, _, _ = U.are_equivalent_seconds x x (Some 1.) in
  require (yes = U.Yes && no = U.No && Option.is_some model
           && timeout = U.Timeout && yes_after_reset = U.Yes)
    "incremental solver session leaked state across mixed verdicts";
  U.reset_solver_session ();
  let x32 = var "x" 32 and x64 = var "x" 64 in
  ignore (U.are_equivalent_seconds x32 x32 (Some 1.));
  let width_verdict, _, width_model =
    U.are_equivalent_seconds ~show_counter_example:true x64
      (E.binary E.Plus x64 (c 64 1)) (Some 1.)
  in
  require
    (width_verdict = U.No
     && Option.fold ~none:false
          ~some:(fun model -> List.mem_assoc "x" model && not (List.mem_assoc "x<64>" model))
          width_model)
    "incremental model labels leaked widths from an earlier query";
  U.reset_solver_session ();
  let identity = certificate x x [] in
  expect "proved_compositional" (P.verify ~original:x ~candidate:x identity);
  expect "error" (P.verify ~original:y ~candidate:x identity);
  expect "error" (P.verify ~original:x ~candidate:y identity);
  expect "error" (P.verify ~original:x ~candidate:x
    (map_first_node (update "width" (`Int 0)) identity));
  expect "error" (P.verify ~original:x ~candidate:x
    (map_first_node (fun n -> n |> update "op" (`String "bvnot")
      |> update "args" (`List [`Int 0])) identity));
  expect "error" (P.verify ~original:x ~candidate:x
    (update "semantics" (`String "trust-me") identity));
  let n1 = E.binary E.Plus (E.binary E.Or x y) (E.binary E.And x y) in
  let n2 = E.binary E.Plus x y and n3 = E.binary E.Plus y x in
  let unexplained = certificate n1 n2 [] |> update "proved" (`Bool true) in
  expect "unknown" (P.verify ~original:n1 ~candidate:n2 unexplained);
  let z = var "z" 8 in
  let context term = E.binary E.Plus (E.binary E.Xor term z)
      (E.ite (E.binary E.Eq x y) (E.binary E.And term z) term) in
  let original = context n1 and candidate = context n3 in
  let incomplete = certificate original candidate [n1, n2] in
  expect "unknown" (P.verify ~original ~candidate incomplete);
  (* Every pure operator survives the typed DAG boundary, including sorts. *)
  let operators : Term.binary E.op list =
    [ E.Plus; E.Minus; E.Mul; E.Udiv; E.Sdiv; E.Umod; E.Smod;
      E.And; E.Or; E.Xor; E.Lsl; E.Lsr; E.Asr; E.Rol; E.Ror;
      E.Concat; E.Eq; E.Diff; E.Ule; E.Ult; E.Uge; E.Ugt;
      E.Sle; E.Slt; E.Sge; E.Sgt ] in
  let codec expression = expect "proved_compositional"
      (P.verify ~original:expression ~candidate:expression
         (certificate expression expression [])) in
  List.iter (fun operation -> codec (E.binary operation x y)) operators;
  List.iter codec [ E.unary E.Not x; E.unary E.Minus x;
    E.unary (E.Uext 8) x; E.unary (E.Sext 8) x;
    E.restrict ~lo:2 ~hi:5 x; E.ite (c 1 1) x y;
    c 128 (-1); var "x!1" 16; var "with\000nul" 32 ];
  let rx = var "rx" 64 and ry = var "ry" 64 in
  let factor = E.binary E.And rx ry in
  let k1 = c 64 0x35 and k2 = c 64 0x17 in
  let ring_lhs = E.binary E.Plus (E.binary E.Mul k1 factor)
      (E.binary E.Mul k2 factor) in
  let ring_rhs = E.binary E.Mul (E.binary E.Plus k1 k2) factor in
  let ring_report = P.verify ~original:ring_lhs ~candidate:ring_rhs
      (ring_certificate ring_lhs ring_rhs) in
  expect "proved_compositional" ring_report;
  require (field "ring_proofs" ring_report = `Int 1) "ring proof was not reported";
  let overflow_lhs = E.binary E.Plus (c 64 (-1)) (c 64 1) in
  let overflow_rhs = c 64 0 in
  expect "proved_compositional"
    (P.verify ~original:overflow_lhs ~candidate:overflow_rhs
       (ring_certificate overflow_lhs overflow_rhs));
  let invalid_rhs = E.binary E.Mul (E.binary E.Plus k1 (c 64 1)) factor in
  expect "error"
    (P.verify ~original:ring_lhs ~candidate:invalid_rhs
       (ring_certificate ring_lhs invalid_rhs));
  let factors = List.init 17 (fun _ -> rx) in
  let left_degree = List.fold_left (E.binary E.Mul) (List.hd factors) (List.tl factors) in
  let right_degree = List.fold_right (E.binary E.Mul) (List.tl factors) (List.hd factors) in
  let limited =
    P.verify ~original:left_degree ~candidate:right_degree
      (ring_certificate left_degree right_degree)
  in
  expect "unknown" limited;
  require (field "reason" limited = `String "ring_limit_exceeded")
    "ring degree limit was not reported explicitly";
  let falling variable degree =
    let result = ref variable in
    for offset = 1 to degree - 1 do
      result := E.binary E.Mul !result (E.binary E.Minus variable (c (E.sizeof variable) offset))
    done;
    !result
  in
  List.iter
    (fun (width, degree) ->
      let variable = var (Printf.sprintf "poly_%d_%d" width degree) width in
      let rec v2 n power total =
        if power > n then total else v2 n (power * 2) (total + (n / power))
      in
      let coefficient = Z.shift_left Z.one (max 0 (width - v2 degree 2 0)) in
      let lhs = E.binary E.Mul (E.constant (Bitvector.create coefficient width))
          (falling variable degree) in
      let rhs = c width 0 in
      let report = P.verify ~original:lhs ~candidate:rhs (poly_certificate lhs rhs) in
      expect "proved_compositional" report;
      require (field "poly_proofs" report = `Int 1) "poly proof was not reported")
    [ 8, 4; 16, 6; 32, 20; 64, 20 ];
  let px = var "poly_x" 8 and py = var "poly_y" 8 in
  let multi = E.binary E.Mul (c 8 64)
      (E.binary E.Mul (falling px 3) (falling py 3)) in
  expect "proved_compositional"
    (P.verify ~original:multi ~candidate:(c 8 0) (poly_certificate multi (c 8 0)));
  let off_by_one = E.binary E.Mul (c 8 32)
      (E.binary E.Mul (falling px 3) (falling py 3)) in
  expect "error"
    (P.verify ~original:off_by_one ~candidate:(c 8 0)
       (poly_certificate off_by_one (c 8 0)));
  let px16 = var "poly_x16" 16 and py16 = var "poly_y16" 16 in
  let off_by_one16 = E.binary E.Mul (c 16 8192)
      (E.binary E.Mul (falling px16 3) (falling py16 3)) in
  expect "error"
    (P.verify ~original:off_by_one16 ~candidate:(c 16 0)
       (poly_certificate off_by_one16 (c 16 0)));
  let rec shared depth node =
    if depth = 0 then node else shared (depth - 1) (E.binary E.Plus node node)
  in
  let shared_dag = shared 20 x in
  let shared_with_zero = E.binary E.Plus shared_dag (c 8 0) in
  expect "proved_compositional"
    (P.verify ~original:shared_with_zero ~candidate:shared_dag
       (linear_mba_certificate shared_with_zero shared_dag));
  let linear_vars = List.init 8 (fun index -> var ("lm" ^ string_of_int index) 8) in
  let sum = function
    | head :: tail -> List.fold_left (E.binary E.Plus) head tail
    | [] -> assert false
  in
  let linear_left = sum linear_vars and linear_right = sum (List.rev linear_vars) in
  let linear_report =
    P.verify ~original:linear_left ~candidate:linear_right
      (linear_mba_certificate linear_left linear_right)
  in
  expect "proved_compositional" linear_report;
  require (field "linear_mba_proofs" linear_report = `Int 1)
    "linear MBA proof was not reported";
  let wide_linear_identity count prefix =
    let variables =
      List.init count (fun index -> var (prefix ^ string_of_int index) 8)
    in
    let rec pairs = function
      | left :: right :: rest ->
          E.binary E.Or left right :: E.binary E.And left right :: pairs rest
      | [] -> []
      | _ -> assert false
    in
    sum (pairs variables), sum variables
  in
  List.iter
    (fun count ->
      let left, right = wide_linear_identity count (Printf.sprintf "wide%d_" count) in
      let started = Unix.gettimeofday () in
      let report = P.verify ~original:left ~candidate:right
          (linear_mba_certificate left right) in
      expect "proved_compositional" report;
      require (Unix.gettimeofday () -. started < 0.1)
        (Printf.sprintf "%d-atom sparse linear MBA replay was unexpectedly slow" count))
    [ 10; 12 ];
  let wide_vars = List.init 10 (fun index -> var ("wide_bad" ^ string_of_int index) 8) in
  let wide_sum = sum wide_vars in
  let wide_off_by_one = E.binary E.Plus wide_sum (c 8 1) in
  expect "error"
    (P.verify ~original:wide_off_by_one ~candidate:wide_sum
       (linear_mba_certificate wide_off_by_one wide_sum));
  let wide_mask_left =
    sum (E.binary E.And (List.hd wide_vars) (c 8 5) :: List.tl wide_vars)
  in
  expect "error"
    (P.verify ~original:wide_mask_left ~candidate:wide_sum
       (linear_mba_certificate wide_mask_left wide_sum));
  let wx0 = List.nth wide_vars 0 and wx1 = List.nth wide_vars 1
  and wx2 = List.nth wide_vars 2 in
  let wide_arithmetic_left =
    sum (E.binary E.And (E.binary E.Plus wx0 wx1) wx2
         :: List.filteri (fun index _ -> index >= 3) wide_vars)
  and wide_arithmetic_right =
    sum (E.binary E.And wx0 wx2 :: E.binary E.And wx1 wx2
         :: List.filteri (fun index _ -> index >= 3) wide_vars)
  in
  expect "error"
    (P.verify ~original:wide_arithmetic_left ~candidate:wide_arithmetic_right
       (linear_mba_certificate wide_arithmetic_left wide_arithmetic_right));
  let lx = var "lmx" 8 and ly = var "lmy" 8 and lz = var "lmz" 8 in
  let product = E.binary E.Mul lx ly in
  let correlated_left = E.binary E.Plus (E.binary E.And product lz)
      (E.binary E.Or product lz) in
  let correlated_right = E.binary E.Plus product lz in
  expect "proved_compositional"
    (P.verify ~original:correlated_left ~candidate:correlated_right
       (linear_mba_certificate correlated_left correlated_right));
  let not_sum = E.unary E.Not (E.binary E.Plus lx ly) in
  let negated = E.binary E.Minus
      (E.binary E.Minus (c 8 (-1)) lx) ly in
  expect "proved_compositional"
    (P.verify ~original:not_sum ~candidate:negated
       (linear_mba_certificate not_sum negated));
  let bad_mask = E.binary E.And lx (c 8 5) in
  expect "error"
    (P.verify ~original:bad_mask ~candidate:lx
       (linear_mba_certificate bad_mask lx));
  let bad_partition = E.binary E.Plus (E.binary E.And lx (c 8 1))
      (E.binary E.And (E.unary E.Not lx) (c 8 1)) in
  expect "error"
    (P.verify ~original:bad_partition ~candidate:(c 8 (-1))
       (linear_mba_certificate bad_partition (c 8 (-1))));
  let bad_distribution = E.binary E.And (E.binary E.Plus lx ly) lz in
  let distributed = E.binary E.Plus (E.binary E.And lx lz) (E.binary E.And ly lz) in
  expect "error"
    (P.verify ~original:bad_distribution ~candidate:distributed
       (linear_mba_certificate bad_distribution distributed));
  Printf.printf "proof_test: typed DAG, ring kernel, endpoint binding and incomplete-derivation regressions passed\n";
  if not available then (
    if Sys.getenv_opt "GREYSYNTH_REQUIRE_SOLVER" = Some "1" then
      failwith "proof_test: solver required but unavailable";
    Printf.printf "proof_test: solver-dependent tests unavailable\n")
  else (
    List.iter
      (fun (left, right) ->
        let verdict, _, _ = U.are_equivalent left right (Some 2) in
        require (verdict = U.No) "linear MBA negative was not refuted by SMT")
      [ bad_mask, lx; bad_partition, c 8 (-1); bad_distribution, distributed;
        wide_off_by_one, wide_sum; wide_mask_left, wide_sum;
        wide_arithmetic_left, wide_arithmetic_right ];
    let negative_verdict, _, _ = U.are_equivalent off_by_one (c 8 0) (Some 2) in
    let negative_verdict16, _, _ = U.are_equivalent off_by_one16 (c 16 0) (Some 2) in
    require (negative_verdict = U.No && negative_verdict16 = U.No)
      "off-by-one poly threshold was not refuted by SMT";
    let complete = certificate original candidate [n1, n2; n2, n3] in
    expect "proved_compositional" (P.verify ~original ~candidate complete);
    let bad = certificate x (c 8 0) [x, c 8 0] in
    let bad_report = P.verify ~original:x ~candidate:(c 8 0) bad in
    expect "error" bad_report;
    require (field "equiv" bad_report = `String "ukn")
      "a refuted local edge must not be reported as output refutation";
    (* Extra valid, uncommitted equalities do not obstruct endpoint derivation. *)
    let unused = certificate original candidate
      [n1, n2; n2, n3; E.binary E.Minus x x, c 8 0] in
    expect "proved_compositional" (P.verify ~original ~candidate unused);
    let p = E.binary E.Mul (E.binary E.Plus x z) (E.binary E.Or y z) in
    let lhs = E.binary E.Plus (E.binary E.And p y) (E.binary E.Or p y) in
    let rhs = E.binary E.Plus p y in
    let verdict, method_ = P.prove_equality ~timeout:2. lhs rhs in
    require (verdict = U.Yes && method_ = "abstract")
      "shared nonlinear subterm abstraction should prove the MBA identity";
    let factor = E.binary E.And x y in
    let k1 = c 8 0x35 and k2 = c 8 0xcb in
    let lhs = E.binary E.Plus (E.binary E.Mul k1 factor) (E.binary E.Mul k2 factor) in
    let rhs = E.binary E.Mul (E.binary E.Plus k1 k2) factor in
    let verdict, method_ = P.prove_equality ~timeout:2. lhs rhs in
    require (verdict = U.Yes && method_ = "abstract")
      "small shared factors and nontrivial constants were not abstracted";
    (* A stronger abstraction can be SAT although the original is valid. *)
    let x4 = var "x4" 4 in
    let a = E.binary E.Plus x4 (c 4 1) in
    let b = E.binary E.Plus x4 (c 4 2) in
    let lhs = E.binary E.Plus b (E.binary E.Minus a a) in
    let rhs = E.binary E.Plus (E.binary E.Plus a (c 4 1))
        (E.binary E.Minus b b) in
    let verdict, method_ = P.prove_equality ~timeout:2. lhs rhs in
    require (verdict = U.Yes && method_ = "concrete")
      "SAT abstraction must fall back to the concrete equality";
    (* Capture of a user variable would incorrectly prove this false edge. *)
    let collision = var "$greysynth.proof.0" 8 in
    let p = E.binary E.Plus (E.binary E.Plus x y) z in
    let verdict, _ = P.prove_equality ~timeout:2.
      (E.binary E.Plus p p) (E.binary E.Plus collision collision) in
    require (verdict = U.No) "abstraction variables must be fresh";
    let verdict, _ = P.prove_equality ~timeout:0. n1 n2 in
    require (verdict = U.Timeout) "exhausted proof budget must not imply equivalence";
    Random.init 2027;
    List.iter
      (fun width ->
        let a = var ("ra" ^ string_of_int width) width in
        let b = var ("rb" ^ string_of_int width) width in
        let opaque = E.binary E.Xor a b in
        for index = 0 to 9 do
          let k1 = c width (Random.bits ()) and k2 = c width (Random.bits ()) in
          let left = E.binary E.Mul k1 (E.binary E.Plus opaque k2) in
          let right = E.binary E.Plus (E.binary E.Mul k1 opaque)
              (E.binary E.Mul k1 k2) in
          let report = P.verify ~original:left ~candidate:right
              (ring_certificate left right) in
          expect "proved_compositional" report;
          let verdict, _, _ = U.are_equivalent left right (Some 2) in
          require (verdict = U.Yes)
            (Printf.sprintf "ring/SMT disagreement at width %d case %d" width index)
        done)
      [ 8; 16; 32; 64 ];
    Printf.printf "proof_test: fresh SMT replay, abstraction, ring cross-checks, transitivity and congruence regressions passed\n")
