(* Candidate generation is deterministic; every accepted replacement still
   has to satisfy the common sampling and SMT policy. *)
module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module G = Greysynth
module P = Rewrite_proof

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var width name = E.var name width name
let plus = E.binary E.Plus
let minus = E.binary E.Minus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor

let reset ?(strict = true) () =
  Random.init 42;
  C.evaluator := Sample_evaluator.make 100;
  C.c_nb_samples := 100;
  U.cost_model := U.Legacy;
  C.c_ac_normalization := false;
  C.c_normalization_portfolio := false;
  C.c_preprocessing_portfolio := false;
  C.c_normalization_max_atoms := 6;
  C.c_mba_oracle := "none";
  C.c_mba_oracle_command := "";
  C.c_mba_oracle_timeout := 2;
  C.c_mba_oracle_calls := 4;
  C.c_reject_non_equiv_simplifications := strict;
  C.c_equiv_timeout := 5;
  C.g_total_timeout := 0.;
  C.g_has_timedout := false;
  R.reset ()

let test_external_oracle_adapter () =
  reset ();
  let script = Filename.temp_file "greysynth-oracle-" ".sh" in
  let marker = Filename.temp_file "greysynth-oracle-" ".calls" in
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun path -> try Sys.remove path with Sys_error _ -> ()) [ script; marker ])
    (fun () ->
      Out_channel.with_open_text script (fun channel ->
          Printf.fprintf channel "#!/bin/sh\nprintf 'call\\n' >> %s\nprintf 'v0\\n'\n"
            (Filename.quote marker));
      Unix.chmod script 0o700;
      C.c_mba_oracle := "rumba";
      C.c_mba_oracle_command := script;
      let x = var 64 "oracle_x" in
      let source = plus x (c 64 0) in
      (match N.oracle_candidate source with
      | Some candidate ->
          require (E.is_equal candidate x) "MBA oracle variable mapping changed"
      | None -> failwith "MBA oracle adapter returned no candidate");
      let square = mul x x in
      let large = plus (plus square square) square in
      ignore (N.run large);
      ignore (N.run (E.unary (E.Uext 8) large));
      let calls = In_channel.with_open_text marker In_channel.input_lines in
      require (List.length calls = 3)
        "MBA oracle did not prioritize maximal pure subtrees under mixed roots")

let test_fail_closed () =
  reset ();
  let x = var 32 "x" in
  let original = plus x (c 32 0) in
  Hashtbl.replace R.proofs (R.proof_key original x) U.Unknown;
  let result = N.run original in
  require (E.is_equal result original) "normalizer accepted an unknown proof";
  require (!(R.inconclusive) > 0) "normalizer bypassed the proof boundary"

let test_metric_minimum () =
  reset ();
  U.cost_model := U.Legacy;
  let original = E.unary (E.Sext 24) (E.restrict ~lo:8 ~hi:15 (var 32 "x")) in
  let result = N.run original in
  require (U.size_of_expr original = 1) "legacy cast/extract metric changed";
  require (U.cost_of_expr U.PaperAst original = 3) "paper AST does not count conversions";
  require (U.cost_of_expr U.Readability original = 5) "readability conversion cost changed";
  let quotient = E.binary E.Udiv (var 32 "x") (var 32 "y") in
  let sum = E.binary E.Plus (var 32 "x") (var 32 "y") in
  require
    (U.cost_of_expr U.Instruction quotient > U.cost_of_expr U.Instruction sum)
    "instruction cost does not penalize division";
  require (E.is_equal original result) "normalizer rewrote a metric-minimum input";
  require (!(R.checked) = 0) "minimum input triggered a speculative rewrite"

let test_partial_timeout () =
  reset ~strict:false ();
  let x = var 32 "x" and y = var 32 "y" in
  let left = plus x (c 32 0) and right = plus y (c 32 0) in
  let original = plus left right in
  let bank = !(C.evaluator) in
  C.evaluator :=
    { bank with node_to_outhash = (fun node ->
        if E.is_equal node right then raise C.Timeout_exception;
        bank.node_to_outhash node) };
  let result = N.run original in
  require !(C.g_has_timedout) "normalizer did not record its timeout";
  require (E.is_equal result (plus x right))
    "normalizer timeout discarded a completed child rewrite"

let prove_shrinks name original maximum =
  reset ();
  let result = N.run original in
  require (U.size_of_expr result <= maximum)
    (Printf.sprintf "%s: expected size <= %d, got %d from %d" name maximum
       (U.size_of_expr result) (U.size_of_expr original));
  require (!(R.proved) > 0) (name ^ ": no replacement was proved");
  let verdict, _, _ = U.are_equivalent original result (Some 5) in
  require (verdict = U.Yes) (name ^ ": independent whole-expression proof failed")

let test_peepholes () =
  let x = var 8 "x" and y = var 8 "y" in
  let condition = E.binary E.Eq x y in
  List.iter (fun (name, original, maximum) -> prove_shrinks name original maximum)
    [ "boolean conditional", E.ite condition (c 1 1) (c 1 0), 3;
      "conditional mask", E.ite condition (c 8 (-1)) (c 8 0), 3;
      "conditional value mask", E.ite condition x (c 8 0), 5;
      "unsigned lower bound", E.binary E.Ult x (c 8 0), 1;
      "unsigned lower inclusive", E.binary E.Uge x (c 8 0), 1;
      "unsigned upper inclusive", E.binary E.Ule x (c 8 255), 1;
      "unsigned upper bound", E.binary E.Ugt x (c 8 255), 1;
      "signed lower bound", E.binary E.Slt x (c 8 128), 1;
      "signed lower inclusive", E.binary E.Sge x (c 8 128), 1;
      "signed upper inclusive", E.binary E.Sle x (c 8 127), 1;
      "signed upper bound", E.binary E.Sgt x (c 8 127), 1;
      "and complement", band x (E.unary E.Not x), 1;
      "or complement", bor x (E.unary E.Not x), 1;
      "xor complement", bxor x (E.unary E.Not x), 1;
      "add inverse", plus x (E.unary E.Minus x), 1;
      "low mask", band x (c 8 31), 1;
      "logical shift", E.binary E.Lsr x (c 8 3), 1;
      "arithmetic overshift", E.binary E.Asr x (c 8 255), 1;
      "unsigned power-of-two quotient", E.binary E.Udiv x (c 8 8), 1;
      "unsigned power-of-two remainder", E.binary E.Umod x (c 8 8), 1;
      "zero divisor", E.binary E.Udiv x (c 8 0), 1;
      "zero remainder divisor", E.binary E.Umod x (c 8 0), 1;
      "shifted divisor", E.binary E.Udiv x (E.binary E.Lsl y (c 8 2)), 3;
      "shifted constant numerator", E.binary E.Udiv (c 8 64)
          (E.binary E.Lsl x (c 8 1)), 3;
      "divisor shift overflow", E.binary E.Udiv x (E.binary E.Lsl y (c 8 8)), 1;
      "adjacent slices", E.binary E.Concat (E.restrict ~lo:4 ~hi:7 x)
          (E.restrict ~lo:0 ~hi:3 x), 1 ]

let test_linear_mba () =
  let x = var 32 "x" and y = var 32 "y" in
  List.iter (fun (name, original, maximum) -> prove_shrinks name original maximum)
    [ "sum of union and intersection", plus (bor x y) (band x y), 3;
      "carry decomposition", plus (bxor x y) (mul (c 32 2) (band x y)), 3;
      "double union", minus (mul (c 32 2) (bor x y)) (bxor x y), 3;
      "negation and offset", minus (E.unary E.Minus x) (c 32 1), 2;
      "scaled MBA", plus (mul (c 32 3) (bor x y))
          (mul (c 32 3) (band x y)), 5;
      "complemented arithmetic", plus (plus (E.unary E.Not (plus x y)) x)
          (plus y (c 32 1)), 1 ];
  let a = var 16 "a" and b = var 16 "b" and d = var 16 "c" in
  let abc = band a (band b d) in
  let two_value =
    plus
      (plus (bor (bxor a b) (bxor a d))
         (mul (c 16 65469) (E.unary E.Not abc)))
      (mul (c 16 65470) abc)
  in
  reset ();
  C.c_equiv_timeout := 1;
  R.start_recording two_value;
  let result = N.run two_value in
  require (U.size_of_expr result <= 7)
    "two-value Boolean recovery exceeded the one-second local proof budget";
  let certificate = P.finish (Option.get !(R.journal)) result in
  let report = P.verify ~timeouts:[ 1. ] ~original:two_value ~candidate:result certificate in
  require
    (Yojson.Basic.Util.member "verification" report = `String "proved_compositional")
    "two-value Boolean micro-steps did not replay within one second"

let test_five_atom_boolean_recovery () =
  let variables = Array.init 5 (fun index -> var 8 ("p" ^ string_of_int index)) in
  let conjunction terms =
    match terms with
    | head :: tail -> List.fold_left band head tail
    | [] -> c 8 (-1)
  in
  let disjunction terms =
    match terms with
    | head :: tail -> List.fold_left bor head tail
    | [] -> c 8 0
  in
  let minterms =
    List.init 32 Fun.id
    |> List.filter (fun assignment -> Z.popcount (Z.of_int assignment) mod 2 = 1)
    |> List.map (fun assignment ->
           Array.to_list variables
           |> List.mapi (fun index variable ->
                  if assignment land (1 lsl index) = 0 then E.unary E.Not variable
                  else variable)
           |> conjunction)
  in
  prove_shrinks "five-atom parity recovery" (disjunction minterms) 9

let test_semilinear_masks () =
  let x16 = var 16 "mask16" in
  prove_shrinks "complementary masks"
    (plus (band x16 (c 16 0xff)) (band x16 (c 16 0xff00))) 1;
  let x32 = var 32 "mask32" in
  prove_shrinks "disjoint partial masks"
    (plus (band x32 (c 32 0x00ff)) (band x32 (c 32 0xff00))) 3

let test_associative_canonicalization () =
  let prove_ac name original maximum =
    reset ();
    C.c_ac_normalization := true;
    let result = N.run original in
    require (U.size_of_expr result <= maximum)
      (Printf.sprintf "%s: expected size <= %d, got %d" name maximum
         (U.size_of_expr result));
    let verdict, _, _ = U.are_equivalent original result (Some 5) in
    require (verdict = U.Yes) (name ^ ": proof failed")
  in
  let x = var 16 "x" and y = var 16 "y" in
  List.iter (fun (name, original, maximum) -> prove_ac name original maximum)
    [ "xor cancellation", bxor (bxor x y) x, 1;
      "coefficient collection", plus (plus x x) x, 3;
      "negative term collection",
        plus (plus x (E.unary E.Minus y)) (E.unary E.Minus x), 2;
      "shift coefficient collection",
        plus (E.binary E.Lsl x (c 16 2)) (E.binary E.Lsl x (c 16 2)), 3;
      "idempotent conjunction", band (band x y) x, 3 ]

let test_minterm_ring_edge_cases () =
  let check label source_text candidate_text =
    reset ();
    C.c_equiv_timeout := 1;
    let source = String_to_sexpr.parse source_text in
    let candidate = String_to_sexpr.parse candidate_text in
    let equalities, ring_equalities =
      match N.minterm_ring_proof source candidate with
      | Some proof -> proof
      | None -> failwith (label ^ ": minterm proof construction failed")
    in
    let builder = P.create source in
    List.iter (fun (left, right) -> P.record builder ~pass:label left right) equalities;
    List.iter (fun (left, right) -> P.record_ring builder ~pass:label left right)
      ring_equalities;
    let report = P.verify ~timeouts:[ 1. ] ~original:source ~candidate
        (P.finish builder candidate) in
    require
      (Yojson.Basic.Util.member "verification" report = `String "proved_compositional")
      (label ^ ": " ^ Yojson.Basic.to_string report)
  in
  check "non-variable target" "(a^b)+2*(a&b)" "a+b";
  check "large coefficients to zero"
    "0x123456789abcdef1*(a&b)+0xedcba9876543210f*(a&b)" "0";
  check "constant offset" "~a+a" "-1";
  check "compound atom"
    "10*((x*y)^z)+20*((x*y)&z)-9*(x*y)-10*z" "x*y";
  check "constant shift" "a<<3" "8*a";
  reset ();
  let source = String_to_sexpr.parse
      "10*((x*y)^z)+20*((x*y)&z)-9*(x*y)-10*z" in
  let result = N.run source in
  require (E.is_equal result (String_to_sexpr.parse "x*y"))
    "non-variable linear candidate was not wired into normalization"

let test_ring_certified_linear_mba () =
  reset ();
  C.c_equiv_timeout := 1;
  let source =
    String_to_sexpr.parse
      "-1*(a&b)+10*(a&~b)+2*a+11*~(a|b)-11*~b"
  in
  let expected = var 64 "a" in
  R.start_recording source;
  let result = N.run source in
  require (E.is_equal result expected)
    "ring-certified linear MBA did not recover the variable";
  let certificate = P.finish (Option.get !(R.journal)) result in
  let report = P.verify ~timeouts:[ 1. ] ~original:source ~candidate:result certificate in
  require
    (Yojson.Basic.Util.member "verification" report = `String "proved_compositional")
    ("ring-certified linear MBA did not replay: " ^ Yojson.Basic.to_string report);
  require (Yojson.Basic.Util.member "ring_proofs" report = `Int 1)
    "linear MBA certificate did not use the ring kernel"

let test_sparse_ring_normalization () =
  let check label source expected =
    reset ();
    R.start_recording source;
    let result = N.run source in
    let expected_match =
      E.is_equal result expected
      || (match U.are_equivalent result expected (Some 2) with
          | U.Yes, _, _ -> true
          | _ -> false)
    in
    require expected_match
      (label ^ ": sparse ring result mismatch: " ^ U.pp result);
    let report = P.verify ~timeouts:[ 1. ] ~original:source ~candidate:result
        (P.finish (Option.get !(R.journal)) result) in
    require
      (Yojson.Basic.Util.member "verification" report = `String "proved_compositional")
      (label ^ ": sparse ring certificate failed")
  in
  let x = var 64 "ring_x" and y = var 64 "ring_y" in
  let xy = mul x y in
  check "two-term polynomial cancellation"
    (minus (plus (mul (c 64 3) xy) (mul (c 64 5) xy)) (mul (c 64 8) xy))
    (c 64 0);
  check "formal polynomial composition"
    (minus (plus x (mul (c 64 2) (mul x x))) (mul (c 64 2) (mul x x))) x;
  let null_term =
    mul (E.constant (Bitvector.create (Z.shift_left Z.one 63) 64))
      (mul x (minus x (c 64 1)))
  in
  check "quadratic null polynomial" null_term (c 64 0);
  check "quadratic null-polynomial composition" (plus x null_term) x;
  let a = var 64 "factor_a" and b = var 64 "factor_b" in
  let factor = band x (E.unary E.Not y) in
  let factored_source =
    plus (mul factor (bxor a b))
      (mul (c 64 2) (mul factor (band a b)))
  in
  check "multiplicative cofactor reduction" factored_source
    (mul factor (plus a b))

let test_compositional_polynomial_identity () =
  let x = var 64 "px" and y = var 64 "py" in
  let m1 = band x y in
  let first = mul m1 (bor x y) in
  let second = mul (band x (E.unary E.Not y)) (band (E.unary E.Not x) y) in
  let check label original expected =
    reset ();
    R.start_recording original;
    let result = N.run original in
    require (E.is_equal result expected) (label ^ ": identity was not recovered");
    let builder = Option.get !(R.journal) in
    let certificate = P.finish builder result in
    let report = P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate:result certificate in
    require
      (Yojson.Basic.Util.member "verification" report = `String "proved_compositional")
      (label ^ ": micro-steps did not replay compositionally")
  in
  check "polynomial partition" (plus first second) (mul x y);
  let commuted_second =
    mul (band (E.unary E.Not y) x) (band y (E.unary E.Not x))
  in
  check "commuted polynomial partition" (plus commuted_second first) (mul x y);
  check "scaled polynomial partition"
    (plus (mul (c 64 3) first) (mul (c 64 3) second))
    (mul (c 64 3) (mul x y))

let test_normalization_portfolio () =
  reset ();
  let x = var 64 "x" and y = var 64 "y" and z = var 64 "z" in
  let w = var 64 "w" and a = var 64 "a" and b = var 64 "b" in
  let carry p q = plus (bxor p q) (mul (c 64 2) (band p q)) in
  let original =
    minus
      (minus
         (minus
            (minus
               (minus (plus (plus (carry x y) (carry z w)) (plus (bor a b) (band a b))) x)
               y)
            z)
         w)
      a
  in
  R.start_recording original;
  let direct = N.run original in
  require (E.is_equal direct b) "six-atom linear normalization failed";
  let baseline_certificate = P.finish (Option.get !(R.journal)) direct in
  let baseline_edges =
    Yojson.Basic.Util.member "equalities" baseline_certificate
    |> Yojson.Basic.Util.to_list |> List.length
  in
  reset ();
  C.c_ac_normalization := true;
  R.start_recording original;
  let ac_result = N.run original in
  let ac_certificate = P.finish (Option.get !(R.journal)) ac_result in
  let ac_edges =
    Yojson.Basic.Util.member "equalities" ac_certificate
    |> Yojson.Basic.Util.to_list |> List.length
  in
  reset ();
  C.c_normalization_portfolio := true;
  R.start_recording original;
  let result = G.run_normalization original in
  require (E.is_equal result b) "normalization portfolio did not select the best branch";
  require (!(R.proved) > 0) "normalization portfolio bypassed local proofs";
  let certificate = P.finish (Option.get !(R.journal)) result in
  let portfolio_edges =
    Yojson.Basic.Util.member "equalities" certificate
    |> Yojson.Basic.Util.to_list |> List.length
  in
  let selected_edges =
    if E.is_equal result ac_result && not (E.is_equal result direct) then ac_edges
    else baseline_edges
  in
  require (portfolio_edges = selected_edges)
    "normalization portfolio retained discarded-branch obligations"

let test_preprocessing_portfolio () =
  let x = var 32 "portfolio_x" and y = var 32 "portfolio_y" in
  let original = plus (plus (bxor x y) (mul (c 32 2) (band x y))) (c 32 0) in
  let run ac portfolio =
    reset ();
    C.c_normalization := true;
    C.c_oes := true;
    C.c_fast_simplify := false;
    C.c_ac_normalization := ac;
    C.c_preprocessing_portfolio := portfolio;
    G.run_preprocessing_portfolio (Some original) original
  in
  let baseline = run false false in
  let experimental = run true false in
  let selected = run true true in
  let expected = min (U.size_of_expr baseline) (U.size_of_expr experimental) in
  require (U.size_of_expr selected = expected)
    "preprocessing portfolio did not retain the cheaper complete branch"

let test_nonlinear_is_opaque () =
  reset ();
  let x = var 8 "x" and y = var 8 "y" in
  (* x*x=x for one-bit assignments, but not for arbitrary words. A
     truth-table normalizer must not expand the nonlinear operations. *)
  let original = minus (plus (mul x x) (mul y y)) (plus x y) in
  let result = N.run original in
  let labels = Hashtbl.create 2 in
  Hashtbl.add labels x (c 8 2);
  Hashtbl.add labels y (c 8 0);
  let value = (Sample_evaluator.make 1).eval_label result 0 labels in
  require (Bitvector.equal value (Bitvector.of_int ~size:8 2))
    "one-bit nonlinear coincidence became a word identity";
  let verdict, _, _ = U.are_equivalent original result (Some 5) in
  require (verdict = U.Yes) "opaque nonlinear normalization changed semantics"

let solver_available =
  Option.is_some Libsolver.bitwuzla_cxx
  || Option.is_some Libsolver.bitwuzla_c
  || Option.is_some Libsolver.z3

let () =
  test_external_oracle_adapter ();
  test_fail_closed ();
  test_metric_minimum ();
  test_partial_timeout ();
  print_endline "normalization_test: fail-closed, metric-minimum and partial-timeout checks passed";
  if solver_available then (
    test_peepholes ();
    test_linear_mba ();
    test_five_atom_boolean_recovery ();
    test_semilinear_masks ();
    test_associative_canonicalization ();
    test_minterm_ring_edge_cases ();
    test_ring_certified_linear_mba ();
    test_sparse_ring_normalization ();
    test_compositional_polynomial_identity ();
    test_normalization_portfolio ();
    test_preprocessing_portfolio ();
    test_nonlinear_is_opaque ();
    print_endline "normalization_test: 58 solver-backed normalization regressions passed")
  else if Sys.getenv_opt "GREYSYNTH_REQUIRE_SOLVER" = Some "1" then
    failwith "normalization_test requires an installed SMT solver"
  else print_endline "normalization_test: proof regressions skipped (no solver installed)"
