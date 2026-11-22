(* Exercise the actual rewrite boundaries with deterministic synthesis mocks. *)
module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module O = Greysynth__Oes
module S = Greysynth__Synthesis
module G = Greysynth
module L = Greysynth__Logging

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let x = E.var "x" 64 "x"
let y = E.var "y" 64 "y"
let zero = c 64 0
let plus = E.binary E.Plus

let reset ?(strict = false) () =
  Random.init 42;
  C.evaluator := Sample_evaluator.make 100;
  C.c_nb_samples := 100;
  C.c_reject_non_equiv_simplifications := strict;
  C.c_equiv_timeout := 5;
  C.c_oes_extended := false;
  C.c_local_extend := false;
  C.c_local_extend_depth := 8;
  C.c_oes_fixedpoint := false;
  C.c_oes_candidate_limit := 4;
  C.c_local_cache := false;
  C.c_add_constants_to_synthesis := false;
  C.c_balanced_tree := false;
  C.c_sampling_strategy := C.RealValues;
  C.c_current_mode_is_global := false;
  C.g_total_timeout := 0.;
  C.g_has_timedout := false;
  C.c_synthesizer_name := "regression mock";
  C.c_synthesizer := (fun _ -> None);
  R.reset ()

let at_xy expression vx vy =
  let labels = Hashtbl.create 2 in
  Hashtbl.add labels x (c 64 vx);
  Hashtbl.add labels y (c 64 vy);
  (Sample_evaluator.make 1).eval_label expression 0 labels

let expect_same_at expression candidate vx vy =
  require (Bitvector.equal (at_xy expression vx vy) (at_xy candidate vx vy))
    (Printf.sprintf "rewrite changes x=%d, y=%d" vx vy)

let test_oes_legacy_collision () =
  reset ();
  let large = E.constant (Bitvector.create (Z.shift_left Z.one 62) 64) in
  let a = plus x large and b = plus (plus y large) zero in
  let original = E.binary E.Xor a b in
  let once = fst (O.linear_simplify ~seed:false original) in
  let result = fst (O.linear_simplify ~seed:false once) in
  require (Bitvector.equal (at_xy original 0 1) (Bitvector.ones 64))
    "hash regression counterexample is wrong";
  List.iter (fun (vx, vy) -> expect_same_at original result vx vy)
    [ (0, 1); (1, 0); (17, 29); (-1, 7) ];
  require (U.size_of_expr result <= U.size_of_expr original)
    "OES enlarged the result"

let test_strict_oes_unknown () =
  reset ~strict:true ();
  let original = plus x zero in
  Hashtbl.add R.proofs (original, x) U.Unknown;
  let result, count = O.linear_simplify ~seed:false original in
  require (E.compare original result = 0) "OES accepted an unproven rewrite";
  require (!count = 0) "rejected OES rewrite was counted";
  require (!(R.inconclusive) > 0) "OES did not reach the proof boundary"

let test_strict_relational_unknown () =
  reset ~strict:true ();
  let original = plus (E.binary E.Or x y) (E.binary E.And x y) in
  Hashtbl.add R.proofs (original, plus x y) U.Unknown;
  Hashtbl.add R.proofs (original, plus y x) U.Unknown;
  let result, count = O.relational_pass original in
  require (E.compare original result = 0)
    "relational pass accepted an unproven rewrite";
  require (count = 0) "rejected relational rewrite was counted";
  require (!(R.inconclusive) > 0) "relational pass did not check its candidate"

let test_strict_cache_unknown () =
  let run global =
    reset ~strict:true ();
    C.c_local_cache := true;
    let chains = Array.make 5 x in
    for i = 1 to 4 do chains.(i) <- plus chains.(i - 1) zero done;
    Array.iter
      (fun a -> Array.iter (fun b -> Hashtbl.replace R.proofs (a, b) U.Unknown) chains)
      chains;
    (* Both traversal orders encounter a large chain after a small cached
       chain. No backend rewrite is offered, isolating the cache-hit path. *)
    let original =
      plus (plus chains.(4) chains.(2)) (plus chains.(2) chains.(4))
    in
    let result =
      if global then S.simplify_global 1 1 original
      else S.simplify_with_horizon 2 1 1 original
    in
    require (U.size_of_expr result = U.size_of_expr original)
      "semantic cache bypassed strict verification";
    require (!(R.inconclusive) > 0) "semantic cache test missed the proof boundary"
  in
  run false;
  run true

let test_false_backend_candidate () =
  reset ();
  let original = plus x (c 64 1) in
  let template, labels = S.truncate original 1 in
  C.c_synthesizer := (fun _ -> Some zero);
  require (S.synthesize ~original template labels 1 1 = None)
    "a backend result that fails samples was accepted in heuristic mode";
  require (!(R.sample_rejections) > 0) "backend result was not independently checked"

let test_raw_candidate_fallback () =
  reset ();
  let quotient = E.binary E.Udiv zero x in
  let original = plus quotient zero in
  let template, labels = S.truncate original 2 in
  let cut = Hashtbl.fold (fun leaf _ _ -> leaf) labels zero in
  C.c_synthesizer := (fun _ -> Some (E.binary E.Udiv zero cut));
  match S.synthesize ~original template labels 1 1 with
  | Some (_, candidate, _) ->
      (* 0 / x is all ones at x=0 under SMT-LIB. The postprocessor must
         preserve the raw quotient instead of proposing the old 0/x -> 0 rule. *)
      require (E.compare candidate quotient = 0)
        "valid raw synthesis was changed by algebraic postprocessing";
      require (!(R.sample_rejections) = 0)
        "removed zero-division rewrite still produced a candidate";
      expect_same_at original candidate 0 0;
      expect_same_at original candidate 17 0
  | None -> failwith "valid raw candidate was not rescued"

let test_preparation_exceptions () =
  let huge = E.constant (Bitvector.create (Z.shift_left Z.one 63) 64) in
  let cases =
    [ E.binary E.Udiv (c 64 1) zero;
      E.binary E.Lsl (c 64 1) huge ]
  in
  List.iter
    (fun raw ->
      reset ();
      let original = plus raw zero in
      let labels = Hashtbl.create 1 in
      C.c_synthesizer := (fun _ -> Some raw);
      match S.synthesize ~original original labels 1 1 with
      | Some (_, candidate, _) ->
          require (U.size_of_expr candidate < U.size_of_expr original)
            "candidate preparation did not preserve a shrinking result";
          expect_same_at original candidate 0 0
      | None -> failwith "candidate preparation exception lost the raw result")
    cases

let test_restored_size () =
  reset ();
  let big = ref x in
  for _ = 1 to 10 do big := plus !big zero done;
  let cut = E.var "cut" 64 "cut" in
  let labels = Hashtbl.create 1 in
  Hashtbl.add labels cut !big;
  let template = plus (plus (E.binary E.Mul cut (c 64 3)) zero) zero in
  let original = S.replace_greek_vars template labels in
  let backend_candidate = plus (plus cut cut) cut in
  require (U.size_of_expr backend_candidate < U.size_of_expr template)
    "size regression needs a smaller synthesis template";
  let restored =
    S.replace_greek_vars (U.binsec_simplify backend_candidate) labels
  in
  require (U.size_of_expr restored > U.size_of_expr original)
    "size regression needs an expanded concrete result";
  expect_same_at original restored 19 0;
  C.c_synthesizer := (fun _ -> Some backend_candidate);
  require (S.synthesize ~original template labels 1 1 = None)
    "smaller template expanded the original subtree"

let test_smallest_cut_representative () =
  reset ();
  let larger = plus x zero in
  List.iter
    (fun original ->
      let _, labels = S.truncate original 1 in
      require (Hashtbl.length labels = 1)
        "equivalent cut leaves were not grouped";
      Hashtbl.iter
        (fun _ representative ->
          require (E.compare representative x = 0)
            "a larger repeated cut leaf replaced the smallest representative")
        labels)
    [ plus x larger; plus larger x ]

let test_ite_substitution () =
  let cond = E.var "cut_cond" 1 "cut_cond" in
  let lhs = E.var "cut_then" 64 "cut_then" in
  let rhs = E.var "cut_else" 64 "cut_else" in
  let condition = E.binary E.Eq x zero in
  let labels = Hashtbl.create 3 in
  Hashtbl.add labels cond condition;
  Hashtbl.add labels lhs x;
  Hashtbl.add labels rhs y;
  let result = S.replace_greek_vars (E.ite cond lhs rhs) labels in
  require (E.compare result (E.ite condition x y) = 0)
    "cut labels remain inside a conditional"

let test_synthesis_partial_timeout () =
  let run global =
    reset ();
    let left = plus (plus x zero) zero in
    let right = plus (plus y zero) zero in
    let original = plus left right in
    let calls = ref 0 in
    C.c_synthesizer := (fun problem ->
        incr calls;
        if not global && !calls = 1 then None
        else if !calls = (if global then 1 else 2) then (
          require (Array.length problem.inputs = 1)
            "timeout regression expected one input in its first child";
          let input = problem.inputs.(0) in
          Some (E.var input.name input.size input.name))
        else raise C.Timeout_exception);
    let result =
      if global then S.simplify_global 1 1 original
      else S.simplify_with_horizon 2 1 1 original
    in
    require !(C.g_has_timedout) "partial traversal did not record its timeout";
    require (E.compare result (plus x right) = 0)
      "timeout discarded an already validated child rewrite";
    require (!calls = (if global then 2 else 3))
      "synthesis continued after exhausting its budget";
    expect_same_at original result 17 29
  in
  run false;
  run true

let test_oes_partial_timeout () =
  reset ();
  let left = plus (plus x zero) zero in
  let right = plus (plus y zero) zero in
  let original = plus left right in
  let bank = !(C.evaluator) in
  let right_visits = ref 0 in
  C.evaluator :=
    { bank with node_to_outhash = (fun node ->
        if E.compare node right = 0 then (
          incr right_visits;
          (* First visit builds the cache; second visit is the rewrite pass. *)
          if !right_visits = 2 then raise C.Timeout_exception);
        bank.node_to_outhash node) };
  let result, count = O.linear_simplify ~seed:false original in
  require !(C.g_has_timedout) "OES did not record its timeout";
  require (E.compare result (plus x right) = 0)
    "OES timeout discarded its completed left child";
  require (!count = 1) "OES partial rewrite count is wrong";
  expect_same_at original result 17 29

let test_larger_proof_budget_retries () =
  reset ~strict:true ();
  let original = plus x zero in
  Hashtbl.replace R.proofs (original, x) U.Timeout;
  Hashtbl.replace R.proof_budgets (original, x) 1.;
  C.c_equiv_timeout := 5;
  require (R.accepts ~pass:"retry-test" original x)
    "larger proof budget did not retry an inconclusive obligation";
  require (!(R.proved) = 1) "retried proof was not recorded"

let test_chs_horizon_restart () =
  reset ~strict:true ();
  C.c_oes := false;
  C.c_check_equiv := false;
  C.c_synthesis_timeout := 1;
  C.c_synthesis_repeat := 1;
  let padded value = plus (plus value zero) zero in
  let left = padded x and right = padded y in
  let original = plus (E.binary E.Or left right) (E.binary E.And left right) in
  let calls = ref 0 in
  C.c_synthesizer := (fun (problem : Greysynth__Synth_backends.problem) ->
      incr calls;
      let input index =
        let item = problem.inputs.(index) in
        E.var item.name item.size item.name
      in
      match !calls, Array.length problem.inputs with
      | 1, _ -> None (* force the first root attempt to miss *)
      | _, 1 -> Some (input 0)
      | _, 2 -> Some (plus (input 0) (input 1))
      | _ -> None);
  let best = ref original in
  G.chs (Some original) best;
  require (U.size_of_expr !best = 3)
    "CHS did not revisit a small horizon after child reductions";
  let verdict, _, _ = U.are_equivalent original !best (Some 5) in
  require (verdict = U.Yes) "CHS horizon restart changed semantics"

let solver_available =
  Option.is_some Libsolver.bitwuzla_cxx
  || Option.is_some Libsolver.bitwuzla_c
  || Option.is_some Libsolver.z3

let test_context_proof () =
  reset ~strict:true ();
  let original = plus (plus x (E.unary E.Not x)) (c 64 1) in
  let template, labels = S.truncate original 2 in
  require (Hashtbl.length labels = 2) "context regression did not cut both correlated leaves";
  let independent_verdict, _, _ = U.are_equivalent template zero (Some 5) in
  require (independent_verdict = U.No)
    "correlated labels unexpectedly proved equal as independent inputs";
  C.c_synthesizer := (fun _ -> Some zero);
  match S.synthesize ~original template labels 1 1 with
  | Some (_, candidate, _) ->
      require (E.compare candidate zero = 0) "context rewrite returned the wrong result";
      require (!(R.proved) = 1) "context rewrite was not proved"
  | None -> failwith "valid context-dependent rewrite was rejected"

let test_balanced_targets () =
  reset ();
  let vars = List.init 8 (fun index -> E.var ("v" ^ string_of_int index) 64 ("v" ^ string_of_int index)) in
  let skewed = List.fold_left plus (List.hd vars) (List.tl vars) in
  C.c_balanced_tree := false;
  let plain, plain_labels = S.truncate skewed 2 in
  C.c_balanced_tree := true;
  let balanced, balanced_labels = S.truncate skewed 2 in
  require (E.compare plain balanced <> 0) "balanced_tree did not change the CHS target";
  require (Hashtbl.length plain_labels <> Hashtbl.length balanced_labels)
    "balanced_tree did not change the horizon cut";
  C.c_balanced_tree := false

let test_sampling_strategies () =
  reset ();
  C.c_nb_samples := 8;
  C.evaluator := Sample_evaluator.make 8;
  let label = E.var "alpha" 8 "alpha" in
  let relations = Hashtbl.create 1 in
  Hashtbl.add relations label (c 8 42);
  let problem strategy =
    C.c_sampling_strategy := strategy;
    S.make_problem label relations 1 1
  in
  let real = problem C.RealValues in
  require
    (Array.for_all (fun (sample : Greysynth__Synth_backends.sample) ->
         Bitvector.equal sample.args.(0) (Bitvector.of_int ~size:8 42)
         && Bitvector.equal sample.args.(0) sample.res) real.samples)
    "real sampling did not preserve contextual label values";
  let labels = problem C.LabelValues in
  require
    (Array.exists (fun (sample : Greysynth__Synth_backends.sample) ->
         not (Bitvector.equal sample.args.(0) (Bitvector.of_int ~size:8 42))) labels.samples)
    "label sampling did not generate independent inputs";
  require
    (Array.for_all (fun (sample : Greysynth__Synth_backends.sample) ->
         Bitvector.equal sample.args.(0) sample.res) labels.samples)
    "label sampling did not evaluate the independent target";
  let wrong = problem C.WrongNaive in
  require
    (Array.exists (fun (sample : Greysynth__Synth_backends.sample) ->
         not (Bitvector.equal sample.args.(0) sample.res)) wrong.samples)
    "wrong_naive no longer represents the mismatched ablation";
  C.c_sampling_strategy := C.RealValues

let test_oes_proof_fallback () =
  reset ~strict:true ();
  let one_sample = Sample_evaluator.make 1 in
  C.evaluator := { one_sample with is_node_constant = (fun _ -> None) };
  let useful = plus x y in
  let original = plus useful zero in
  let result, rewrites = O.linear_simplify ~seed:false original in
  require (E.compare result useful = 0)
    "OES did not fall back from smaller false representatives";
  require (!rewrites = 1) "OES proof-aware fallback count is wrong";
  require (!(R.sample_rejections) >= 1)
    "OES fallback did not exercise the false sampled representatives"

let test_legacy_simplifier_edges () =
  let x8 = E.var "x8" 8 "x8" in
  let eval expression value =
    let labels = Hashtbl.create 1 in
    Hashtbl.add labels x8 (c 8 value);
    (Sample_evaluator.make 1).eval_label expression 0 labels
  in
  let check label expression value =
    let simplified = U.binsec_simplify expression in
    require (Bitvector.equal (eval expression value) (eval simplified value))
      (label ^ ": legacy simplifier changed an edge case")
  in
  check "zero quotient at zero" (E.binary E.Udiv (c 8 0) x8) 0;
  check "self quotient at zero" (E.binary E.Udiv x8 x8) 0;
  check "subtract one" (E.binary E.Minus x8 (c 8 1)) 2;
  let a = E.var "a" 8 "a" and b = E.var "b" 8 "b" and d = E.var "d" 8 "d" in
  let reassociated = U.binsec_simplify (plus a (plus b d)) in
  require (E.sizeof reassociated = 8) "legacy reassociation changed the result width"

let test_logging_reset () =
  L.log_linear_size_after := 99;
  L.log_chs_synthesis_attempts := [ (3, true, 1., true) ];
  Hashtbl.replace L.log_chs_time_per_horizon 2 1.;
  L.log_final_is_equiv := U.Yes;
  L.reset ();
  require (!(L.log_linear_size_after) = 0) "linear metrics survived reset";
  require (!(L.log_chs_synthesis_attempts) = []) "attempt metrics survived reset";
  require (Hashtbl.length L.log_chs_time_per_horizon = 0) "horizon metrics survived reset";
  require (!(L.log_final_is_equiv) = U.Disabled) "equivalence metrics survived reset"

let () =
  test_oes_legacy_collision ();
  test_strict_oes_unknown ();
  test_strict_relational_unknown ();
  test_strict_cache_unknown ();
  test_false_backend_candidate ();
  test_raw_candidate_fallback ();
  test_preparation_exceptions ();
  test_restored_size ();
  test_smallest_cut_representative ();
  test_ite_substitution ();
  test_synthesis_partial_timeout ();
  test_oes_partial_timeout ();
  test_balanced_targets ();
  test_sampling_strategies ();
  test_oes_proof_fallback ();
  test_legacy_simplifier_edges ();
  test_logging_reset ();
  print_endline "pipeline_test: 20 solver-independent regressions passed";
  if solver_available then (
    test_context_proof ();
    test_larger_proof_budget_retries ();
    test_chs_horizon_restart ();
    print_endline "pipeline_test: contextual proof and horizon restart passed")
  else if Sys.getenv_opt "GREYSYNTH_REQUIRE_SOLVER" = Some "1" then
    failwith "pipeline_test requires an installed SMT solver"
  else print_endline "pipeline_test: contextual SMT proof skipped (no solver installed)"
