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
  Printf.printf "proof_test: typed DAG, endpoint binding and incomplete-derivation regressions passed\n";
  if not available then (
    if Sys.getenv_opt "GREYSYNTH_REQUIRE_SOLVER" = Some "1" then
      failwith "proof_test: solver required but unavailable";
    Printf.printf "proof_test: solver-dependent tests unavailable\n")
  else (
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
    (* A stronger abstraction can be SAT although the original is valid. *)
    let x4 = var "x4" 4 in
    let a = E.binary E.Plus x4 (c 4 1) in
    let p = E.binary E.Mul a a in
    let lhs = E.binary E.Plus p p in
    let rhs = E.binary E.Mul (E.binary E.Mul (c 4 2) a) a in
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
    Printf.printf "proof_test: fresh SMT replay, abstraction, transitivity and congruence regressions passed\n")
