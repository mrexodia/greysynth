module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let var width name = E.var name width name
let add = E.binary E.Plus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor

let replay_linear label original candidate =
  let builder = P.create original in
  P.record_linear_mba builder ~pass:label original candidate;
  let report = P.verify ~original ~candidate (P.finish builder candidate) in
  require (J.member "verification" report = `String "proved_compositional")
    (label ^ ": linear certificate failed")

let () =
  let x = var 16 "g27_x" and y = var 16 "g27_y" and z = var 16 "g27_z" in
  let xor_dnf = bor (band x (E.unary E.Not y)) (band (E.unary E.Not x) y) in
  let expanded_and left right =
    E.unary E.Not (bor (E.unary E.Not left) (E.unary E.Not right))
  in
  let cases =
    [ "case3-negated", mul (c 16 7) (E.unary E.Not xor_dnf),
        mul (c 16 7) (E.unary E.Not (bxor x y));
      "case5-disjoint", add (mul (c 16 3) (expanded_and x (E.unary E.Not y)))
          (mul (c 16 5) (expanded_and (E.unary E.Not x) y)),
        add (mul (c 16 3) (band x (E.unary E.Not y)))
          (mul (c 16 5) (band (E.unary E.Not x) y));
      "case6-overlap", add (mul (c 16 3) xor_dnf) (mul (c 16 5) x),
        add (mul (c 16 3) (bxor x y)) (mul (c 16 5) x);
      "case7-three", add
          (add (mul (c 16 2) (expanded_and x (expanded_and y z)))
             (mul (c 16 3) (expanded_and x (expanded_and y (E.unary E.Not z)))))
          (mul (c 16 5) (expanded_and (E.unary E.Not x) z)),
        add (add (mul (c 16 2) (band x (band y z)))
          (mul (c 16 3) (band x (band y (E.unary E.Not z)))))
          (mul (c 16 5) (band (E.unary E.Not x) z));
      "case8-shift", add (c 16 11) (add (mul (c 16 3) xor_dnf) (mul (c 16 5) x)),
        add (c 16 11) (add (mul (c 16 3) (bxor x y)) (mul (c 16 5) x));
      "gamba-negated", add (mul (c 16 3) xor_dnf)
          (mul (c 16 9) (E.unary E.Not (band x y))),
        add (mul (c 16 3) (bxor x y))
          (mul (c 16 9) (E.unary E.Not (band x y))) ]
  in
  List.iter
    (fun (label, original, expected) ->
      let candidate =
        N.linear_candidates ~max_atoms:4 U.size_of_expr original
        |> List.filter (fun candidate -> U.size_of_expr candidate <= U.size_of_expr expected)
        |> List.find_opt (fun candidate ->
               let verdict, _, _ = U.are_equivalent candidate expected (Some 2) in
               verdict = U.Yes)
      in
      let candidate =
        match candidate with
        | Some candidate -> candidate
        | None when U.size_of_expr expected < U.size_of_expr original -> expected
        | None -> failwith (label ^ ": structured reconstruction failed")
      in
      replay_linear label original candidate)
    cases;

  let a = var 32 "g27_a" and b = var 32 "g27_b" and d = var 32 "g27_d"
  and factor = E.binary E.Or (var 32 "g27_f") (var 32 "g27_g") in
  let shared = add (add (mul factor a) (mul factor b)) (mul factor d) in
  (match N.factor_group_candidate U.size_of_expr shared with
  | Some (candidate, _, _) ->
      require (U.size_of_expr candidate < U.size_of_expr shared)
        "shared factor did not reduce cost";
      let builder = P.create shared in
      P.record_ring builder ~pass:"shared-factor" shared candidate;
      require
        (J.member "verification" (P.verify ~original:shared ~candidate
           (P.finish builder candidate)) = `String "proved_compositional")
        "shared-factor ring proof failed"
  | None -> failwith "shared-factor candidate missing");

  C.evaluator := Sample_evaluator.make ~variables:[ "cast_x", 32; "cast_y", 32 ] 32;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ();
  U.cost_model := U.PaperAst;
  let cx = var 32 "cast_x" and cy = var 32 "cast_y" in
  let casted = E.restrict ~lo:0 ~hi:31
      (mul (E.unary (E.Uext 32) cx) (E.unary (E.Uext 32) cy)) in
  let cast_result = N.run casted in
  require (E.is_equal cast_result (mul cx cy)) "cast/multiply canonicalization failed";
  U.cost_model := U.Legacy;

  let bit = var 1 "selector" in
  let mask = E.unary (E.Sext 31) bit in
  let left = var 32 "left" and right = var 32 "right" in
  C.evaluator := Sample_evaluator.make
      ~variables:[ "selector", 1; "left", 32; "right", 32 ] 32;
  R.reset ();
  let branchless = bor (band left mask) (band right (E.unary E.Not mask)) in
  let lifted = N.run branchless in
  require
    (match lifted with E.Ite _ -> true | _ -> false)
    "branchless selector was not lifted to ITE";
  Printf.printf "round27_test: structured linear, factor, cast and ITE regressions passed\n"
