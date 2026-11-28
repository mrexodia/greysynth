module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let () =
  let a = E.var "r66_a" 64 "r66_a" and b = E.var "r66_b" 64 "r66_b"
  and c = E.var "r66_c" 64 "r66_c" in
  let source = E.binary E.Minus (E.unary E.Not a)
      (E.binary E.Plus (E.unary E.Not b) c) in
  (match N.not_pushdown_candidate U.size_of_expr source with
  | Some candidate ->
      let expected = E.binary E.Minus (E.binary E.Minus b a) c in
      require (E.is_equal candidate expected) "top-level complement subtraction rewrite wrong"
  | None -> failwith "top-level complement subtraction candidate missing");
  Printf.printf "round66_test: top-level complement subtraction passed\n"
