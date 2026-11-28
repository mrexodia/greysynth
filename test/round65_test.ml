module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let () =
  let a = E.var "r65_a" 64 "r65_a" and b = E.var "r65_b" 64 "r65_b" in
  let source = E.unary E.Not (E.binary E.Plus (E.unary E.Not a) b) in
  (match N.not_pushdown_candidate U.size_of_expr source with
  | Some candidate -> require (E.is_equal candidate (E.binary E.Minus a b)) "NOT-plus rewrite wrong"
  | None -> failwith "NOT-plus candidate missing");
  Printf.printf "round65_test: NOT arithmetic pushdown passed\n"
