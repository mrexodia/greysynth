module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let () =
  let x = E.var "r61_x" 64 "r61_x" and y = E.var "r61_y" 64 "r61_y" in
  let neg = E.unary E.Not (E.binary E.Minus (E.unary E.Not x) y) in
  require (Option.is_some (N.not_pushdown_candidate U.size_of_expr neg))
    "subtraction NOT pushdown missing";
  let xor = E.unary E.Not (E.binary E.Xor x (E.binary E.And y (E.unary E.Not x))) in
  require (U.size_of_expr (N.demorgan_not (match xor with E.Unary { x; _ } -> x | _ -> assert false))
           <= U.size_of_expr xor)
    "cost-minimizing De Morgan expanded the expression";
  Printf.printf "round61_test: De Morgan pushdown passed\n"
