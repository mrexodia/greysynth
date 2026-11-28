module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r59_x" 64 "r59_x" and y = E.var "r59_y" 64 "r59_y" in
  let b = E.binary E.And (E.unary E.Not y) x in
  let source = E.binary E.Plus (c 64 14)
      (E.binary E.Plus (E.binary E.Mul (c 64 14) b)
         (E.binary E.Mul (c 64 9) y)) in
  let candidates = N.linear_candidates U.size_of_expr source in
  require (List.exists (fun candidate -> U.size_of_expr candidate < U.size_of_expr source) candidates)
    "constant absorption produced no smaller candidate";
  Printf.printf "round59_test: universal constant absorption passed\n"
