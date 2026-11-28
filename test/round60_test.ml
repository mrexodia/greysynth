module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r60_x" 64 "r60_x" and y = E.var "r60_y" 64 "r60_y" in
  let source = E.binary E.Plus (E.binary E.Mul (c 64 6) y)
      (E.binary E.Mul (c 64 5) (E.binary E.And (E.unary E.Not y) x)) in
  let candidates = N.linear_candidates U.size_of_expr source in
  require (List.exists (fun value -> U.size_of_expr value <= 7) candidates)
    "asymmetric two-variable OR basis was not synthesized";
  Printf.printf "round60_test: asymmetric two-variable basis passed\n"
