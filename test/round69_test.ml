module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let () =
  let x0 = E.var "r69_x0" 64 "r69_x0" and x1 = E.var "r69_x1" 64 "r69_x1"
  and x2 = E.var "r69_x2" 64 "r69_x2" and x3 = E.var "r69_x3" 64 "r69_x3"
  and x4 = E.var "r69_x4" 64 "r69_x4" and x5 = E.var "r69_x5" 64 "r69_x5" in
  let source = E.binary E.Minus
      (E.binary E.Plus (E.binary E.Mul x1 x3) x4)
      (E.binary E.Plus (E.binary E.Mul x0 x5) (E.binary E.Mul x1 x2)) in
  match N.common_factor_pullout_candidate U.size_of_expr source with
  | Some candidate -> require (U.size_of_expr candidate < U.size_of_expr source) "opposite-sign factor pullout failed"
  | None -> failwith "opposite-sign factor candidate missing"
