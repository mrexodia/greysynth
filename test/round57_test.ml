module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r57_x" 64 "r57_x" in
  let dead = E.binary E.Mul (c 64 128)
      (E.binary E.Mul x (E.binary E.Plus x (c 64 3))) in
  let source = E.unary (E.Uext 57) (E.restrict ~lo:0 ~hi:6 dead) in
  match N.lowk_restrict_homomorphism_candidate U.size_of_expr source with
  | Some (candidate, _, _, _) ->
      require (U.size_of_expr candidate = 1) "dead low-k branch was not annihilated";
      Printf.printf "round57_test: dead low-k branch annihilation passed\n"
  | None -> failwith "dead low-k candidate missing"
