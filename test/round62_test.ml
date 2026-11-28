module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r62_x" 64 "r62_x" and y = E.var "r62_y" 64 "r62_y" in
  let source = E.binary E.Plus (c 64 1)
      (E.binary E.Plus (E.binary E.Mul (c 64 3) x) (E.binary E.And x y)) in
  let best = N.linear_candidates U.size_of_expr source
      |> List.sort (fun a b -> Int.compare (U.size_of_expr a) (U.size_of_expr b)) in
  require (match best with h :: _ -> U.size_of_expr h <= 8 | [] -> false)
    "constant absorption did not reach cost 8";
  Printf.printf "round62_test: absorbed signed sum passed\n"
