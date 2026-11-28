module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r63_x" 64 "r63_x" and y = E.var "r63_y" 64 "r63_y" in
  let a = E.binary E.Plus x y and b = E.binary E.Plus y x in
  let source = E.binary E.Xor (E.binary E.And a (c 64 0x55))
      (E.binary E.And b (c 64 0x55)) in
  match N.gf2_masked_xor_candidate_with_bridges U.size_of_expr source with
  | Some (candidate, rings, _, _) ->
      require (U.size_of_expr candidate = 1 && rings <> [])
        "AC-unified GF2 candidate did not cancel";
      Printf.printf "round63_test: AC-unified GF2 normalization passed\n"
  | None -> failwith "AC-unified GF2 candidate missing"
