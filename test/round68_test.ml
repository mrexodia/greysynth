module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r68_x" 64 "r68_x" and y = E.var "r68_y" 64 "r68_y" in
  let a = E.binary E.Plus x y and b = E.binary E.Plus y x in
  let inner = E.binary E.Xor (E.binary E.And a (c 64 0x55))
      (E.binary E.And b (c 64 0x55)) in
  let source = E.binary E.Plus (c 64 7) inner in
  (match N.gf2_masked_xor_candidate_with_bridges U.size_of_expr inner with
  | Some (candidate, rings, _, _) ->
      require (U.size_of_expr candidate = 1 && rings <> []) "nested AC replacement missing";
      require (U.size_of_expr source > U.size_of_expr candidate) "invalid nested test"
  | None -> failwith "nested GF2 candidate missing");
  Printf.printf "round68_test: nested GF2 AC replacement passed\n"
