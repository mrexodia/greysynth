module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r64_x" 64 "r64_x" and y = E.var "r64_y" 64 "r64_y" in
  let a = ref (E.binary E.Plus x y) and b = ref (E.binary E.Plus y x) in
  for _ = 1 to 20 do a := E.binary E.Xor !a (c 64 0); b := E.binary E.Xor !b (c 64 0) done;
  let source = E.binary E.Xor (E.binary E.And !a (c 64 0x55))
      (E.binary E.And !b (c 64 0x55)) in
  (match N.gf2_masked_xor_candidate_with_bridges U.size_of_expr source with
  | Some (candidate, _, _, _) -> require (U.size_of_expr candidate = 1) "deep AC GF2 did not cancel"
  | None -> failwith "deep AC GF2 candidate missing");
  Printf.printf "round64_test: deep AC GF2 normalization passed\n"
