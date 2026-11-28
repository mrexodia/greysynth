module E = Libterm.Sexpr.Expr
module N = Greysynth__Normalization
module C = Greysynth__Config
let require x m = if not x then failwith m
let () =
  C.reset_defaults (); C.g_total_timeout := 0.; C.g_has_timedout := false;
  let x = E.var "r58_x" 64 "r58_x" in
  let source = ref x in
  for _ = 1 to 200 do source := E.binary E.Plus !source !source done;
  let result = N.dag_bottom_up_simplify ~zero_smt:true
      ~deadline:(Unix.gettimeofday () -. 0.001) !source in
  require (Sexpr.Expr.sizeof result = 64) "soft-stop changed result width";
  Printf.printf "round58_test: soft timeout preserved a typed partial result\n"
