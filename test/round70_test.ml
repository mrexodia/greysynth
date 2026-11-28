module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r70_x" 96 "r70_x" in
  let source = E.binary E.Plus (E.unary (E.Sext 32) (c 64 0x15))
      (E.restrict ~lo:0 ~hi:95 x) in
  C.reset_defaults (); C.evaluator := Sample_evaluator.make ~variables:["r70_x",96] 16;
  C.g_total_timeout := 0.; R.reset ~original:source (); R.start_recording source;
  let result = N.dag_constant_cast_simplify source in
  require
    (match result with E.Binary { f = E.Plus; x = E.Cst _; y = E.Var _; _ } -> true | _ -> false)
    ("constant/full restrict casts not folded: " ^ U.pp result);
  Printf.printf "round70_test: cast DAG folding passed\n"
