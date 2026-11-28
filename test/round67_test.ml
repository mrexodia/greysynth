module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
let require x m = if not x then failwith m
let c w v = E.constant (Bitvector.of_int ~size:w v)
let () =
  let x = E.var "r67_x" 64 "r67_x" and y = E.var "r67_y" 64 "r67_y" in
  let bucket m = E.binary E.Plus
      (E.binary E.And x (c 64 m))
      (E.binary E.Minus y (E.binary E.And x (c 64 m))) in
  let base = E.binary E.Plus (bucket 0x55) (bucket 0x33) in
  let source = E.binary E.Plus base base in
  C.reset_defaults (); C.evaluator := Sample_evaluator.make ~variables:["r67_x",64;"r67_y",64] 32;
  C.g_total_timeout := 0.; R.reset ~original:source (); R.start_recording source;
  match N.mask_bucket_linear_sum_candidate U.size_of_expr source with
  | Some (candidate, rings, linear) ->
      require (R.accepts_compositional ~pass:"r67" ~equalities:[]
        ~ring_equalities:rings ~linear_mba_equalities:linear source candidate)
        "mask bucket proof failed";
      Printf.printf "round67_test: mask bucket partition passed\n"
  | None -> failwith "mask bucket candidate missing"
