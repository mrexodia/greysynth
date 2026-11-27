module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
module C = Greysynth__Config
module R = Greysynth__Rewrite
module N = Greysynth__Normalization
module P = Rewrite_proof
module J = Yojson.Basic.Util

let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let cz width value = E.constant (Bitvector.create value width)
let add = E.binary E.Plus
let sub = E.binary E.Minus
let mul = E.binary E.Mul
let band = E.binary E.And
let bor = E.binary E.Or
let bxor = E.binary E.Xor

let setup original =
  C.reset_defaults ();
  C.evaluator := Sample_evaluator.make
      ~variables:(Sample_evaluator.variables_of_expr original) ~seed:0 64;
  C.g_total_timeout := 0.; C.g_has_timedout := false;
  C.c_reject_non_equiv_simplifications := true; C.c_equiv_timeout := 2;
  R.reset ~original (); R.start_recording original

let replay original candidate =
  let certificate = P.finish (Option.get !(R.journal)) candidate in
  require
    (J.member "verification"
       (P.verify ~timeouts:[ 1.; 5. ] ~original ~candidate certificate)
     = `String "proved_compositional")
    "independent certificate replay failed"

let best_linear original =
  match
    N.linear_candidates_with_rings ~max_atoms:8 U.size_of_expr original
    |> List.sort (fun (left, _, _) (right, _, _) ->
           Int.compare (U.size_of_expr left) (U.size_of_expr right))
  with
  | (candidate, ring_equalities, rewritten_source) :: _ ->
      let accepted =
        R.accepts_compositional ~pass:"round47-boundaries" ~equalities:[]
          ~ring_equalities ~linear_mba_equalities:[ rewritten_source, candidate ]
          original candidate
      in
      let diagnostic =
        if accepted then ""
        else
          let builder = P.create original in
          List.iter (fun (left, right) ->
              P.record_ring builder ~pass:"diag-ring" left right) ring_equalities;
          P.record_linear_mba builder ~pass:"diag-linear" rewritten_source candidate;
          P.verify ~original ~candidate (P.finish builder candidate)
          |> Yojson.Basic.to_string
      in
      require accepted
        ("boundary-consistent linear proof failed (" ^ !(R.last_rejection)
         ^ "): " ^ U.pp candidate ^ " " ^ diagnostic);
      candidate
  | [] -> failwith "boundary-consistent linear candidate missing"

let rec encoded_sum depth left right =
  if depth = 0 then add left right
  else encoded_sum (depth - 1) (bxor left right)
      (mul (c (E.sizeof left) 2) (band left right))

let () =
  let x0 = E.var "r47_x0" 64 "r47_x0"
  and x1 = E.var "r47_x1" 64 "r47_x1"
  and x2 = E.var "r47_x2" 64 "r47_x2" in
  let a = add (band x0 x1) (bxor x0 x2)
  and b = mul (sub x0 x2) (bor x1 x2)
  and m = band (cz 64 (Z.of_string "7038830054286223081")) x2 in
  let carry_zero = sub
      (sub (add a b) (mul (c 64 2) (band a b)))
      (bxor a b) in
  let scalar_zero = sub
      (mul (sub x0 x2) (mul (c 64 (-36)) (bor x1 x2)))
      (mul (c 64 (-36)) b) in
  let block = add (add carry_zero scalar_zero) (sub m m) in
  let source = ref block in
  for _ = 1 to 4 do source := add !source !source done;
  let source = !source in
  require (U.size_of_expr source > 400) "compound boundary test is too small";
  setup source;
  let started = Unix.gettimeofday () in
  let candidate = best_linear source in
  require (Unix.gettimeofday () -. started < 0.1)
    "compound boundary recovery exceeded 0.1 seconds";
  require (U.size_of_expr candidate = 1)
    "compound boundary identity did not collapse to zero";
  replay source candidate;

  let y0 = E.var "r47_y0" 64 "r47_y0"
  and y1 = E.var "r47_y1" 64 "r47_y1"
  and y2 = E.var "r47_y2" 64 "r47_y2"
  and y3 = E.var "r47_y3" 64 "r47_y3" in
  let factor0 = ref (encoded_sum 1 y0 y1)
  and factor1 = ref (encoded_sum 1 y2 y3) in
  for _ = 1 to 6 do
    factor0 := add !factor0 !factor0;
    factor1 := add !factor1 !factor1
  done;
  let factor0 = !factor0 and factor1 = !factor1 in
  let stress = add (mul factor0 factor1)
      (mul (sub factor0 y0) (add factor1 y2)) in
  require (U.size_of_expr stress > 2000) "stress preservation test is too small";
  setup stress;
  let stress_started = Unix.gettimeofday () in
  let stress_result = N.dag_bottom_up_simplify ~zero_smt:true
      ~deadline:(stress_started +. 2.0) stress in
  require (Unix.gettimeofday () -. stress_started < 2.0)
    "stress DAG pass exceeded its soft deadline";
  require (U.size_of_expr stress_result < U.size_of_expr stress)
    "stress DAG pass discarded its partial linear reductions";
  replay stress stress_result;
  Printf.printf "round47_test: compound boundaries and partial DAG work passed\n"
