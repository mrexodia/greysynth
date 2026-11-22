open Libterm.Sexpr

let fail fmt = Printf.ksprintf failwith fmt

let expect_bv name expected actual =
  if not (Bitvector.equal expected actual) then
    fail "%s: expected %s, got %s" name
      (Bitvector.to_string expected) (Bitvector.to_string actual)

let expect_invalid name f =
  match f () with
  | _ -> fail "%s: expected Invalid_argument" name
  | exception Invalid_argument _ -> ()

let c width n = Expr.constant (Bitvector.create n width)
let small width n = c width (Z.of_int n)

let test_extrema () =
  let ev = Sample_evaluator.make 5 in
  List.iter
    (fun width ->
      let x = Expr.var "x" width "x" in
      let high_bit = Z.shift_left Z.one (width - 1) in
      expect_bv "max signed" (Bitvector.create (Z.pred high_bit) width)
        (ev.eval x 3);
      expect_bv "min signed" (Bitvector.create high_bit width) (ev.eval x 4))
    [ 1; 8; 32; 64; 128 ]

let test_shift_semantics () =
  let ev = Sample_evaluator.make 16 in
  List.iter
    (fun width ->
      let one = small width 1 in
      let negative = small width (-2) in
      let large = c width (Z.shift_left Z.one (width - 1)) in
      List.iter
        (fun amount ->
          List.iter
            (fun op ->
              expect_bv "oversized logical shift" (Bitvector.zeros width)
                (ev.eval (Expr.binary op one amount) 0))
            [ Expr.Lsl; Expr.Lsr ];
          expect_bv "oversized signed shift" (Bitvector.fill width)
            (ev.eval (Expr.binary Expr.Asr negative amount) 0);
          expect_bv "oversized positive signed shift" (Bitvector.zeros width)
            (ev.eval (Expr.binary Expr.Asr one amount) 0))
        [ small width width; small width (width + 1); large ];
      let x = Expr.var "cut_x" width "cut_x" in
      let y = Expr.var "cut_y" width "cut_y" in
      let labels = Hashtbl.create 2 in
      Hashtbl.add labels x negative;
      Hashtbl.add labels y large;
      List.iter
        (fun op ->
          expect_bv "eval/eval_label shift agreement"
            (ev.eval (Expr.binary op negative large) 0)
            (ev.eval_label (Expr.binary op x y) 0 labels))
        [ Expr.Lsl; Expr.Lsr; Expr.Asr; Expr.Rol; Expr.Ror ])
    [ 8; 32; 64; 128 ];
  expect_bv "128-bit shift by 64"
    (Bitvector.create (Z.shift_left Z.one 64) 128)
    (ev.eval (Expr.binary Expr.Lsl (small 128 1) (small 128 64)) 0);
  expect_bv "24-bit rotate by 64"
    (Bitvector.create (Z.shift_left Z.one 16) 24)
    (ev.eval (Expr.binary Expr.Rol (small 24 1) (small 24 64)) 0)

let test_total_division () =
  let ev = Sample_evaluator.make 8 in
  List.iter
    (fun width ->
      let zero = small width 0 in
      let positive = small width 5 in
      let negative = small width (-5) in
      expect_bv "unsigned division by zero" (Bitvector.fill width)
        (ev.eval (Expr.binary Expr.Udiv positive zero) 0);
      expect_bv "positive signed division by zero" (Bitvector.fill width)
        (ev.eval (Expr.binary Expr.Sdiv positive zero) 0);
      expect_bv "negative signed division by zero" (Bitvector.ones width)
        (ev.eval (Expr.binary Expr.Sdiv negative zero) 0);
      List.iter
        (fun op ->
          expect_bv "remainder by zero" (Bitvector.of_int ~size:width (-5))
            (ev.eval (Expr.binary op negative zero) 0))
        [ Expr.Umod; Expr.Smod ])
    [ 8; 64; 128 ]

let test_complete_signatures () =
  Random.init 17;
  let ev = Sample_evaluator.make 100 in
  let x = Expr.var "x" 64 "x" and y = Expr.var "y" 64 "y" in
  let large = c 64 (Z.shift_left Z.one 62) in
  let a = Expr.binary Expr.Plus x large in
  let b = Expr.binary Expr.Plus (Expr.binary Expr.Plus y large) (small 64 0) in
  let a_outputs = List.init 100 (ev.eval a) in
  let b_outputs = List.init 100 (ev.eval b) in
  (* OCaml's default hash inspects only ten meaningful values. Large boxed
     bitvectors consume that budget during the identical corner samples, so
     the old integer signatures collide before any differing random value. *)
  assert (Hashtbl.hash a_outputs = Hashtbl.hash b_outputs);
  assert (a_outputs <> b_outputs);
  assert (ev.node_to_outhash a <> ev.node_to_outhash b);
  let signatures = Hashtbl.create 2 in
  Hashtbl.add signatures (ev.node_to_outhash a) "a";
  Hashtbl.add signatures (ev.node_to_outhash b) "b";
  assert (Hashtbl.find signatures (ev.node_to_outhash a) = "a");
  assert (Hashtbl.find signatures (ev.node_to_outhash b) = "b");
  assert (ev.node_to_outhash (small 8 0) <> ev.node_to_outhash (small 64 0))

let test_node_hash_collisions () =
  (* Find a repeatable ordinary 30-bit structural-hash collision. Keeping
     the complete node key makes this harmless to the evaluator. *)
  let seen = Hashtbl.create 65536 in
  let rec find n =
    if n = 200000 then fail "could not find the node-cache regression pair";
    let node = small 64 n in
    let hash = Hashtbl.hash node in
    match Hashtbl.find_opt seen hash with
    | Some other -> (other, node)
    | None ->
        Hashtbl.add seen hash node;
        find (n + 1)
  in
  let a, b = find 0 in
  assert (not (Expr.is_equal a b));
  assert (Hashtbl.hash a = Hashtbl.hash b);
  let ev = Sample_evaluator.make 8 in
  let expected = function Expr.Cst v -> v | _ -> assert false in
  expect_bv "first colliding node" (expected a) (ev.eval a 0);
  expect_bv "second colliding node" (expected b) (ev.eval b 0)

let test_structured_variable_tuples () =
  let x = Expr.var "a" 8 "a" and y = Expr.var "b" 8 "b" in
  let variables = Sample_evaluator.variables_of_expr (Expr.binary Expr.Plus x y) in
  let ev = Sample_evaluator.make ~variables ~seed:7 16 in
  expect_bv "first basis variable" (Bitvector.ones 8) (ev.eval x 5);
  expect_bv "first basis zero" (Bitvector.zeros 8) (ev.eval y 5);
  expect_bv "second basis zero" (Bitvector.zeros 8) (ev.eval x 6);
  expect_bv "second basis variable" (Bitvector.ones 8) (ev.eval y 6);
  let again = Sample_evaluator.make ~variables ~seed:7 16 in
  expect_bv "reproducible stratified tail" (ev.eval x 12) (again.eval x 12);
  let training = Sample_evaluator.make ~variables ~seed:0 40 in
  let holdout = Sample_evaluator.make ~variables ~seed:1 40 in
  let cross_variable_differences = ref 0 and cross_seed_differences = ref 0 in
  for sample = 7 to 39 do
    if not (Bitvector.equal (training.eval x sample) (training.eval y sample)) then
      incr cross_variable_differences;
    if not (Bitvector.equal (training.eval x sample) (holdout.eval x sample)) then
      incr cross_seed_differences
  done;
  if !cross_variable_differences < 24 then
    fail "structured tail remains diagonally collapsed (%d/33 differ)"
      !cross_variable_differences;
  if !cross_seed_differences < 24 then
    fail "holdout tail is not independent (%d/33 differ)" !cross_seed_differences

let test_sample_ids () =
  expect_invalid "zero sample count" (fun () -> Sample_evaluator.make 0);
  expect_invalid "negative sample count" (fun () -> Sample_evaluator.make (-1));
  let ev = Sample_evaluator.make 8 in
  let x = Expr.var "x" 64 "x" in
  expect_invalid "negative sample id" (fun () -> ev.eval x (-1));
  expect_invalid "negative reset id" (fun () -> ev.reset (-1));
  let held_out = ev.eval x 10000 in
  expect_bv "held-out sample cache" held_out (ev.eval x 10000);
  let before = ev.node_to_outhash x in
  ev.reset 0;
  assert (ev.node_to_outhash x = before);
  match ev.is_node_constant (small 64 7) with
  | Some value -> expect_bv "constant evaluates missing samples"
                    (Bitvector.of_int ~size:64 7) value
  | None -> fail "constant not detected"

let () =
  test_extrema ();
  test_shift_semantics ();
  test_total_division ();
  test_complete_signatures ();
  test_node_hash_collisions ();
  test_structured_variable_tuples ();
  test_sample_ids ();
  print_endline "sample_evaluator_test: all checks passed"
