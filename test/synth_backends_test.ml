module B = Greysynth__Synth_backends
module E = Libterm.Sexpr.Expr
module T = Xyntia_utils.Tree
module TC = T.UnitTreeConstructor
module O = Xyntia_utils.Operators

let require condition message = if not condition then failwith message
let bv width value = Bitvector.of_int ~size:width value
let leaf width value = TC.mk_const_of_bv (bv width value)
let evaluate expression = (Sample_evaluator.make 1).eval expression 0

let check label tree expected =
  let expression = B.xyntia_tree_to_expr tree in
  require (E.sizeof expression = tree.bitsz)
    (Printf.sprintf "%s: output width changed" label);
  let actual = evaluate expression in
  require (Bitvector.equal actual expected)
    (Printf.sprintf "%s: conversion changed semantics (%s != %s)" label
       (Bitvector.to_hexstring actual) (Bitvector.to_hexstring expected))

let () =
  let x = leaf 8 0x91 and y = leaf 8 3 in
  List.iter
    (fun op ->
      check ("unary " ^ O.Unop.to_string op) (TC.mk_unop op x)
        (O.Unop.apply op (bv 8 0x91)))
    [ O.Minus; O.Not; O.Ehad; O.Arba; O.Smol ];
  check "unary shesh" (TC.mk_unop O.Shesh (leaf 32 0x12345678))
    (O.Unop.apply O.Shesh (bv 32 0x12345678));
  check "byte swap" (TC.mk_unop O.Byteswap (leaf 16 0x1234))
    (O.Unop.apply O.Byteswap (bv 16 0x1234));

  List.iter
    (fun op ->
      check ("binary " ^ O.Binop.to_string op) (TC.mk_binop op x y)
        (O.Binop.apply op (bv 8 0x91) (bv 8 3)))
    [ O.Add; O.Sub; O.Mul; O.And; O.Or; O.Xor; O.RShiftu; O.RShifts;
      O.LShift; O.RotateRight; O.Div_x86; O.SDiv_x86; O.Mod_x86;
      O.SMod_x86; O.RShiftu_x86; O.RShifts_x86; O.LShift_x86;
      O.UMin; O.UMax; O.SMin; O.SMax ];

  List.iter
    (fun op ->
      let a = bv 8 1 and b = bv 8 0x23 and c = bv 8 7 in
      check ("ternary " ^ O.Triop.to_string op)
        (TC.mk_triop op (leaf 8 1) (leaf 8 0x23) (leaf 8 7))
        (O.Triop.apply op a b c))
    [ O.Div; O.SDiv; O.Mod; O.SMod; O.ITE; O.Im ];

  List.iter
    (fun (label, op, input) ->
      check label (TC.mk_sizemod op input)
        (O.SizeMod.apply op (match input.node with T.Const c -> c.value | _ -> assert false)))
    [ "zero extension", O.Extend 16, leaf 8 0x81;
      "sign extension", O.Sextend 16, leaf 8 0x81;
      "reduction", O.Reduce 8, leaf 16 0x1281 ];

  let variable = TC.mk_var (T.var_of "x" 8) in
  let extended = B.xyntia_tree_to_expr (TC.mk_sizemod (O.Extend 16) variable) in
  (match extended with
  | E.Unary { f = E.Uext 8; x = E.Var v; _ } ->
      require (v.name = "x" && v.size = 8) "variable identity changed"
  | _ -> failwith "mixed-width variable conversion has the wrong shape");
  let sample : B.sample = { args = [| bv 8 7 |]; res = bv 8 3 } in
  let problem : B.problem =
    {
      inputs = [| { name = "v"; size = 8 } |];
      output_size = 8;
      samples = [| sample |];
      constants = [ bv 8 0x2a ];
      timeout = 1;
      repeat = 1;
    }
  in
  let sygus = B.cvc5_sygus_problem problem in
  let contains needle =
    try
      ignore (Str.search_forward (Str.regexp_string needle) sygus 0);
      true
    with Not_found -> false
  in
  List.iter
    (fun terminal ->
      require (contains terminal) ("cvc5 grammar is missing " ^ terminal))
    [ "#x2a"; "(bvudiv NT8 NT8)"; "(bvsdiv NT8 NT8)";
      "(bvurem NT8 NT8)"; "(bvsrem NT8 NT8)" ];
  Printf.printf "synth_backends: Xyntia conversion and cvc5 grammar passed\n"
