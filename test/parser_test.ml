(* The textual boundary must preserve widths, names, and all pure operators. *)
module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils
let require condition message = if not condition then failwith message
let c width value = E.constant (Bitvector.of_int ~size:width value)
let roundtrip expression =
  let printed = U.pp expression in
  let parsed = String_to_sexpr.parse printed in
  require (E.is_equal expression parsed) ("round-trip changed expression: " ^ printed)

let () =
  let x = E.var "x!1" 8 "x!1" and y = E.var "y" 8 "y" in
  let binary_operations : Term.binary E.op list =
    [ E.Plus; E.Minus; E.Mul; E.Udiv; E.Sdiv; E.Umod; E.Smod;
      E.And; E.Or; E.Xor; E.Lsl; E.Lsr; E.Asr; E.Rol; E.Ror;
      E.Concat; E.Eq; E.Diff; E.Ule; E.Ult; E.Uge; E.Ugt;
      E.Sle; E.Slt; E.Sge; E.Sgt ]
  in
  List.iter (fun op -> roundtrip (E.binary op x y)) binary_operations;
  List.iter roundtrip
    [ x; c 1 1; c 8 255; c 16 65535;
      E.constant (Bitvector.create (Z.shift_left Z.one 100) 128);
      E.unary E.Not x; E.unary E.Minus x;
      E.unary (E.Uext 8) x; E.unary (E.Sext 8) x;
      E.restrict ~lo:2 ~hi:5 x;
      E.binary E.Concat (c 8 0x12) (c 16 0x3456);
      E.binary E.Plus (E.unary (E.Uext 8) x) (c 16 1);
      E.ite (E.binary E.Eq x y) (c 8 3) y ];
  List.iter
    (fun name -> roundtrip (E.var name 32 name))
    ["x"; "x!1"; "x!2"; "rol"; "with space"; "quote\"slash\\";
     ""; "λ"; "x\000z"];
  let evaluator = Sample_evaluator.make 8 in
  let expect source width value =
    let expression = String_to_sexpr.parse source in
    require (E.sizeof expression = width) ("incorrect width: " ^ source);
    let actual = evaluator.eval expression 0 in
    require (Bitvector.equal actual (Bitvector.of_int ~size:width value))
      ("incorrect semantics: " ^ source)
  in
  List.iter (fun (source, width, value) -> expect source width value)
    [ ("!0<8>", 1, 1); ("!7<8>", 1, 0); ("~0<8>", 8, 255);
      ("2 | 3 == 3", 64, 3); ("2 & 1 == 0", 64, 0);
      ("1 + 2 << 3", 64, 24); ("1 << 2 + 1", 64, 8);
      ("1<8> ++ 2<16>", 24, 65538);
      ("255<8> + 1<16>", 16, 256);
      ("1<8> + 2", 8, 3);
      ("uext(8) 1<8>", 16, 1); ("uext(8) 1", 72, 1);
      ("sext(8) 255<8>", 16, 65535);
      ("restrict(4, 7) 171<8>", 4, 10);
      ("-5<8> %s 3<8>", 8, 254);
      ("255<8> <s 1<8>", 1, 1); ("255<8> <u 1<8>", 1, 0);
      ("1<8> != 2<8>", 1, 1);
      ("0 ? 3<8> : 1 ? 5<8> : 7<8>", 8, 5);
      ("3<8> ** 0", 8, 1) ];
  require
    (E.is_equal (String_to_sexpr.parse "x<<y")
       (String_to_sexpr.parse "x << y"))
    "shift lexing must not depend on whitespace";
  let explicit = String_to_sexpr.parse "1<8> + 2<16>" in
  (match explicit with
  | E.Binary { x = E.Unary { f = E.Uext 8; x = E.Cst value; _ }; _ } ->
      require (Bitvector.size_of value = 8) "explicit literal width was lost"
  | _ -> failwith "explicit literal must be extended, not resized");
  List.iter
    (fun source ->
      let rejected =
        try ignore (String_to_sexpr.parse source); false with Failure _ -> true
      in
      require rejected ("invalid input accepted: " ^ source))
    ["x<0>"; "uext(8 x"; "restrict(1 2) x"; "restrict(7,8) x<8>";
     "uext(18446744073709551615) x";
     "restrict(0,18446744073709551615) x";
     "x ** 18446744073709551615"; "x ** 4097";
     "x && y"; "x || y"];
  Printf.printf "parser: operator/name round-trips and semantic regressions passed\n"
