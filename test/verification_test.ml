(* Regression tests for the trusted equivalence boundary and checker CLI. *)
module E = Libterm.Sexpr.Expr
module U = Greysynth_utils.Utils

let require condition message = if not condition then failwith message
let constant size value = E.constant (Bitvector.of_int ~size value)
let name = function
  | U.Yes -> "yes"
  | U.No -> "no"
  | U.Timeout -> "timeout"
  | U.Unknown -> "unknown"
  | U.Disabled -> "disabled"

let check label expected lhs rhs =
  let actual, _, _ = U.are_equivalent lhs rhs (Some 5) in
  require (actual = expected)
    (Printf.sprintf "%s: expected %s, got %s" label (name expected) (name actual))

let solver_available =
  Option.is_some Libsolver.bitwuzla_cxx
  || Option.is_some Libsolver.bitwuzla_c
  || Option.is_some Libsolver.z3

let solver_tests () =
  let c = constant 8 in
  let one = constant 1 in
  let bin op x y = E.binary op (c x) (c y) in
  let cases =
    [
      ("add", bin E.Plus 250 10, c 4);
      ("subtract", bin E.Minus 0 1, c 255);
      ("multiply", bin E.Mul 100 3, c 44);
      ("unsigned division", bin E.Udiv 251 3, c 83);
      ("signed division", bin E.Sdiv (-5) 3, c (-1));
      ("unsigned remainder", bin E.Umod 251 3, c 2);
      ("signed remainder", bin E.Smod (-5) 3, c (-2));
      ("and", bin E.And 10 12, c 8);
      ("or", bin E.Or 10 12, c 14);
      ("xor", bin E.Xor 10 12, c 6);
      ("left shift", bin E.Lsl 1 8, c 0);
      ("logical right shift", bin E.Lsr 128 8, c 0);
      ("arithmetic right shift", bin E.Asr 128 8, c 255);
      ("rotate left", bin E.Rol 129 1, c 3);
      ("rotate right", bin E.Ror 129 1, c 192);
      ("concat", bin E.Concat 0x12 0x34, constant 16 0x1234);
      ("equal", bin E.Eq 7 7, one 1);
      ("different", bin E.Diff 7 8, one 1);
      ("unsigned <=", bin E.Ule 128 1, one 0);
      ("unsigned <", bin E.Ult 128 1, one 0);
      ("unsigned >=", bin E.Uge 128 1, one 1);
      ("unsigned >", bin E.Ugt 128 1, one 1);
      ("signed <=", bin E.Sle 128 1, one 1);
      ("signed <", bin E.Slt 128 1, one 1);
      ("signed >=", bin E.Sge 128 1, one 0);
      ("signed >", bin E.Sgt 128 1, one 0);
      ("not", E.unary E.Not (c 0), c 255);
      ("negate", E.unary E.Minus (c 1), c 255);
      ("zero extend", E.unary (E.Uext 8) (c 255), constant 16 255);
      ("sign extend", E.unary (E.Sext 8) (c 255), constant 16 65535);
      ("restrict", E.restrict ~lo:4 ~hi:7 (c 0xab), constant 4 10);
      ("conditional", E.ite (one 1) (c 17) (c 23), c 17);
    ]
  in
  List.iter (fun (label, lhs, rhs) -> check label U.Yes lhs rhs) cases;
  let x = E.var "x" 8 "x" in
  check "division identity" U.Yes (E.binary E.Udiv x (c 1)) x;
  check "conditional with variable condition" U.Yes
    (E.ite (E.binary E.Eq x (c 0)) (c 0) x) x;
  check "signed remainder differs from modulo" U.No
    (bin E.Smod (-5) 3) (c 1);
  let result, _, model =
    U.are_equivalent ~show_counter_example:true x
      (E.binary E.Plus x (c 1)) (Some 5)
  in
  require (result = U.No) "inequivalence must be refuted";
  require (Option.fold ~none:false ~some:(List.mem_assoc "x") model)
    "refutation must include the requested input model";
  let x = E.var "x" 64 "x" and y = E.var "y" 64 "y" in
  let masked = E.binary E.And y (constant 64 63) in
  let diff = E.binary E.Xor (E.binary E.Lsl x masked) (E.binary E.Lsl x y) in
  check "large shifts are not reduced modulo 64" U.No diff (constant 64 0);
  check "solver symbols preserve arbitrary variable identity" U.No
    (E.var "x\000a" 8 "x\000a") (E.var "x\000b" 8 "x\000b");
  Printf.printf "verification: %d solver regressions passed\n" (List.length cases + 6)

let read_all channel =
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_channel buf channel 1 done with End_of_file -> ());
  Buffer.contents buf

let cli_tests executable =
  let invoke args =
    let args = Array.of_list (executable :: args) in
    let channels = Unix.open_process_args_full executable args (Unix.environment ()) in
    let stdout, _, stderr = channels in
    let output = read_all stdout and error = read_all stderr in
    let status = Unix.close_process_full channels in
    (status, output, error)
  in
  let arguments n lhs rhs =
    ["-sample"; string_of_int n; "-obf"; "-string"; lhs; "-gt"; "-string"; rhs]
  in
  List.iter
    (fun n ->
      let status, _, _ = invoke (arguments n "x" "x") in
      require (status <> Unix.WEXITED 0) "empty samples must be rejected")
    [0; -1];
  let field key output = Yojson.Basic.Util.member key (Yojson.Basic.from_string output) in
  let status, output, error = invoke (arguments 8 "x" "x") in
  require (status = Unix.WEXITED 0) ("sample checker failed: " ^ error);
  require (field "equiv" output = `String "ukn") "sample agreement is not a proof";
  require (field "verification" output = `String "sampled") "sample status missing";
  require (field "sample_match" output = `Bool true) "sample agreement missing";
  let _, output, _ = invoke (arguments 8 "0" "1") in
  require (field "equiv" output = `String "no") "sample mismatch must refute";
  let _, output, _ = invoke (arguments 8 "x / 0" "123") in
  require (field "equiv" output <> `String "yes") "failed evaluation cannot prove equivalence";
  let status, _, _ = invoke (arguments 8 "x<8>" "x<32>") in
  require (status <> Unix.WEXITED 0) "different input widths must not silently coerce";
  Printf.printf "verification: 6 checker CLI regressions passed\n"

let () =
  check "output widths differ" U.No (constant 8 1) (constant 16 1);
  if solver_available then solver_tests ()
  else (
    check "no solver is unknown" U.Unknown (constant 8 1) (constant 8 1);
    Printf.printf "verification: no solver installed; checked fail-closed result\n");
  if Array.length Sys.argv > 1 then cli_tests Sys.argv.(1)
