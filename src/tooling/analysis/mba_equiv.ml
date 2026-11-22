(**************************************************************************)
(*  This file is part of BINSEC.                                          *)
(*                                                                        *)
(*  Copyright (C) 2026-2027                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  You can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

(* mba_equiv - Check equivalence of two MBA expressions
 *
 * Usage:
 *   mba_equiv -obf -string "<expr>" -gt -string "<expr>"
 *   mba_equiv -obf -cil <file> <func> -gt -cil <file> <func>
 *   mba_equiv -obf -cil <file> <func> -gt -string "<expr>"
 *   mba_equiv -obf -string "<expr>" -gt -cil <file> <func>
 *
 * Equivalence mode:
 *   -smt          Use SMT solver (default)
 *   -sample N     Evaluate both expressions on N random inputs and compare
 *)

type mode = Smt | Sample of int

(* Expression source type *)
type expr_source =
  | StringExpr of string
  | CilExpr of string * string (* file, func *)

(* Load expression from source *)
let load_expr default_size = function
  | StringExpr s -> String_to_sexpr.parse ?default_size s
  | CilExpr (file, func) -> Cil_to_sexpr.load_from_file file func

(* Read expression string from file *)
let read_expr_from_file (file : string) : string =
  try
    let ic = open_in file in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    String.trim content
  with Sys_error msg ->
    Format.eprintf "Error reading file %s: %s\n" file msg;
    exit 1

(* Main *)
let () =
  let obf_source : expr_source option ref = ref None in
  let gt_source : expr_source option ref = ref None in
  let timeout = ref 10 in
  let default_size = ref None in
  let current_target = ref None in
  let mode = ref Smt in

  let usage_msg =
    "Usage:\n\
    \  mba_equiv -obf -string \"<expr>\" -gt -string \"<expr>\"\n\
    \  mba_equiv -obf -string-file <file> -gt -string-file <file>\n\
    \  mba_equiv -obf -cil <file> <func> -gt -cil <file> <func>\n\
    \  mba_equiv -obf -cil <file> <func> -gt -string \"<expr>\"\n\
    \  mba_equiv -obf -cil <file> <func> -gt -string-file <file>\n\n\
     Equivalence mode (default: -smt):\n\
    \  -smt              Use SMT solver\n\
    \  -sample <N>       Evaluate both expressions on N random inputs and compare\n\n\
     Options:"
  in

  let set_string_expr s =
    match !current_target with
    | Some `Obf -> obf_source := Some (StringExpr s)
    | Some `Gt -> gt_source := Some (StringExpr s)
    | None ->
        Format.eprintf "Error: -string must come after -obf or -gt\n";
        exit 1
  in

  let set_string_file_expr file =
    let content = read_expr_from_file file in
    set_string_expr content
  in

  let set_cil_expr file func =
    match !current_target with
    | Some `Obf -> obf_source := Some (CilExpr (file, func))
    | Some `Gt -> gt_source := Some (CilExpr (file, func))
    | None ->
        Format.eprintf "Error: -cil must come after -obf or -gt\n";
        exit 1
  in

  let spec =
    [
      ( "-obf",
        Arg.Unit (fun () -> current_target := Some `Obf),
        " Specify obfuscated expression (followed by -string or -cil)" );
      ( "-gt",
        Arg.Unit (fun () -> current_target := Some `Gt),
        " Specify ground truth expression (followed by -string or -cil)" );
      ( "-string",
        Arg.String set_string_expr,
        "<expr> Parse string expression (DBA syntax)" );
      ( "-cil",
        Arg.Tuple
          [
            Arg.String
              (fun file ->
                let func_ref = ref "" in
                Arg.current := !Arg.current;
                func_ref := file);
            Arg.String
              (fun func ->
                let file = Sys.argv.(!Arg.current - 1) in
                set_cil_expr file func);
          ],
        "<file> <func> Parse C file and extract function's return expression" );
      ( "-smt",
        Arg.Unit (fun () -> mode := Smt),
        " Use SMT solver for equivalence checking (default)" );
      ( "-sample",
        Arg.Int (fun n -> mode := Sample n),
        "<N> Evaluate on N random inputs and compare outputs" );
      ( "-timeout",
        Arg.Int (fun t -> timeout := t),
        "<seconds> SMT solver timeout (default: 10)" );
    ]
  in

  (* Custom argument parsing to handle the stateful -obf/-gt followed by -string/-cil *)
  let argv = Sys.argv in
  let argc = Array.length argv in
  let i = ref 1 in

  while !i < argc do
    let arg = argv.(!i) in
    match arg with
    | "-obf" ->
        current_target := Some `Obf;
        incr i
    | "-gt" ->
        current_target := Some `Gt;
        incr i
    | "-string" ->
        if !i + 1 >= argc then (
          Format.eprintf "Error: -string requires an argument\n";
          exit 1);
        incr i;
        set_string_expr argv.(!i);
        incr i
    | "-string-file" ->
        if !i + 1 >= argc then (
          Format.eprintf "Error: -string-file requires an argument\n";
          exit 1);
        incr i;
        set_string_file_expr argv.(!i);
        incr i
    | "-cil" ->
        if !i + 2 >= argc then (
          Format.eprintf
            "Error: -cil requires two arguments (file and function)\n";
          exit 1);
        incr i;
        let file = argv.(!i) in
        incr i;
        let func = argv.(!i) in
        set_cil_expr file func;
        incr i
    | "-smt" ->
        mode := Smt;
        incr i
    | "-sample" ->
        if !i + 1 >= argc then (
          Format.eprintf "Error: -sample requires an argument\n";
          exit 1);
        incr i;
        mode := Sample (int_of_string argv.(!i));
        incr i
    | "-timeout" ->
        if !i + 1 >= argc then (
          Format.eprintf "Error: -timeout requires an argument\n";
          exit 1);
        incr i;
        timeout := int_of_string argv.(!i);
        incr i
    | "-size" ->
        if !i + 1 >= argc then (
          Format.eprintf "Error: -size requires an argument\n";
          exit 1);
        incr i;
        default_size := Some (int_of_string argv.(!i));
        incr i
    | "-help" | "--help" ->
        Arg.usage spec usage_msg;
        exit 0
    | _ ->
        Format.eprintf "Error: Unknown argument: %s\n" arg;
        Arg.usage spec usage_msg;
        exit 1
  done;

  (* Validate that we have both expressions *)
  if Option.is_none !obf_source then (
    Format.eprintf "Error: Missing -obf expression\n";
    Arg.usage spec usage_msg;
    exit 1);

  if Option.is_none !gt_source then (
    Format.eprintf "Error: Missing -gt expression\n";
    Arg.usage spec usage_msg;
    exit 1);

  (match !mode with
  | Sample n when n <= 0 ->
      Format.eprintf "Error: -sample must be positive\n";
      exit 1
  | _ -> ());
  if !timeout <= 0 then (
    Format.eprintf "Error: -timeout must be positive\n";
    exit 1);

  try
    let sexpr_obf_raw = load_expr !default_size (Option.get !obf_source) in
    let sexpr_gt_raw = load_expr !default_size (Option.get !gt_source) in

    (* Do not silently narrow the input domain to reconcile two different
       variable widths. Callers can express the intended extension explicitly. *)
    let variable_sizes = Hashtbl.create 8 in
    let rec validate_variables = function
      | Sexpr.Expr.Var v -> (
          match Hashtbl.find_opt variable_sizes v.name with
          | Some size when size <> v.size ->
              failwith
                (Printf.sprintf
                   "Variable %s has widths %d and %d; use explicit extension or restriction"
                   v.name size v.size)
          | _ -> Hashtbl.replace variable_sizes v.name v.size)
      | Sexpr.Expr.Unary r -> validate_variables r.x
      | Sexpr.Expr.Binary r ->
          validate_variables r.x;
          validate_variables r.y
      | Sexpr.Expr.Ite r ->
          validate_variables r.c;
          validate_variables r.t;
          validate_variables r.e
      | _ -> ()
    in
    validate_variables sexpr_obf_raw;
    validate_variables sexpr_gt_raw;
    let sexpr_obf, sexpr_gt = (sexpr_obf_raw, sexpr_gt_raw) in

    let size_obf = Greysynth_utils.Utils.size_of_expr sexpr_obf in
    let size_gt = Greysynth_utils.Utils.size_of_expr sexpr_gt in
    let expr_obf_str = Greysynth_utils.Utils.pp sexpr_obf in
    let expr_gt_str = Greysynth_utils.Utils.pp sexpr_gt in
    let costs expression =
      let open Greysynth_utils.Utils in
      `Assoc
        [ ("legacy", `Int (cost_of_expr Legacy expression));
          ("paper_ast", `Int (cost_of_expr PaperAst expression));
          ("instruction", `Int (cost_of_expr Instruction expression));
          ("readability", `Int (cost_of_expr Readability expression)) ]
    in

    let equiv_str, verification, time, counter_example_json, sample_fields =
      match !mode with
      | Smt ->
          let result, t, counter_example =
            Greysynth_utils.Utils.are_equivalent sexpr_obf sexpr_gt (Some !timeout)
              ~show_counter_example:true
          in
          let s =
            match result with
            | Greysynth_utils.Utils.Yes -> "yes"
            | Greysynth_utils.Utils.No -> "no"
            | _ -> "ukn"
          in
          let ce_json =
            match counter_example with
            | Some ce ->
                `Assoc
                  (List.map
                     (fun (var, value) -> (var, `String (Z.to_string value)))
                     ce)
            | None -> `Null
          in
          let verification =
            match result with
            | Greysynth_utils.Utils.Yes -> "proved"
            | Greysynth_utils.Utils.No -> "refuted"
            | Greysynth_utils.Utils.Timeout -> "timeout"
            | _ -> "unknown"
          in
          (s, verification, t, ce_json, [])
      | Sample n ->
          let ev = Sample_evaluator.make n in
          let t0 = Unix.gettimeofday () in
          let matched = ref true in
          let checked = ref 0 in
          let error = ref None in
          let exception Mismatch in
          (try
             for sid = 0 to n - 1 do
               let v_obf = ev.eval sexpr_obf sid in
               let v_gt = ev.eval sexpr_gt sid in
               incr checked;
               if not (Bitvector.equal v_obf v_gt) then (
                 matched := false;
                 raise Mismatch)
             done
           with
          | Mismatch -> ()
          | exn -> error := Some (Printexc.to_string exn));
          let t = Unix.gettimeofday () -. t0 in
          let verdict, verification, sample_match =
            match !error with
            | Some _ -> ("ukn", "evaluation_error", `Null)
            | None when !matched -> ("ukn", "sampled", `Bool true)
            | None -> ("no", "refuted", `Bool false)
          in
          (* Finite agreement is evidence, never a proof of equivalence. *)
          let fields =
            [
              ("sample_match", sample_match);
              ("checked_samples", `Int !checked);
              ("requested_samples", `Int n);
            ]
          in
          let fields =
            match !error with
            | None -> fields
            | Some message -> ("evaluation_error", `String message) :: fields
          in
          (verdict, verification, t, `Null, fields)
    in

    let json =
      `Assoc
        ([
          ("equiv", `String equiv_str);
          ("verification", `String verification);
          ("equiv_time", `Float time);
          ( "obf",
            `Assoc
              [ ("expression", `String expr_obf_str); ("size", `Int size_obf);
                ("costs", costs sexpr_obf) ]
          );
          ( "gt",
            `Assoc
              [ ("expression", `String expr_gt_str); ("size", `Int size_gt);
                ("costs", costs sexpr_gt) ] );
          ("counter_example", counter_example_json);
        ] @ sample_fields)
    in
    Format.printf "%s\n" (Yojson.Basic.pretty_to_string json)
  with
  | Failure msg ->
      Format.eprintf "Error: %s\n" msg;
      exit 1
  | e ->
      Format.eprintf "Unexpected error: %s\n" (Printexc.to_string e);
      exit 1
