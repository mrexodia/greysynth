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

(* Synthesis backends (interface and contract: synth_backends.mli).

   Adding a backend:
     1. write a module of type [BACKEND] (see [Cvc5_backend] for an external
        tool, [Xyntia_backend] for an in-process library);
     2. add it to [all] at the bottom of this file.
   It is then selected with  "synthesizer": "<name>"  in the config JSON, and
   reads its own settings from that same JSON in [make]. *)

open Sexpr.Expr

(* ── Backend interface ─────────────────────────────────────────── *)

(* An input of the unknown function: a cut leaf, usually a Greek letter. *)
type input = { name : string; size : int }

type sample = {
  args : Bitvector.t array; (* one value per input, in [problem.inputs] order *)
  res : Bitvector.t; (* output value, [problem.output_size] bits *)
}

type problem = {
  inputs : input array;
  output_size : int;
  samples : sample array;
  constants : Bitvector.t list;
      (* constants of the original subtree when "add_constants_to_synthesis"
         is set, else empty; a hint backends are free to ignore *)
  timeout : int; (* seconds *)
  repeat : int; (* attempts, for randomised backends *)
}

type synthesizer = problem -> Sexpr.Expr.t option

module type BACKEND = sig
  val name : string
  (** Value of the "synthesizer" config key that selects this backend. *)

  val make : Yojson.Basic.t -> synthesizer
  (** Called once with the whole config JSON: read backend-specific keys
      here, then return the synthesis function. *)
end

(* ── Helpers for backends ──────────────────────────────────────── *)

(* The variable standing for an input. A result may only use these and
   constants. *)
let input_var (i : input) : Sexpr.Expr.t = var i.name i.size i.name

(* Positional names v0, v1, ... for tools that need plain identifiers. *)
let positional_name (idx : int) : string = Printf.sprintf "v%d" idx

let input_of_positional (p : problem) (s : string) : input option =
  let n = String.length s in
  let digits =
    n >= 2 && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub s 1 (n - 1))
  in
  if not digits || s.[0] <> 'v' then None
  else
    match int_of_string_opt (String.sub s 1 (n - 1)) with
    | Some idx when idx < Array.length p.inputs -> Some p.inputs.(idx)
    | _ -> None

(* Replace the positional variables of a parsed result by the inputs. *)
let of_positional (p : problem) (e : Sexpr.Expr.t) : Sexpr.Expr.t =
  let rec aux e =
    match e with
    | Var v -> (
        match input_of_positional p v.name with
        | Some i when i.size = v.size -> input_var i
        | Some _ -> failwith ("wrong width for variable " ^ v.name)
        | None -> failwith ("unknown variable " ^ v.name))
    | Cst _ -> e
    | Unary { f; x; _ } -> unary f (aux x)
    | Binary { f; x; y; _ } -> binary f (aux x) (aux y)
    | Ite { c; t; e = e'; _ } -> ite (aux c) (aux t) (aux e')
    | Load _ -> failwith "memory load in result"
  in
  aux e

(* A result is usable only if it has the expected width and mentions nothing
   but the problem's inputs. *)
let well_formed (p : problem) (e : Sexpr.Expr.t) : bool =
  let is_input name size =
    Array.exists (fun (i : input) -> i.name = name && i.size = size) p.inputs
  in
  let rec ok = function
    | Var v -> is_input v.name v.size
    | Cst _ -> true
    | Unary { x; _ } -> ok x
    | Binary { x; y; _ } -> ok x && ok y
    | Ite { c; t; e; _ } -> ok c && ok t && ok e
    | Load _ -> false
  in
  sizeof e = p.output_size && ok e

(* Run a shell command and return its standard output. *)
let run_command (cmd : string) : string =
  let ic = Unix.open_process_in cmd in
  Fun.protect
    ~finally:(fun () -> ignore (Unix.close_process_in ic))
    (fun () -> In_channel.input_all ic)

(* Write [contents] to a fresh temporary file and run [f] on its path; the
   file is removed afterwards. *)
let with_temp_file ~prefix ~suffix (contents : string) (f : string -> 'a) : 'a =
  let path = Filename.temp_file prefix suffix in
  Fun.protect
    ~finally:(fun () -> try Sys.remove path with Sys_error _ -> ())
    (fun () ->
      Out_channel.with_open_text path (fun oc -> output_string oc contents);
      f path)

(* Optional string setting of the config JSON. *)
let config_string (json : Yojson.Basic.t) (key : string) ~(default : string) :
    string =
  match Yojson.Basic.Util.member key json with
  | `Null -> default
  | `String s -> s
  | _ -> failwith (Printf.sprintf "config: %S must be a string" key)

let pad_left width c s = String.make (max 0 (width - String.length s)) c ^ s

(* SMT-LIB literal of exactly the bitvector's width. *)
let smtlib_literal (bv : Bitvector.t) : string =
  let size = Bitvector.size_of bv and value = Bitvector.value_of bv in
  if size mod 4 = 0 then "#x" ^ pad_left (size / 4) '0' (Z.format "%x" value)
  else "#b" ^ pad_left size '0' (Z.format "%b" value)

(* ── Xyntia (in-process) ───────────────────────────────────────── *)

module XT = Xyntia_utils.Tree
module XO = Xyntia_utils.Operators

let same_width_binary op x y =
  if sizeof x <> sizeof y then failwith "xyntia: binary operand widths differ";
  binary op x y

let x86_shift op x y =
  let width = sizeof x in
  let mask = if width = 64 then 63 else 31 in
  same_width_binary op x
    (same_width_binary And y (constant (Bitvector.of_int ~size:(sizeof y) mask)))

(* Translate the complete Xyntia tree language, not only the small MBA grammar.
   In particular, Xyntia's ternary division uses [concat high low] as a 2w-bit
   numerator. Dropping [high] would silently change the synthesized function. *)
let rec xyntia_tree_to_expr (tree : unit XT.t) : Sexpr.Expr.t =
  let convert = xyntia_tree_to_expr in
  match tree.node with
  | XT.Var v -> var v.name v.sz v.name
  | XT.Const c -> constant c.value
  | XT.SizeMod (op, child) ->
      let child = convert child in
      let source = sizeof child in
      (match op with
      | XO.Extend width when width >= source -> unary (Uext (width - source)) child
      | XO.Sextend width when width >= source -> unary (Sext (width - source)) child
      | XO.Reduce width when width > 0 && width <= source ->
          unary (Restrict { lo = 0; hi = width - 1 }) child
      | _ -> failwith "xyntia: invalid width modifier in result")
  | XT.Unop (op, child) ->
      let child = convert child in
      (match op with
      | XO.Minus -> unary Minus child
      | XO.Not -> unary Not child
      | XO.Ehad -> same_width_binary Lsr child (constant (Bitvector.of_int ~size:(sizeof child) 1))
      | XO.Arba -> same_width_binary Lsr child (constant (Bitvector.of_int ~size:(sizeof child) 4))
      | XO.Shesh -> same_width_binary Lsr child (constant (Bitvector.of_int ~size:(sizeof child) 16))
      | XO.Smol -> same_width_binary Lsl child (constant (Bitvector.of_int ~size:(sizeof child) 1))
      | XO.Byteswap ->
          let width = sizeof child in
          if width mod 8 <> 0 then failwith "xyntia: byte swap width is not byte-aligned";
          let bytes = width / 8 in
          let rec build index =
            let byte = unary (Restrict { lo = index * 8; hi = (index * 8) + 7 }) child in
            if index = bytes - 1 then byte else binary Concat byte (build (index + 1))
          in
          build 0)
  | XT.Binop (op, left, right) ->
      let left = convert left and right = convert right in
      (match op with
      | XO.Add -> same_width_binary Plus left right
      | XO.Sub -> same_width_binary Minus left right
      | XO.Mul -> same_width_binary Mul left right
      | XO.And -> same_width_binary And left right
      | XO.Or -> same_width_binary Or left right
      | XO.Xor -> same_width_binary Xor left right
      | XO.LShift -> same_width_binary Lsl left right
      | XO.RShiftu -> same_width_binary Lsr left right
      | XO.RShifts -> same_width_binary Asr left right
      | XO.RotateRight -> same_width_binary Ror left right
      | XO.Div_x86 -> same_width_binary Udiv left right
      | XO.SDiv_x86 -> same_width_binary Sdiv left right
      | XO.Mod_x86 -> same_width_binary Umod left right
      | XO.SMod_x86 -> same_width_binary Smod left right
      | XO.LShift_x86 -> x86_shift Lsl left right
      | XO.RShiftu_x86 -> x86_shift Lsr left right
      | XO.RShifts_x86 -> x86_shift Asr left right
      | XO.UMin -> ite (same_width_binary Ult left right) left right
      | XO.UMax -> ite (same_width_binary Ugt left right) left right
      | XO.SMin -> ite (same_width_binary Slt left right) left right
      | XO.SMax -> ite (same_width_binary Sgt left right) left right)
  | XT.Triop (op, first, second, third) ->
      let first = convert first and second = convert second and third = convert third in
      (match op with
      | XO.ITE -> ite first second third
      | XO.Im ->
          let one = constant (Bitvector.ones (sizeof first)) in
          ite (same_width_binary Eq first one) second third
      | (XO.Div | XO.SDiv | XO.Mod | XO.SMod) as op ->
          let width = sizeof third in
          if sizeof first <> width || sizeof second <> width then
            failwith "xyntia: ternary division operand widths differ";
          let numerator = binary Concat first second in
          let divisor =
            unary (if op = XO.SDiv || op = XO.SMod then Sext width else Uext width) third
          in
          let operation =
            match op with
            | XO.Div -> Udiv | XO.SDiv -> Sdiv | XO.Mod -> Umod | XO.SMod -> Smod
            | _ -> assert false
          in
          unary (Restrict { lo = 0; hi = width - 1 })
            (binary operation numerator divisor))

module Xyntia_backend : BACKEND = struct
  let name = "xyntia"

  let make json =
    let grammar = config_string json "xyntia_grammar" ~default:"full" in
    let valid_grammars =
      [ "5"; "mba"; "expr"; "expr_ite"; "mba_shift"; "mba_ite"; "full";
        "sygus"; "expr_x86"; "full_x86" ]
    in
    if not (List.mem grammar valid_grammars) then
      failwith
        (Printf.sprintf "config: invalid xyntia_grammar %S (expected one of: %s)"
           grammar (String.concat ", " valid_grammars));
    (* "xsmir_ops": comma-separated inference rules *)
    let infrules =
      config_string json "xsmir_ops" ~default:""
      |> String.split_on_char ',' |> List.map String.trim
      |> List.filter (( <> ) "")
      |> List.map Xyntia_utils.Distance.str_to_infrule
    in
    fun p ->
      let vars = Array.map (fun i -> XT.var_of i.name i.size) p.inputs in
      let res_var = XT.var_of "res" p.output_size in
      let samples =
        Array.map
          (fun s ->
            {
              Xyntia_utils.Oracle.vars = Array.map2 (fun v x -> (v, x)) vars s.args;
              res = (res_var, s.res);
            })
          p.samples
      in
      let module O =
        (val Xyntia_utils.Oracle.of_samples samples (Array.of_list p.constants)
            : Xyntia_utils.Oracle.ORACLE)
      in
      let (module MU : Xyntia_utils.Mutations.MUTATIONS) =
        Xyntia_utils.Mutations.mutations_of_str
          (module O : Xyntia_utils.Oracle.ORACLE)
          grammar
      in
      let args : Xyntia.synthesis_args =
        {
          heuristic = Xyntia_utils.Heuristic.kind_of_string "ils";
          time = p.timeout;
          dist = Xyntia_utils.Distance.kind_of_str "logarith";
          maxdepth = max_int;
          repeat = p.repeat;
          formula = None;
          smt = None;
          smt_to = None;
          cegis = false;
          infrules;
          noguidance = false;
          rules_combinator = "product";
          check = false;
        }
      in
      let result = Xyntia.run (module O) (module MU) args in
      if result.synthesis.success then
        Some (xyntia_tree_to_expr result.synthesis.simplified)
      else None
end

(* ── Syntia (external Python script, JSON samples) ─────────────── *)

module Syntia_backend : BACKEND = struct
  let name = "syntia"

  let value_json (bv : Bitvector.t) (location : string) =
    let size = Bitvector.size_of bv in
    Printf.sprintf {|{"value": "0x%s", "size": "0x%x", "location": "%s"}|}
      (pad_left ((size + 3) / 4) '0' (Z.format "%x" (Bitvector.value_of bv)))
      size location

  (* Syntia's sample file: the first sample as "initial", the others as
     "sampling" (indexed from 0). *)
  let samples_json (p : problem) : string =
    let sample_json (s : sample) =
      let inputs =
        Array.to_list s.args
        |> List.mapi (fun i x ->
               Printf.sprintf {|"%d": %s|} i (value_json x p.inputs.(i).name))
      in
      Printf.sprintf {|{"inputs": {%s}, "outputs": {"0": %s}}|}
        (String.concat ", " inputs) (value_json s.res "res")
    in
    let sampling =
      Array.to_list p.samples |> List.tl
      |> List.mapi (fun i s -> Printf.sprintf {|"%d": %s|} i (sample_json s))
    in
    (* exprsize is a placeholder, unused for synthesis *)
    Printf.sprintf
      {|{"initial": %s, "sampling": {%s}, "info": {"exprsize": 999, "nvars": %d}}|}
      (sample_json p.samples.(0))
      (String.concat ", " sampling)
      (Array.length p.inputs)

  let make json =
    let cmd = config_string json "synthesizer_cmd" ~default:"python3" in
    let script =
      config_string json "synthesizer_script"
        ~default:
          (Filename.concat (Sys.getcwd ())
             "tools/syntia/scripts/synthesize_sample.py")
    in
    fun p ->
      if Array.length p.samples = 0 then None
      else
        let out =
          with_temp_file ~prefix:"syntia_sample_" ~suffix:".json"
            (samples_json p) (fun path ->
              run_command
                (Printf.sprintf "%s %s --sample %s --timeout %d" cmd
                   (Filename.quote script) (Filename.quote path) p.timeout))
        in
        let answer = Yojson.Basic.from_string out in
        let open Yojson.Basic.Util in
        if answer |> member "success" |> to_string <> "yes" then None
        else
          (* Syntia names the inputs v0, v1, ...: annotate them with their
             width, parse, then map them back to the inputs. *)
          let sized =
            Str.global_substitute
              (Str.regexp "\\bv[0-9]+\\b")
              (fun s ->
                let v = Str.matched_string s in
                match input_of_positional p v with
                | Some i -> Printf.sprintf "%s<%d>" v i.size
                | None -> v)
              (answer |> member "expression" |> to_string)
          in
          Some
            (of_positional p
               (String_to_sexpr.parse ~default_size:p.output_size sized))
end

(* ── cvc5 (external solver, SyGuS) ─────────────────────────────── *)

module Cvc5_backend : BACKEND = struct
  let name = "cvc5"

  let binops =
    [
      ("bvadd", fun x y -> binary Plus x y);
      ("bvsub", fun x y -> binary Minus x y);
      ("bvmul", fun x y -> binary Mul x y);
      ("bvand", fun x y -> binary And x y);
      ("bvor", fun x y -> binary Or x y);
      ("bvxor", fun x y -> binary Xor x y);
      ("bvshl", fun x y -> binary Lsl x y);
      ("bvlshr", fun x y -> binary Lsr x y);
      ("bvashr", fun x y -> binary Asr x y);
      ("bvudiv", fun x y -> binary Udiv x y);
      ("bvsdiv", fun x y -> binary Sdiv x y);
      ("bvurem", fun x y -> binary Umod x y);
      ("bvsrem", fun x y -> binary Smod x y);
    ]

  let unops = [ ("bvnot", fun x -> unary Not x); ("bvneg", fun x -> unary Minus x) ]

  (* Operators offered in the grammar, with their arity. *)
  let grammar_ops =
    [
      ("bvadd", 2); ("bvsub", 2); ("bvmul", 2); ("bvand", 2); ("bvor", 2);
      ("bvxor", 2); ("bvnot", 1); ("bvneg", 1); ("bvshl", 2); ("bvlshr", 2);
      ("bvashr", 2);
    ]

  (* f(v0, ..., vn) with one non-terminal per bit width (operators, inputs of
     that width, 0 and -1, and extend/extract from the other widths), and one
     constraint per sample. *)
  let sygus_problem (p : problem) : string =
    let buf = Buffer.create 2048 in
    let add fmt = Printf.bprintf buf fmt in
    let widths =
      List.sort_uniq Int.compare
        (p.output_size :: List.map (fun (i : input) -> i.size) (Array.to_list p.inputs))
    in
    let nt w = Printf.sprintf "NT%d" w in
    add "(set-logic BV)\n(synth-fun f (";
    Array.iteri (fun idx i -> add "(%s (_ BitVec %d)) " (positional_name idx) i.size) p.inputs;
    add ") (_ BitVec %d)\n" p.output_size;
    add "  ((Start (_ BitVec %d))\n" p.output_size;
    List.iter (fun w -> add "   (%s (_ BitVec %d))\n" (nt w) w) widths;
    add "  ) (\n";
    add "  (Start (_ BitVec %d) (%s))\n" p.output_size (nt p.output_size);
    List.iter
      (fun w ->
        add "  (%s (_ BitVec %d) (\n" (nt w) w;
        Array.iteri
          (fun idx (i : input) -> if i.size = w then add "    %s\n" (positional_name idx))
          p.inputs;
        add "    %s\n" (smtlib_literal (Bitvector.create Z.zero w));
        add "    %s\n" (smtlib_literal (Bitvector.create (Z.pred (Z.shift_left Z.one w)) w));
        List.iter
          (fun (op, arity) ->
            if arity = 1 then add "    (%s %s)\n" op (nt w)
            else add "    (%s %s %s)\n" op (nt w) (nt w))
          grammar_ops;
        List.iter
          (fun other ->
            if other < w then (
              add "    ((_ zero_extend %d) %s)\n" (w - other) (nt other);
              add "    ((_ sign_extend %d) %s)\n" (w - other) (nt other))
            else if other > w then add "    ((_ extract %d 0) %s)\n" (w - 1) (nt other))
          widths;
        add "  ))\n")
      widths;
    add "))\n";
    Array.iter
      (fun s ->
        add "(constraint (= (f";
        Array.iter (fun x -> add " %s" (smtlib_literal x)) s.args;
        add ") %s))\n" (smtlib_literal s.res))
      p.samples;
    add "(check-synth)\n";
    Buffer.contents buf

  let tokenize (s : string) : string list =
    let toks = ref [] and tok = Buffer.create 16 in
    let flush () =
      if Buffer.length tok > 0 then (
        toks := Buffer.contents tok :: !toks;
        Buffer.clear tok)
    in
    String.iter
      (function
        | ('(' | ')') as c ->
            flush ();
            toks := String.make 1 c :: !toks
        | ' ' | '\t' | '\n' | '\r' -> flush ()
        | c -> Buffer.add_char tok c)
      s;
    flush ();
    List.rev !toks

  let literal (tok : string) : Sexpr.Expr.t option =
    let n = String.length tok in
    let digits = String.sub tok 2 (max 0 (n - 2)) in
    if n > 2 && tok.[0] = '#' && tok.[1] = 'x' then
      Some (constant (Bitvector.create (Z.of_string_base 16 digits) (4 * (n - 2))))
    else if n > 2 && tok.[0] = '#' && tok.[1] = 'b' then
      Some (constant (Bitvector.create (Z.of_string_base 2 digits) (n - 2)))
    else None

  (* Body of cvc5's answer  (define-fun f ((v0 ..) ..) (_ BitVec n) <body>),
     or None when there is no answer (unknown, timeout, ...). *)
  let parse_answer (p : problem) (output : string) : Sexpr.Expr.t option =
    let toks = ref (tokenize output) in
    if not (List.mem "define-fun" !toks) then None
    else
      let next () =
        match !toks with
        | t :: rest ->
            toks := rest;
            t
        | [] -> failwith "cvc5: truncated answer"
      in
      let expect t =
        let t' = next () in
        if t' <> t then failwith (Printf.sprintf "cvc5: expected %s, got %s" t t')
      in
      let skip_group () =
        expect "(";
        let depth = ref 1 in
        while !depth > 0 do
          match next () with "(" -> incr depth | ")" -> decr depth | _ -> ()
        done
      in
      let rec term () =
        match next () with
        | "(" -> (
            match next () with
            | "_" ->
                (* (_ bvN w): decimal literal *)
                let lit = next () in
                let w = int_of_string (next ()) in
                expect ")";
                if String.length lit > 2 && String.sub lit 0 2 = "bv" then
                  constant
                    (Bitvector.create
                       (Z.of_string (String.sub lit 2 (String.length lit - 2)))
                       w)
                else failwith ("cvc5: unknown literal " ^ lit)
            | "(" ->
                (* ((_ op i [j]) x): extensions and extracts *)
                expect "_";
                let f =
                  match next () with
                  | "zero_extend" ->
                      let n = int_of_string (next ()) in
                      fun x -> unary (Uext n) x
                  | "sign_extend" ->
                      let n = int_of_string (next ()) in
                      fun x -> unary (Sext n) x
                  | "extract" ->
                      let hi = int_of_string (next ()) in
                      let lo = int_of_string (next ()) in
                      fun x -> unary (Restrict { lo; hi }) x
                  | op -> failwith ("cvc5: unknown indexed operator " ^ op)
                in
                expect ")";
                let x = term () in
                expect ")";
                f x
            | op -> (
                match (List.assoc_opt op unops, List.assoc_opt op binops) with
                | Some f, _ ->
                    let x = term () in
                    expect ")";
                    f x
                | None, Some f ->
                    let x = term () in
                    let y = term () in
                    expect ")";
                    f x y
                | None, None -> failwith ("cvc5: unknown operator " ^ op)))
        | tok -> (
            match literal tok with
            | Some c -> c
            | None -> (
                match input_of_positional p tok with
                | Some i -> input_var i
                | None -> failwith ("cvc5: unknown variable " ^ tok)))
      in
      while next () <> "define-fun" do () done;
      ignore (next ()) (* function name *);
      skip_group () (* parameters *);
      skip_group () (* return sort *);
      Some (term ())

  let make json =
    let cmd = config_string json "synthesizer_cmd" ~default:"cvc5" in
    fun p ->
      let out =
        with_temp_file ~prefix:"cvc5_sygus_" ~suffix:".sy" (sygus_problem p)
          (fun path ->
            run_command
              (Printf.sprintf "%s --lang=sygus2 --tlimit=%d %s" cmd
                 (p.timeout * 1000) (Filename.quote path)))
      in
      parse_answer p out
end

(* ── Registry ──────────────────────────────────────────────────── *)

let all : (module BACKEND) list =
  [ (module Xyntia_backend); (module Syntia_backend); (module Cvc5_backend) ]

let names = List.map (fun (module B : BACKEND) -> B.name) all

(* The synthesizer called [name], configured from the config [json]. *)
let select (name : string) (json : Yojson.Basic.t) : synthesizer =
  match List.find_opt (fun (module B : BACKEND) -> B.name = name) all with
  | Some (module B) -> B.make json
  | None ->
      failwith
        (Printf.sprintf "Unknown synthesizer: %s (expected one of: %s)" name
           (String.concat ", " names))
