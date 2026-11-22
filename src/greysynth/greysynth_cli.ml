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

(* greysynth - CLI for MBA expression simplification
 *
 * Usage:
 *   greysynth -obf -cil <file> <func> [-gt -cil <file> <func>] <config.json>
 *   greysynth -obf -string "<expr>" [-gt -string "<expr>"] <config.json>
 *   greysynth -obf -cil <file> <func> -gt -string "<expr>" <config.json>
 *
 * Expression options are shared with other simplifiers, see Cli_input.
 *)

let usage_msg =
  "Usage:\n\
  \  greysynth -obf -cil <file> <func> [-gt -cil <file> <func>] <config.json>\n\
  \  greysynth -obf -string \"<expr>\" [-gt -string \"<expr>\"] <config.json>\n\n\
   Optional second positional argument: proof-output.json\n\nOptions:"

let () =
  let input = Cli_input.parse_command_line ~usage:usage_msg in

  (* The only positional argument should be the config file *)
  let config_file, proof_output =
    match input.positional with
    | [ config ] -> config, None
    | [ config; proof ] -> config, Some proof
    | [] -> Cli_input.fail_usage usage_msg "Error: Missing config file argument\n"
    | _ -> Cli_input.fail_usage usage_msg "Error: Too many positional arguments\n"
  in

  if not (Sys.file_exists config_file) then (
    Format.eprintf "Error: Config file %s does not exist\n" config_file;
    exit 1);

  
    (* This is where we actually call GreySynth *)
  try Greysynth.run ?proof_output input.obf config_file input.gt
  with Failure msg ->
    Format.eprintf "Error: %s\n" msg;
    exit 1
