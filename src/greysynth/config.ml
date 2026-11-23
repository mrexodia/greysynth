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

(* Configuration knobs (set from JSON, see [load_config_from_json] in the
   driver) and the long-lived runtime state shared across the pipeline:
   the evaluator, the CHS cache and the global timeout. *)

open Logging

type sampling_t = RealValues | LabelValues | WrongNaive

let string_of_sampling = function
  | RealValues -> "real"
  | LabelValues -> "label"
  | WrongNaive -> "wrong_naive"

(* ── Config knobs ──────────────────────────────────────────────── *)
let c_normalization = ref true
let c_ac_normalization = ref false
let c_normalization_portfolio = ref false
let c_preprocessing_portfolio = ref false
let c_egraph_extraction = ref false
let c_egraph_max_enodes = ref 2048
let c_egraph_max_iters = ref 4
let c_normalization_max_atoms = ref 6
let c_mba_oracle = ref "none"
let c_mba_oracle_command = ref ""
let c_mba_oracle_timeout = ref 2
let c_mba_oracle_calls = ref 4
let c_oes = ref false
let c_oes_extended = ref false
let c_oes_fixedpoint = ref false
let c_oes_candidate_limit = ref 1
let c_local_extend = ref false
let c_local_extend_depth = ref 6
let c_fast_simplify = ref false
let c_global_synthesis = ref false
let c_chs = ref false
let c_chs_max_inputs = ref 0
let c_chs_max_horizon = ref 0
let c_synthesis_timeout = ref 1
let c_synthesis_repeat = ref 1
let c_cegis_retries = ref 1
let c_learn_synthesis_rules = ref true
let c_learned_rules_file = ref ""
let c_chs_adaptive_schedule = ref false
let c_chs_probe_timeout = ref 1
let c_synthesizer_portfolio = ref ""
let c_balanced_tree = ref false
let c_sampling_strategy = ref RealValues
let c_branch_covering_samples = ref true
let c_equiv_timeout = ref 1
let c_check_equiv = ref false
let c_nb_samples = ref 100
let c_current_mode_is_global = ref false
let c_reject_non_equiv_simplifications = ref true
let c_local_cache = ref false
let c_add_constants_to_synthesis = ref false
let c_synthesis_constant_limit = ref 12

(* "synthesizer" config key and the backend it selects (see Synth_backends) *)
let c_synthesizer_name = ref "xyntia"
let c_xyntia_grammar = ref "auto"
let c_synthesizer : Synth_backends.synthesizer ref = ref (fun _ -> None)
let c_synthesizer_portfolio_backends :
    (string * Synth_backends.synthesizer) list ref = ref []

(* ── Runtime state ─────────────────────────────────────────────── *)
let g_total_timeout = ref 0.
let g_start_time = ref 0.
let g_has_timedout = ref false

let chs_cache_per_horizon : (Sample_evaluator.outhash, Sexpr.Expr.t) Hashtbl.t =
  Hashtbl.create 1000

let evaluator = ref (Sample_evaluator.make 1)

exception Timeout_exception

type config_spec = {
  json_key : string;
  report_key : string option;
  required : bool;
  default : Yojson.Basic.t;
  set_json : Yojson.Basic.t -> unit;
  get_json : unit -> Yojson.Basic.t;
  validate : unit -> unit;
}

let bool_spec ?report ?(required = false) key default target =
  { json_key = key; report_key = report; required; default = `Bool default;
    set_json = (fun json -> target := Yojson.Basic.Util.to_bool json);
    get_json = (fun () -> `Bool !target); validate = (fun () -> ()) }

let int_spec ?report ?(required = false) ?(validate = fun _ -> true)
    ?(message = "must be valid") key default target =
  { json_key = key; report_key = report; required; default = `Int default;
    set_json = (fun json -> target := Yojson.Basic.Util.to_int json);
    get_json = (fun () -> `Int !target);
    validate = (fun () -> if not (validate !target) then failwith ("config: " ^ key ^ " " ^ message)) }

let string_spec ?report ?(required = false) ?(validate = fun _ -> true)
    ?(message = "must be valid") key default target =
  { json_key = key; report_key = report; required; default = `String default;
    set_json = (fun json -> target := Yojson.Basic.Util.to_string json);
    get_json = (fun () -> `String !target);
    validate = (fun () -> if not (validate !target) then failwith ("config: " ^ key ^ " " ^ message)) }

let config_specs =
  [
    bool_spec ~report:"is_normalization_enabled" "normalization" true c_normalization;
    bool_spec ~report:"ac_normalization" "ac_normalization" false c_ac_normalization;
    bool_spec ~report:"normalization_portfolio" "normalization_portfolio" false c_normalization_portfolio;
    bool_spec ~report:"preprocessing_portfolio" "preprocessing_portfolio" false c_preprocessing_portfolio;
    bool_spec ~report:"egraph_extraction" "egraph_extraction" false c_egraph_extraction;
    int_spec ~report:"egraph_max_enodes" ~validate:((<) 0) ~message:"must be positive"
      "egraph_max_enodes" 2048 c_egraph_max_enodes;
    int_spec ~report:"egraph_max_iters" ~validate:((<) 0) ~message:"must be positive"
      "egraph_max_iters" 4 c_egraph_max_iters;
    int_spec ~report:"normalization_max_atoms" ~validate:(fun value -> value >= 1 && value <= 10)
      ~message:"must be between 1 and 10" "normalization_max_atoms" 6 c_normalization_max_atoms;
    string_spec ~report:"mba_oracle" ~validate:(fun value -> List.mem value ["none"; "rumba"; "cobra"])
      ~message:"must be none, rumba, or cobra" "mba_oracle" "none" c_mba_oracle;
    string_spec "mba_oracle_command" "" c_mba_oracle_command;
    int_spec ~report:"mba_oracle_timeout" ~validate:((<) 0) ~message:"must be positive"
      "mba_oracle_timeout" 2 c_mba_oracle_timeout;
    int_spec ~report:"mba_oracle_calls" ~validate:((<=) 0) ~message:"must be nonnegative"
      "mba_oracle_calls" 4 c_mba_oracle_calls;
    bool_spec ~report:"is_linear_enabled" "oes" true c_oes;
    bool_spec "oes_extended" false c_oes_extended;
    bool_spec "oes_fixedpoint" false c_oes_fixedpoint;
    int_spec ~report:"oes_candidate_limit" ~validate:((<) 0) ~message:"must be positive"
      "oes_candidate_limit" 1 c_oes_candidate_limit;
    bool_spec "local_extend" false c_local_extend;
    int_spec ~validate:((<) 0) ~message:"must be positive" "local_extend_depth" 4 c_local_extend_depth;
    bool_spec ~report:"is_fast_simplify_enabled" "fast_simplify" false c_fast_simplify;
    bool_spec ~report:"is_global_enabled" "global_synthesis" false c_global_synthesis;
    bool_spec ~report:"is_chs_enabled" "chs" true c_chs;
    int_spec ~report:"chs_max_inputs" ~validate:((<=) 0) ~message:"must be nonnegative"
      "chs_max_inputs" 0 c_chs_max_inputs;
    int_spec ~report:"chs_max_horizon" ~validate:((<=) 0) ~message:"must be nonnegative"
      "chs_max_horizon" 0 c_chs_max_horizon;
    int_spec ~validate:((<) 0) ~message:"must be positive" "synthesis_timeout" 2 c_synthesis_timeout;
    int_spec ~validate:((<) 0) ~message:"must be positive" "synthesis_repeat" 1 c_synthesis_repeat;
    int_spec ~report:"cegis_retries" ~validate:((<=) 0) ~message:"must be nonnegative"
      "cegis_retries" 1 c_cegis_retries;
    bool_spec ~report:"learn_synthesis_rules" "learn_synthesis_rules" true c_learn_synthesis_rules;
    string_spec ~report:"learned_rules_file" "learned_rules_file" "" c_learned_rules_file;
    bool_spec ~report:"chs_adaptive_schedule" "chs_adaptive_schedule" false
      c_chs_adaptive_schedule;
    int_spec ~report:"chs_probe_timeout" ~validate:((<) 0) ~message:"must be positive"
      "chs_probe_timeout" 1 c_chs_probe_timeout;
    string_spec ~report:"synthesizer_portfolio" "synthesizer_portfolio" ""
      c_synthesizer_portfolio;
    bool_spec ~report:"balanced_tree" "balanced_tree" true c_balanced_tree;
    bool_spec "reject_non_equiv_simplifications" true c_reject_non_equiv_simplifications;
    int_spec ~validate:((<) 0) ~message:"must be positive" "equiv_timeout" 1 c_equiv_timeout;
    bool_spec ~report:"check_equiv" "check_equiv" false c_check_equiv;
    int_spec ~validate:((<) 0) ~message:"must be positive" "nb_samples" 100 c_nb_samples;
    bool_spec ~report:"local_cache" "local_cache" true c_local_cache;
    bool_spec "add_constants_to_synthesis" true c_add_constants_to_synthesis;
    int_spec ~report:"synthesis_constant_limit" ~validate:((<=) 0)
      ~message:"must be nonnegative" "synthesis_constant_limit" 12 c_synthesis_constant_limit;
    string_spec "synthesizer" "xyntia" c_synthesizer_name;
    string_spec "xyntia_grammar" "auto" c_xyntia_grammar;
    bool_spec ~report:"branch_covering_samples" "branch_covering_samples" true
      c_branch_covering_samples;
    { json_key = "cost_model"; report_key = Some "cost_model"; required = false;
      default = `String "legacy";
      set_json = (fun json ->
        let value = Yojson.Basic.Util.to_string json in
        try Greysynth_utils.Utils.cost_model := Greysynth_utils.Utils.cost_model_of_string value
        with Invalid_argument message -> failwith ("config: " ^ message));
      get_json = (fun () -> `String (Greysynth_utils.Utils.string_of_cost_model
                                       !Greysynth_utils.Utils.cost_model));
      validate = (fun () -> ()) };
    { json_key = "sampling_strategy"; report_key = None; required = false;
      default = `String "real";
      set_json = (fun json ->
        match Yojson.Basic.Util.to_string json with
        | "real" -> c_sampling_strategy := RealValues
        | "label" -> c_sampling_strategy := LabelValues
        | "wrong_naive" -> c_sampling_strategy := WrongNaive
        | value -> failwith ("config: unknown sampling_strategy " ^ value));
      get_json = (fun () -> `String (string_of_sampling !c_sampling_strategy));
      validate = (fun () -> ()) };
    { json_key = "total_timeout"; report_key = None; required = false;
      default = `Int 600;
      set_json = (fun json -> g_total_timeout := float_of_int (Yojson.Basic.Util.to_int json));
      get_json = (fun () -> `Float !g_total_timeout);
      validate = (fun () -> if !g_total_timeout < 0. then failwith "config: total_timeout must be nonnegative") };
  ]

let reset_defaults () =
  List.iter (fun spec -> spec.set_json spec.default) config_specs

let report_fields () =
  List.filter_map
    (fun spec -> Option.map (fun key -> key, spec.get_json ()) spec.report_key)
    config_specs

let apply_config_specs json =
  if Yojson.Basic.Util.member "local_synthesis" json <> `Null then
    failwith "config: \"local_synthesis\" was renamed to \"chs\"";
  List.iter
    (fun spec ->
      let value = Yojson.Basic.Util.member spec.json_key json in
      if value = `Null then (
        if spec.required then failwith ("config: missing " ^ spec.json_key)
        else spec.set_json spec.default)
      else spec.set_json value;
      spec.validate ())
    config_specs;
  if !c_mba_oracle <> "none" && !c_mba_oracle_command = "" then
    failwith "config: mba_oracle_command is required when an MBA oracle is enabled";
  if !c_synthesizer_portfolio <> "" then
    String.split_on_char ',' !c_synthesizer_portfolio
    |> List.map String.trim
    |> List.iter (fun name ->
           if name = "" || not (List.mem name Synth_backends.names) then
             failwith
               (Printf.sprintf "config: unknown synthesizer_portfolio backend %S" name))

let check_timeout () =
  if !g_total_timeout > 0. then
    let elapsed = Unix.gettimeofday () -. !g_start_time in
    if elapsed > !g_total_timeout then (
      _log_warn "timeout" "%.1fs elapsed (limit: %.1fs)" elapsed
        !g_total_timeout;
      raise Timeout_exception)

let load_config_from_json json_file : unit =
  try
    reset_defaults ();
    let json = Yojson.Basic.from_file json_file in
    apply_config_specs json;
    c_synthesizer := Synth_backends.select !c_synthesizer_name json;
    c_synthesizer_portfolio_backends :=
      (if !c_synthesizer_portfolio = "" then []
       else
         String.split_on_char ',' !c_synthesizer_portfolio
         |> List.map String.trim
         |> List.map (fun name -> name, Synth_backends.select name json));

    (* Print configuration summary *)
    let pipeline =
      String.concat " -> "
        (List.filter_map Fun.id
           [
             (if !c_normalization then Some "Normalize" else None);
             (if !c_oes then
                Some
                  ((if !c_oes_extended then "OES+" else "OES")
                  ^ if !c_local_extend then "L" else "")
              else None);
             (if !c_fast_simplify then Some "FastSimplify" else None);
             (if !c_global_synthesis then Some "Global" else None);
             (if !c_chs then Some "CHS" else None);
           ])
    in
    _log_header "GreySynth";
    Format.eprintf "  config     %s\n" json_file;
    Format.eprintf "  pipeline   %s\n"
      (if pipeline = "" then "(none)" else pipeline);
    Format.eprintf "  synth      %s  (timeout=%ds, repeat=%d, samples=%d)\n"
      !c_synthesizer_name !c_synthesis_timeout !c_synthesis_repeat !c_nb_samples;
    Format.eprintf "  sampling   %s\n" (string_of_sampling !c_sampling_strategy);
    Format.eprintf "  cost       %s\n"
      (Greysynth_utils.Utils.string_of_cost_model !Greysynth_utils.Utils.cost_model);
    if !c_check_equiv then
      Format.eprintf "  equiv      on  (timeout=%ds)\n" !c_equiv_timeout;
    Format.eprintf "%!";

    ()
  with
  | Sys_error msg -> failwith ("config: " ^ msg)
  | Yojson.Json_error msg -> failwith ("config JSON: " ^ msg)
  | Yojson.Basic.Util.Type_error (msg, _) -> failwith ("config type: " ^ msg)
