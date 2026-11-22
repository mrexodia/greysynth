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
let c_oes = ref false
let c_oes_extended = ref false
let c_oes_fixedpoint = ref false
let c_oes_candidate_limit = ref 1
let c_local_extend = ref false
let c_local_extend_depth = ref 6
let c_fast_simplify = ref false
let c_global_synthesis = ref false
let c_chs = ref false
let c_synthesis_timeout = ref 1
let c_synthesis_repeat = ref 1
let c_cegis_retries = ref 1
let c_learn_synthesis_rules = ref true
let c_balanced_tree = ref false
let c_sampling_strategy = ref RealValues
let c_equiv_timeout = ref 1
let c_check_equiv = ref false
let c_nb_samples = ref 100
let c_current_mode_is_global = ref false
let c_reject_non_equiv_simplifications = ref true
let c_local_cache = ref false
let c_add_constants_to_synthesis = ref false

(* "synthesizer" config key and the backend it selects (see Synth_backends) *)
let c_synthesizer_name = ref "xyntia"
let c_synthesizer : Synth_backends.synthesizer ref = ref (fun _ -> None)

(* ── Runtime state ─────────────────────────────────────────────── *)
let g_total_timeout = ref 0.
let g_start_time = ref 0.
let g_has_timedout = ref false

let chs_cache_per_horizon : (Sample_evaluator.outhash, Sexpr.Expr.t) Hashtbl.t =
  Hashtbl.create 1000

let evaluator = ref (Sample_evaluator.make 1)

exception Timeout_exception

let check_timeout () =
  if !g_total_timeout > 0. then
    let elapsed = Unix.gettimeofday () -. !g_start_time in
    if elapsed > !g_total_timeout then (
      _log_warn "timeout" "%.1fs elapsed (limit: %.1fs)" elapsed
        !g_total_timeout;
      raise Timeout_exception)

let load_config_from_json json_file : unit =
  try
    let json = Yojson.Basic.from_file json_file in
    let open Yojson.Basic.Util in
    (c_normalization :=
       match json |> member "normalization" with
       | `Null -> true
       | v -> to_bool v);
    (c_ac_normalization :=
       match json |> member "ac_normalization" with
       | `Null -> false
       | v -> to_bool v);
    (c_normalization_portfolio :=
       match json |> member "normalization_portfolio" with
       | `Null -> false
       | v -> to_bool v);
    c_oes := json |> member "oes" |> to_bool;
    (c_oes_extended :=
       match json |> member "oes_extended" with
       | `Null -> false
       | v -> to_bool v);
    (c_oes_fixedpoint :=
       match json |> member "oes_fixedpoint" with
       | `Null -> false
       | v -> to_bool v);
    (c_oes_candidate_limit :=
       match json |> member "oes_candidate_limit" with
       | `Null -> 1
       | v -> to_int v);
    if !c_oes_candidate_limit <= 0 then
      failwith "config: oes_candidate_limit must be positive";
    (c_local_extend :=
       match json |> member "local_extend" with
       | `Null -> false
       | v -> to_bool v);
    (c_local_extend_depth :=
       match json |> member "local_extend_depth" with
       | `Null -> 4
       | v -> to_int v);
    (c_fast_simplify :=
       match json |> member "fast_simplify" with
       | `Null -> false
       | v -> to_bool v);
    c_global_synthesis := json |> member "global_synthesis" |> to_bool;
    if member "local_synthesis" json <> `Null then
      failwith "config: \"local_synthesis\" was renamed to \"chs\"";
    c_chs := json |> member "chs" |> to_bool;
    c_synthesis_timeout := json |> member "synthesis_timeout" |> to_int;
    c_synthesis_repeat := json |> member "synthesis_repeat" |> to_int;
    (c_cegis_retries :=
       match json |> member "cegis_retries" with
       | `Null -> 1
       | v -> to_int v);
    if !c_cegis_retries < 0 then failwith "config: cegis_retries must be nonnegative";
    (c_learn_synthesis_rules :=
       match json |> member "learn_synthesis_rules" with
       | `Null -> true
       | v -> to_bool v);
    c_balanced_tree := json |> member "balanced_tree" |> to_bool;
    c_reject_non_equiv_simplifications :=
      json |> member "reject_non_equiv_simplifications" |> to_bool;
    c_equiv_timeout := json |> member "equiv_timeout" |> to_int;
    c_check_equiv := json |> member "check_equiv" |> to_bool;
    c_nb_samples := json |> member "nb_samples" |> to_int;
    if !c_nb_samples <= 0 then
      failwith "config: nb_samples must be positive";
    if !c_equiv_timeout <= 0 then
      failwith "config: equiv_timeout must be positive";
    c_local_cache := json |> member "local_cache" |> to_bool;
    c_add_constants_to_synthesis :=
      json |> member "add_constants_to_synthesis" |> to_bool;
    (Greysynth_utils.Utils.cost_model :=
       match json |> member "cost_model" with
       | `Null -> Greysynth_utils.Utils.Legacy
       | `String value ->
           (try Greysynth_utils.Utils.cost_model_of_string value
            with Invalid_argument message -> failwith ("config: " ^ message))
       | _ -> failwith "config: cost_model must be a string");

    (* Backend-specific keys are read by the backend itself *)
    (c_synthesizer_name :=
       match json |> member "synthesizer" with
       | `Null -> "xyntia"
       | v -> to_string v);
    c_synthesizer := Synth_backends.select !c_synthesizer_name json;

    g_total_timeout := json |> member "total_timeout" |> to_int |> float_of_int;

    evaluator := Sample_evaluator.make !c_nb_samples;

    let sampling_str = json |> member "sampling_strategy" |> to_string in
    (c_sampling_strategy :=
       match sampling_str with
       | "label" -> LabelValues
       | "real" -> RealValues
       | "wrong_naive" -> WrongNaive
       | _ ->
           failwith
             (Format.sprintf
                "Unknown sampling_strategy: %s (expected 'real' or 'label' or \
                 'wrong_naive')"
                sampling_str));

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
