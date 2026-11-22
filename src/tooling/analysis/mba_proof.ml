(* Independently replay a producer certificate against externally supplied
   expressions. No synthesis state, proof cache, or reported verdict is trusted. *)
let usage =
  "Usage: mba_proof -obf -string-file INPUT -gt -string-file OUTPUT \
   [-size WIDTH] CERTIFICATE.json [SECONDS[,RETRY_SECONDS...]]"

let () =
  let input = Cli_input.parse_command_line ~usage in
  let certificate, timeouts =
    match input.positional with
    | [path] -> path, [1.]
    | [path; schedule] ->
        let values =
          try String.split_on_char ',' schedule |> List.map float_of_string
          with _ -> Cli_input.fail_usage usage "Error: invalid timeout schedule\n"
        in
        path, values
    | _ -> Cli_input.fail_usage usage "Error: expected a certificate and optional timeout schedule\n"
  in
  let candidate = match input.gt with
    | Some candidate -> candidate
    | None -> Cli_input.fail_usage usage "Error: -gt must specify the actual output expression\n"
  in
  let report =
    try Rewrite_proof.verify ~timeouts ~original:input.obf ~candidate
      (Yojson.Basic.from_file certificate)
    with exn -> `Assoc [
      "verification", `String "error"; "equiv", `String "ukn";
      "reason", `String ("invalid_certificate: " ^ Printexc.to_string exn)]
  in
  Format.printf "%s\n" (Yojson.Basic.pretty_to_string report)
