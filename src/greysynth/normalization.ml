(* Thin orchestration facade for deterministic normalization.  Algebraic engines
   live in Norm_* modules; this module preserves the historical Normalization API.
   All accepted rewrites still cross Rewrite and independent proof replay. *)

open Config
include Norm_probes

let dag_constant_cast_simplify expression =
  let memo = Nodes.create 128 and constants = Sample_evaluator.make 1 in
  let fold_shift_count node =
    match node with
    | E.Unary { f = (E.Uext _ | E.Sext _ | E.Restrict _);
                x = E.Cst _; _ } ->
        (match constant_cast_fold_candidate constants.eval node with
        | Some candidate
          when Rewrite.accepts ~allow_equal_cost:true ~timeout:0.15
                 ~pass:"constant-cast-prepass" node candidate -> candidate
        | _ -> node)
    | _ -> node
  in
  let rec visit node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Unary { f; x; _ } ->
              let rewritten = visit x in
              if E.is_equal rewritten x then node
              else (try E.unary f rewritten with Invalid_argument _ -> node)
          | E.Binary { f; x; y; _ } ->
              let rewritten_x = visit x
              and rewritten_y =
                let rewritten = visit y in
                if f = E.Lsl then fold_shift_count rewritten else rewritten
              in
              if E.is_equal rewritten_x x && E.is_equal rewritten_y y then node
              else
                (try E.binary f rewritten_x rewritten_y
                 with Invalid_argument _ -> node)
          | E.Ite { c; t; e; _ } ->
              let rewritten_c = visit c and rewritten_t = visit t
              and rewritten_e = visit e in
              if E.is_equal rewritten_c c && E.is_equal rewritten_t t
                 && E.is_equal rewritten_e e
              then node
              else
                (try E.ite rewritten_c rewritten_t rewritten_e
                 with Invalid_argument _ -> node)
          | _ -> node
        in
        Nodes.add memo node result;
        result
  in
  visit expression

let dag_bottom_up_simplify ?(minimal = false) ?(zero_smt = false)
    ?(smt_budget = 1.0) ?deadline expression =
  let memo = Nodes.create 256 in
  let constants = Sample_evaluator.make 1 in
  let cost = Greysynth_utils.Utils.size_of_expr in
  let expression_cost = cost expression in
  let soft_stopped = ref false and smt_spent = ref 0.0
  and opaque_probe_calls = ref 0 and lowk_calls = ref 0 in
  let probe_shell_memo = Nodes.create 128 in
  let rec contains_probe_shell node =
    match Nodes.find_opt probe_shell_memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Unary { f = E.Not; _ }
          | E.Binary { f = (E.And | E.Or | E.Xor | E.Lsl); _ } -> true
          | E.Unary { x; _ } -> contains_probe_shell x
          | E.Binary { x; y; _ } ->
              contains_probe_shell x || contains_probe_shell y
          | E.Ite { c; t; e; _ } ->
              contains_probe_shell c || contains_probe_shell t
              || contains_probe_shell e
          | _ -> false
        in
        Nodes.add probe_shell_memo node result;
        result
  in
  let pure_bitwise root =
    let memo = Nodes.create 32 in
    let rec visit node =
      match Nodes.find_opt memo node with
      | Some result -> result
      | None ->
          let result =
            match node with
            | E.Var _ | E.Cst _ -> true
            | E.Unary { f = E.Not; x; _ } -> visit x
            | E.Binary { f = (E.And | E.Or | E.Xor); x; y; _ } ->
                visit x && visit y
            | _ -> false
          in
          Nodes.add memo node result;
          result
    in
    visit root
  in
  let semilinear_shape root =
    let memo = Nodes.create 32 in
    let rec visit node =
      match Nodes.find_opt memo node with
      | Some result -> result
      | None ->
          let result =
            match node with
            | E.Unary { f = (E.Uext _ | E.Sext _ | E.Restrict _); _ }
            | E.Binary { f = E.Lsl; _ } -> true
            | E.Binary { f = (E.And | E.Or | E.Xor);
                         x = E.Cst _; _ }
            | E.Binary { f = (E.And | E.Or | E.Xor);
                         y = E.Cst _; _ } -> true
            | E.Unary { x; _ } -> visit x
            | E.Binary { x; y; _ } -> visit x || visit y
            | E.Ite { c; t; e; _ } -> visit c || visit t || visit e
            | _ -> false
          in
          Nodes.add memo node result;
          result
    in
    visit root
  in
  let should_stop () =
    let now = Unix.gettimeofday () in
    let local = Option.fold ~none:false ~some:(fun limit -> now >= limit) deadline in
    let global =
      !g_total_timeout > 0.
      && !g_total_timeout -. (now -. !g_start_time) <= 0.35
    in
    if local || global then soft_stopped := true;
    !soft_stopped
  in
  let try_smt thunk =
    if zero_smt || !soft_stopped || !smt_spent >= smt_budget then false
    else
      let started = Unix.gettimeofday () in
      let result =
        try thunk () with Timeout_exception -> soft_stopped := true; false
      in
      smt_spent := !smt_spent +. (Unix.gettimeofday () -. started);
      result
  in
  let rec visit node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        ignore (should_stop ());
        let semantic_child child =
          if minimal || !soft_stopped then child else
          match is_semantically_bitwise cost child with
          | Some candidate
            when Rewrite.accepts_compositional ~pass:"dag-semantic-bitwise"
                   ~equalities:[] ~linear_mba_equalities:[ child, candidate ]
                   child candidate -> candidate
          | _ -> child
        in
        let rebuilt =
          match node with
          | E.Unary { f = E.Not; x; _ } -> E.unary E.Not (semantic_child (visit x))
          | E.Unary { f; x; _ } -> E.unary f (visit x)
          | E.Binary { f = (E.And | E.Or | E.Xor as f); x; y; _ } ->
              E.binary f (semantic_child (visit x)) (semantic_child (visit y))
          | E.Binary { f; x; y; _ } -> E.binary f (visit x) (visit y)
          | E.Ite { c; t; e; _ } -> E.ite (visit c) (visit t) (visit e)
          | _ -> node
        in
        let result = ref rebuilt in
        if not !soft_stopped then
        (try
        (match constant_cast_fold_candidate constants.eval !result with
        | Some candidate
          when try_smt (fun () ->
                 Rewrite.accepts ~allow_equal_cost:true ~timeout:0.15
                   ~pass:"dag-constant-cast" !result candidate) ->
            result := candidate
        | _ -> ());
        (match restrict_factoring_candidate !result with
        | Some candidate
          when try_smt (fun () ->
                 Rewrite.accepts ~allow_equal_cost:true ~timeout:0.15
                   ~pass:"dag-restrict-factor" !result candidate) ->
            result := candidate
        | _ -> ());
        (match bit0_parity_candidate cost !result with
        | Some candidate
          when try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                 ~pass:"dag-bit0-parity" !result candidate) ->
            result := candidate
        | _ -> ());
        (match abstract_slice_candidate !result with
        | Some candidate
          when try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                 ~pass:"dag-abstract-slice" !result candidate) -> result := candidate
        | _ -> ());
        if not zero_smt && cost !result <= 256 && !lowk_calls < 6 then
          (match lowk_restrict_homomorphism_candidate cost !result with
          | Some (candidate, equalities, linear_mba_equalities, ring_equalities) ->
              incr lowk_calls;
              if try_smt (fun () ->
                   Rewrite.accepts_compositional ~timeout:0.15
                     ~pass:"dag-lowk-homomorphism" ~equalities
                     ~linear_mba_equalities ~ring_equalities !result candidate)
              then result := candidate
          | None -> ());
        (match nonlinear_product_identity_candidate !result with
        | Some (candidate, [], linear_mba_equalities,
                semilinear_mba_equalities, ring_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-product-peel"
                 ~equalities:[] ~ring_equalities ~linear_mba_equalities
                 ~semilinear_mba_equalities !result candidate -> result := candidate
        | Some (candidate, equalities, linear_mba_equalities,
                semilinear_mba_equalities, ring_equalities)
          when not zero_smt
               && try_smt (fun () ->
                      Rewrite.accepts_compositional ~pass:"dag-product-peel"
                        ~equalities ~ring_equalities ~linear_mba_equalities
                        ~semilinear_mba_equalities !result candidate) ->
            result := candidate
        | _ -> ());
        (match common_factor_pullout_candidate cost !result with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-factor-pullout"
                 ~equalities:[] ~ring_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        let accept_linear (candidate, ring_equalities, rewritten_source) =
          Rewrite.accepts_compositional ~pass:"dag-linear-mba"
            ~equalities:[] ~ring_equalities
            ~linear_mba_equalities:[ rewritten_source, candidate ]
            !result candidate
        in
        if cost !result >= 3 then (
          let max_atoms =
            let expanded =
              expression_cost <= 4096 && cost !result <= 4096
              && contains_probe_shell !result
            in
            if not minimal && (cost !result <= 512 || expanded)
               && Greysynth_utils.Utils.dag_size_bounded ~limit:1024 !result <= 1024
            then 6 else 4
          in
          let proposals =
            if expression_cost <= 512 && contains_probe_shell !result then
              linear_candidates_with_rings ~max_atoms cost !result
            else
              linear_candidates ~max_atoms cost !result
              |> List.map (fun candidate -> candidate, [], !result)
          in
          let proposals =
            proposals
            |> List.sort (fun (left, _, _) (right, _, _) ->
                   Int.compare (cost left) (cost right))
          in
          (match List.find_opt accept_linear proposals with
          | Some (candidate, _, _) -> result := candidate
          | None ->
              linear_candidates ~max_atoms cost !result
              |> List.sort (fun left right -> Int.compare (cost left) (cost right))
              |> List.find_opt (fun candidate ->
                     accept_linear (candidate, [], !result))
              |> Option.iter (fun candidate -> result := candidate)));
        (match if cost !result >= 15 then gf2_masked_xor_candidate cost !result else None with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-gf2-masked-xor"
                 ~equalities:[] ~semilinear_mba_equalities:[ !result, candidate ]
                 !result candidate
               || (not zero_smt && try_smt (fun () ->
                     Rewrite.accepts ~timeout:0.50 ~pass:"dag-gf2-masked-xor-smt"
                       !result candidate)) -> result := candidate
        | _ -> ());
        (match
           if expression_cost <= 16_384 then semilinear_mba_candidate cost !result
           else semilinear_mba_candidate_with_atoms cost !result
         with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-semilinear-mba"
                 ~equalities:[] ~semilinear_mba_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        (match !result with
        | E.Binary { f = E.Plus; x; y; _ }
          when expression_cost <= 16_384 && cost !result <= 24
               && pure_bitwise x && pure_bitwise y ->
            let candidate = E.binary E.Xor x y in
            if Rewrite.samples_agree !result candidate
               && Rewrite.accepts_compositional ~allow_equal_cost:true
                    ~pass:"dag-disjoint-sum-xor" ~equalities:[]
                    ~linear_mba_equalities:[ !result, candidate ]
                    !result candidate
            then result := candidate
        | _ -> ());
        if Greysynth_utils.Utils.dag_size_bounded ~limit:512 !result <= 512 then (
          (match complementary_slice_refine_candidate cost !result with
          | Some (candidate, equalities, ring_equalities)
            when not zero_smt
                 && try_smt (fun () ->
                        Rewrite.accepts_compositional ~timeout:0.15
                          ~pass:"dag-complementary-slice" ~equalities
                          ~ring_equalities !result candidate) ->
              result := candidate
          | _ -> ());
          (match mask_lift_candidate cost !result with
          | Some candidate
            when cost !result <= 512
                 && try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                      ~pass:"dag-mask-lift" !result candidate) ->
              result := candidate
          | _ -> ()));
        if not zero_smt || cost !result <= 512 then
          (match nonlinear_poly_candidate ~max_cost:2048 cost !result with
          | Some (candidate, linear_mba_equalities, ring_equalities,
                  final_linear_equalities)
            when Rewrite.accepts_compositional ~pass:"dag-minterm-ring-poly"
                   ~equalities:[] ~ring_equalities
                   ~linear_mba_equalities:(linear_mba_equalities @ final_linear_equalities)
                   !result candidate -> result := candidate
          | _ -> ());
        if not minimal then (
        (if cost !result <= 256 then
           match known_bits_candidate cost !result with
           | Some candidate
             when try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                    ~pass:"dag-known-bits" !result candidate) ->
               result := candidate
           | _ -> ());
        (match xor_affine_mask_candidate cost !result with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-xor-affine-mask"
                 ~equalities:[] ~semilinear_mba_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        let accept_probe candidate =
          Rewrite.accepts_compositional ~pass:"dag-semantic-probe-linear"
            ~equalities:[] ~linear_mba_equalities:[ !result, candidate ]
            !result candidate
          || ((semilinear_shape !result || semilinear_shape candidate)
              && Rewrite.accepts_compositional
                   ~pass:"dag-semantic-probe-semilinear" ~equalities:[]
                   ~semilinear_mba_equalities:[ !result, candidate ]
                   !result candidate)
          || try_smt (fun () -> Rewrite.accepts ~timeout:0.25
               ~pass:"dag-semantic-probe" !result candidate)
        in
        if not zero_smt && !smt_spent < smt_budget
           && !opaque_probe_calls < 16
           && cost !result >= 9 && cost !result <= 256
           && contains_probe_shell !result
        then
          (match probe_opaque_atoms ~maximal_repeated:false cost !result with
          | Some candidate ->
              incr opaque_probe_calls;
              if accept_probe candidate then result := candidate
          | None -> ());
        if cost !result >= 5 && cost !result <= 64 then (
          let probes =
            [ probe_low_width_exact cost !result;
              probe_semantic_linear_mba cost !result;
              probe_semantic_poly cost !result ]
            |> List.filter_map Fun.id
            |> List.sort (fun left right -> Int.compare (cost left) (cost right))
          in
          match probes with
          | candidate :: _ when accept_probe candidate -> result := candidate
          | _ -> ());
        (match power2_pullout_candidate cost !result with
        | Some candidate
          when cost !result <= 512
               && try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                      ~pass:"dag-power2-pullout" !result candidate) ->
            result := candidate
        | _ -> ());
        (match demand_bits_candidate cost !result with
        | Some candidate
          when cost !result <= 512
               && try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                      ~pass:"dag-demand-bits" !result candidate) ->
            result := candidate
        | _ -> ());
        (match pair_complementary_atoms cost !result with
        | Some (candidate, ring_equalities, linear_mba_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-complementary-atoms"
                 ~equalities:[] ~ring_equalities ~linear_mba_equalities
                 !result candidate -> result := candidate
        | _ -> ());
        (match correlated_null_candidate cost !result with
        | Some (candidate, ring_equalities, linear_mba_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-correlated-null"
                 ~equalities:[] ~ring_equalities ~linear_mba_equalities
                 !result candidate -> result := candidate
        | _ -> ()));
        (match reduce_modular_polynomial cost !result with
        | Some (candidate, equalities, poly_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-poly-mod2w"
                 ~equalities ~poly_equalities !result candidate -> result := candidate
        | _ -> ());
        (match ring_not_bridge_candidate cost !result with
        | Some (candidate, linear_mba_equalities, ring_equalities)
          when Rewrite.accepts_compositional ~pass:"dag-ring-not-mod2w"
                 ~equalities:[] ~linear_mba_equalities ~ring_equalities
                 !result candidate -> result := candidate
        | _ -> ());
        (match !result with
        | E.Binary { f = (E.Plus | E.Minus | E.Mul); _ }
          when cost !result <= 256 && contains_probe_shell !result ->
            (match recursive_bitwise_ac_candidate !result with
            | Some (candidate, linear_mba_equalities, ring_equalities)
              when Rewrite.accepts_compositional ~allow_equal_cost:true
                     ~pass:"dag-bitwise-ac" ~equalities:[]
                     ~linear_mba_equalities ~ring_equalities !result candidate ->
                result := candidate
            | _ -> ())
        | _ -> ());
        (match ring_polynomial_candidate cost !result with
        | Some candidate
          when Rewrite.accepts_compositional ~pass:"dag-ring-mod2w"
                 ~equalities:[] ~ring_equalities:[ !result, candidate ]
                 !result candidate -> result := candidate
        | _ -> ());
        (match peepholes constants.eval !result with
        | candidate :: _
          when cost !result <= 512
               && try_smt (fun () -> Rewrite.accepts ~timeout:0.15
                      ~pass:"dag-peephole" !result candidate) ->
            result := candidate
        | _ -> ())
        with Timeout_exception -> soft_stopped := true);
        Nodes.add memo node !result;
        !result
  in
  visit expression

let oracle_compatible expression =
  let width = E.sizeof expression in
  let rec inspect = function
    | E.Var variable -> variable.size = width
    | E.Cst value -> Bitvector.size_of value = width
    | E.Unary { f = (E.Not | E.Minus); x; _ } -> inspect x
    | E.Binary { f = (E.Plus | E.Minus | E.Mul | E.And | E.Or | E.Xor);
                 x; y; _ } -> inspect x && inspect y
    | E.Binary { f = E.Lsl; x; y = (E.Cst _ as y); _ } -> inspect x && inspect y
    | _ -> false
  in
  inspect expression

let oracle_candidate expression =
  if !c_mba_oracle = "none" then None
  else
    let width = E.sizeof expression in
    let variables = Hashtbl.create 16 in
    let rec inspect = function
      | E.Var variable when variable.size = width ->
          Hashtbl.replace variables (variable.name, variable.size) (); true
      | E.Cst value -> Bitvector.size_of value = width
      | E.Unary { f = (E.Not | E.Minus); x; _ } -> inspect x
      | E.Binary { f = (E.Plus | E.Minus | E.Mul | E.And | E.Or | E.Xor);
                   x; y; _ } -> inspect x && inspect y
      | E.Binary { f = E.Lsl; x; y = (E.Cst _ as y); _ } -> inspect x && inspect y
      | _ -> false
    in
    if not (inspect expression) then None
    else
      let variables =
        Hashtbl.fold (fun variable () result -> variable :: result) variables []
        |> List.sort Stdlib.compare |> Array.of_list
      in
      let positions = Hashtbl.create (Array.length variables) in
      Array.iteri (fun index variable -> Hashtbl.add positions variable index) variables;
      let rec rename = function
        | E.Var variable ->
            let index = Hashtbl.find positions (variable.name, variable.size) in
            E.var (Printf.sprintf "v%d" index) variable.size
              (Printf.sprintf "v%d" index)
        | E.Unary { f; x; _ } -> E.unary f (rename x)
        | E.Binary { f; x; y; _ } -> E.binary f (rename x) (rename y)
        | node -> node
      in
      let rendered = Greysynth_utils.Utils.pp ~show_size:false (rename expression) in
      let command =
        match !c_mba_oracle with
        | "rumba" ->
            Printf.sprintf "%s --n %d %s" !c_mba_oracle_command width
              (Filename.quote rendered)
        | "cobra" ->
            Printf.sprintf "%s --mba %s --bitwidth %d" !c_mba_oracle_command
              (Filename.quote rendered) width
        | _ -> assert false
      in
      try
        let timeout =
          if !g_total_timeout <= 0. then !c_mba_oracle_timeout
          else
            let remaining =
              !g_total_timeout -. (Unix.gettimeofday () -. !g_start_time)
              |> floor |> int_of_float
            in
            if remaining <= 0 then raise Timeout_exception;
            min !c_mba_oracle_timeout remaining
        in
        let output =
          Synth_backends.run_command ~timeout command
          |> String.split_on_char '\n'
          |> List.filter (fun line -> String.trim line <> "")
          |> List.rev
        in
        let rec restore = function
              | E.Var variable when String.length variable.name >= 2
                                  && variable.name.[0] = 'v' ->
                  let index =
                    int_of_string
                      (String.sub variable.name 1 (String.length variable.name - 1))
                  in
                  let name, size = variables.(index) in
                  if variable.size <> size then failwith "MBA oracle changed variable width";
                  E.var name size name
              | E.Var _ -> failwith "MBA oracle returned an unknown variable"
              | E.Unary { f; x; _ } -> E.unary f (restore x)
              | E.Binary { f; x; y; _ } -> E.binary f (restore x) (restore y)
              | E.Ite _ | E.Load _ -> failwith "MBA oracle returned an unsupported node"
              | node -> node
            in
        let rec parse = function
          | [] -> None
          | answer :: rest ->
              (try
                 let parsed =
                   String_to_sexpr.parse ~default_size:width (String.trim answer)
                 in
                 let candidate = restore parsed in
                 if E.sizeof candidate = width then Some candidate else parse rest
               with _ -> parse rest)
        in
        parse output
      with
      | Config.Timeout_exception -> raise Config.Timeout_exception
      | exn ->
          Logging._log_warn "mba-oracle" "%s" (Printexc.to_string exn);
          None

exception Soft_normalization_stop

let run ?deadline expression =
  let check_timeout () =
    Config.check_timeout ();
    match deadline with
    | Some limit when Unix.gettimeofday () >= limit -> raise Soft_normalization_stop
    | _ -> ()
  in
  let results = Nodes.create 128 in
  let sizes = Nodes.create 128 in
  let constants = Sample_evaluator.make 1 in
  let oracle_calls = ref 0 in
  let rec cost expression =
    match Nodes.find_opt sizes expression with
    | Some value -> value
    | None ->
        let open Greysynth_utils.Utils in
        let value =
          match expression with
          | E.Unary { f; x; _ } -> unary_cost !cost_model f + cost x
          | E.Binary { f; x; y; _ } -> binary_cost !cost_model f + cost x + cost y
          | E.Ite { c; t; e; _ } ->
              conditional_cost !cost_model + cost c + cost t + cost e
          | _ -> 1
        in
        Nodes.add sizes expression value;
        value
  in
  let try_oracle current =
    if !oracle_calls >= !c_mba_oracle_calls || cost current < 11
       || !c_mba_oracle = "none" || not (oracle_compatible current)
    then None
    else (
      incr oracle_calls;
      match oracle_candidate current with
      | Some candidate when cost candidate < cost current ->
          let accepted =
            if not (Rewrite.samples_agree current candidate) then
              Rewrite.accepts ~pass:"mba-oracle" current candidate
            else
              match minterm_ring_proof current candidate with
              | Some (equalities, ring_equalities) ->
                  Rewrite.accepts_compositional ~pass:"mba-oracle-ring"
                    ~equalities ~ring_equalities current candidate
              | None -> Rewrite.accepts ~pass:"mba-oracle" current candidate
          in
          if accepted then Some candidate else None
      | _ -> None)
  in
  let rec oracle_visit node =
    if !g_has_timedout then node
    else (
      check_timeout ();
      if oracle_compatible node && cost node >= 11 then
        Option.value (try_oracle node) ~default:node
      else
        match node with
        | E.Unary { f; x; _ } -> E.unary f (oracle_visit x)
        | E.Binary { f; x; y; _ } ->
            E.binary f (oracle_visit x) (oracle_visit y)
        | E.Ite { c; t; e; _ } ->
            E.ite (oracle_visit c) (oracle_visit t) (oracle_visit e)
        | _ -> node)
  in
  let rec visit ?(allow_oracle = true) original =
    if !g_has_timedout then original
    else match Nodes.find_opt results original with
    | Some result -> result
    | None ->
        let current = ref original in
        (try
           check_timeout ();
           let accept_minterm pass candidate =
             if not (Rewrite.samples_agree original candidate) then false
             else
               match minterm_ring_proof original candidate with
               | Some (equalities, ring_equalities) ->
                   Rewrite.accepts_compositional ~pass
                     ~equalities ~ring_equalities original candidate
               | None -> Rewrite.accepts ~pass original candidate
           in
           let early_null =
             match reduce_univariate_null_polynomial cost original with
             | Some (candidate, equalities, ring_equalities)
               when Rewrite.accepts_compositional ~pass:"falling-null"
                      ~equalities ~ring_equalities original candidate -> Some candidate
             | _ ->
                 peepholes constants.eval original
                 |> List.find_opt (fun candidate ->
                        is_number Z.zero candidate
                        && cost candidate < cost original
                        && Rewrite.accepts ~pass:"falling-null" original candidate)
           in
           let early_minterm =
             if Option.is_some early_null || cost original < 11 then None
             else
               Sample_evaluator.variables_of_expr original
               |> List.map (fun (name, width) -> E.var name width name)
               |> List.filter (fun candidate -> cost candidate < cost original)
               |> List.find_opt (accept_minterm "minterm-ring-mba")
           in
           (match early_null, early_minterm with
           | Some candidate, _ | None, Some candidate -> current := visit candidate
           | None, None ->
               current := (match original with
                 | E.Unary { f; x; _ } -> E.unary f (visit ~allow_oracle x)
                 | E.Binary { f; x; y; _ } ->
                     let x = visit ~allow_oracle x in
                     let y = visit ~allow_oracle y in
                     E.binary f x y
                 | E.Ite { c; t; e; _ } ->
                     let c = visit ~allow_oracle c in
                     let t = visit ~allow_oracle t in
                     let e = visit ~allow_oracle e in
                     E.ite c t e
                 | _ -> original));
           if Option.is_none early_minterm && not !g_has_timedout then (
             let oracle = if allow_oracle then try_oracle !current else None in
             match oracle with
             | Some candidate -> current := candidate; current := visit ~allow_oracle:false candidate
             | None ->
             let bitsliced =
               match if cost original >= 11 then bitsliced_candidate cost original else None with
               | Some candidate when cost candidate < cost !current
                                     && Rewrite.samples_agree original candidate ->
                   (match
                      first_some
                        (bitsliced_ring_proof original candidate)
                        (minterm_ring_proof original candidate)
                    with
                   | Some (equalities, ring_equalities)
                     when Rewrite.accepts_compositional ~pass:"bitsliced"
                            ~equalities ~ring_equalities original candidate ->
                       Some candidate
                   | _ ->
                       if Rewrite.accepts ~pass:"bitsliced" original candidate
                       then Some candidate else None)
               | _ -> None
             in
             let minterm_polynomial =
               match bitsliced with
               | Some candidate -> Some (candidate, [], [])
               | None when cost !current < 11 -> None
               | None ->
                   (match minterm_polynomial_candidate cost !current with
                   | Some (candidate, equalities, ring_equalities)
                     when Rewrite.samples_agree !current candidate
                          && Rewrite.accepts_compositional ~pass:"minterm-polynomial"
                               ~equalities ~ring_equalities !current candidate ->
                       Some (candidate, equalities, ring_equalities)
                   | _ -> None)
             in
             let factor_grouped =
               match minterm_polynomial with
               | Some (candidate, _, _) -> Some candidate
               | None when cost !current < 11 -> None
               | None ->
                   (match factor_group_candidate cost !current with
                   | Some (candidate, equalities, ring_equalities)
                     when Rewrite.accepts_compositional ~pass:"factor-group"
                            ~equalities ~ring_equalities !current candidate ->
                       Some candidate
                   | _ -> None)
             in
             let ring_normalized =
               match factor_grouped with
               | Some candidate -> Some candidate
               | None when cost !current < 5 -> None
               | None ->
                   (match ring_polynomial_candidate cost !current with
                   | Some candidate
                     when Rewrite.samples_agree !current candidate
                          && Rewrite.accepts_compositional ~pass:"ring-polynomial"
                               ~equalities:[] ~ring_equalities:[ !current, candidate ]
                               !current candidate -> Some candidate
                   | _ -> None)
             in
             let lowk_decomposed =
               if cost !current < 5 || cost !current > 256 then None
               else
                 match lowk_restrict_homomorphism_candidate cost !current with
                 | Some (candidate, equalities, linear_mba_equalities,
                         ring_equalities)
                   when Rewrite.accepts_compositional ~timeout:0.4
                          ~pass:"normalize-lowk-homomorphism" ~equalities
                          ~linear_mba_equalities ~ring_equalities
                          !current candidate -> Some candidate
                 | _ -> None
             in
             let linear_decomposed =
               if not (E.is_equal !current expression)
                  || cost !current < 4 || cost !current > 10_000
               then None
               else
                 let enhanced =
                   cost !current <= 512 && has_bitwise_operator !current
                 in
                 let proposals =
                   (if enhanced then linear_candidates_with_rings cost !current
                    else linear_candidates cost !current
                         |> List.map (fun candidate -> candidate, [], !current))
                   |> List.sort (fun (left, _, _) (right, _, _) ->
                          Int.compare (cost left) (cost right))
                 in
                 let accepted =
                   List.find_opt
                     (fun (candidate, ring_equalities, rewritten_source) ->
                       Rewrite.accepts_compositional
                         ~pass:"normalize-linear-mba" ~equalities:[]
                         ~ring_equalities
                         ~linear_mba_equalities:[ rewritten_source, candidate ]
                         !current candidate)
                     proposals
                 in
                 (match accepted with
                 | Some (candidate, _, _) -> Some candidate
                 | None when enhanced ->
                     linear_candidates cost !current
                     |> List.sort (fun left right -> Int.compare (cost left) (cost right))
                     |> List.find_opt (fun candidate ->
                            Rewrite.accepts_compositional
                              ~pass:"normalize-linear-mba-fallback" ~equalities:[]
                              ~linear_mba_equalities:[ !current, candidate ]
                              !current candidate)
                 | None -> None)
             in
             let decomposed =
               match lowk_decomposed with
               | Some candidate -> Some candidate
               | None ->
                   (match nonlinear_product_identity_candidate !current with
                   | Some (candidate, equalities, linear_mba_equalities,
                           semilinear_mba_equalities, ring_equalities)
                     when cost candidate < cost !current
                          && Rewrite.accepts_compositional ~pass:"product-peel"
                               ~equalities ~ring_equalities
                               ~linear_mba_equalities ~semilinear_mba_equalities
                               !current candidate -> Some candidate
                   | _ ->
                       (match ring_normalized with
                       | Some candidate -> Some candidate
                       | None ->
                           (match product_partition_candidate !current with
                           | Some (candidate, equalities)
                             when cost candidate < cost !current
                                  && Rewrite.accepts_compositional ~pass:"polynomial"
                                       ~equalities !current candidate ->
                               Some candidate
                           | _ -> linear_decomposed)))
             in
             match decomposed with
             | Some candidate ->
                 current := candidate;
                 current := visit ~allow_oracle candidate
             | None ->
                 let candidates = peepholes constants.eval !current
                     @ (if !c_ac_normalization then canonical_candidates !current else [])
                     @ (if cost !current >= 4 then linear_candidates cost !current else []) in
                 let candidates = List.filter (fun candidate -> cost candidate < cost !current) candidates in
                 let candidates = List.sort_uniq (fun a b ->
                     let order = Int.compare (cost a) (cost b) in
                     if order = 0 then E.compare a b else order) candidates in
                 let accepts candidate =
                   let fallback () =
                     match complement_product_steps !current candidate with
                     | Some (equalities, ring_equalities) ->
                         if Rewrite.accepts_compositional ~pass:"linear-mba"
                              ~equalities ~ring_equalities !current candidate
                         then true
                         else Rewrite.accepts ~pass:"normalize" !current candidate
                     | None -> Rewrite.accepts ~pass:"normalize" !current candidate
                   in
                   if List.length (Sample_evaluator.variables_of_expr !current) >= 3
                      && linear_mba_compatible !current
                      && Rewrite.accepts_compositional ~pass:"linear-mba-mod2w"
                           ~equalities:[]
                           ~linear_mba_equalities:[ !current, candidate ]
                           !current candidate
                   then true
                   else if not (Rewrite.samples_agree !current candidate) then
                     Rewrite.accepts ~pass:"normalize" !current candidate
                   else
                     match minterm_ring_proof !current candidate with
                     | Some (equalities, ring_equalities) ->
                         if Rewrite.accepts_compositional ~pass:"minterm-ring-mba"
                              ~equalities ~ring_equalities !current candidate
                         then true else fallback ()
                     | None -> fallback ()
                 in
                 match List.find_opt accepts candidates with
                 | Some candidate ->
                     current := candidate;
                     current := visit ~allow_oracle candidate
                 | None -> ())
         with
         | Soft_normalization_stop -> ()
         | Timeout_exception -> g_has_timedout := true);
        Nodes.replace results original !current;
        !current
  in
  let expression =
    if !c_mba_oracle = "none" || !c_mba_oracle_calls = 0 then expression
    else
      try oracle_visit expression with Soft_normalization_stop -> expression
  in
  let root_bitsliced =
    if cost expression > 512 then None
    else
      match bitsliced_candidate cost expression with
      | Some candidate when Rewrite.samples_agree expression candidate ->
          (match
             first_some
               (bitsliced_ring_proof expression candidate)
               (minterm_ring_proof expression candidate)
           with
          | Some (equalities, ring_equalities)
            when Rewrite.accepts_compositional ~pass:"bitsliced-root"
                   ~equalities ~ring_equalities expression candidate ->
              Some candidate
          | _ -> None)
      | _ -> None
  in
  match root_bitsliced with
  | Some candidate -> visit ~allow_oracle:false candidate
  | None -> visit ~allow_oracle:false expression
