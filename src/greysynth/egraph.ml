(* Bounded non-destructive equivalence search used in place of ordinary
   normalization+OES preprocessing. Branches retain independent proof/cache
   checkpoints and only the globally extracted branch is committed. *)

open Greysynth_utils.Utils
open Config
module E = Sexpr.Expr
module Nodes = Sexpr.BvTbl

let last_enodes = ref 0
let last_iterations = ref 0
let last_fallback = ref false
let statistics () = (!last_enodes, !last_iterations)
let fell_back () = !last_fallback

type branch = {
  expression : E.t;
  proof : Rewrite_proof.checkpoint option;
  cache : Rewrite.cache_checkpoint;
}

let associative = function
  | E.Plus | E.Mul | E.And | E.Or | E.Xor -> true
  | _ -> false

let ac_normalize expression =
  let memo = Nodes.create 128 in
  let rec normalize node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        let result =
          match node with
          | E.Unary { f; x; _ } -> E.unary f (normalize x)
          | E.Binary { f; x; y; _ } when associative f ->
              let rec flatten result = function
                | E.Binary { f = child_op; x; y; _ } when child_op = f ->
                    flatten (flatten result x) y
                | child -> normalize child :: result
              in
              let terms = flatten (flatten [] x) y |> List.sort E.compare in
              let rec build = function
                | [] -> assert false
                | [ term ] -> term
                | terms ->
                    let count = List.length terms in
                    let rec split n left rest =
                      if n = 0 then (List.rev left, rest)
                      else match rest with
                        | head :: tail -> split (n - 1) (head :: left) tail
                        | [] -> assert false
                    in
                    let left, right = split (count / 2) [] terms in
                    E.binary f (build left) (build right)
              in
              build terms
          | E.Binary { f; x; y; _ } -> E.binary f (normalize x) (normalize y)
          | E.Ite { c; t; e; _ } -> E.ite (normalize c) (normalize t) (normalize e)
          | _ -> node
        in
        Nodes.add memo node result;
        result
  in
  normalize expression

let optimize expression =
  last_enodes := 0;
  last_iterations := 0;
  last_fallback := false;
  let variable_count =
    Sample_evaluator.variables_of_expr expression |> List.length
  in
  if not !c_egraph_extraction || variable_count < 2
     || size_of_expr expression > !c_egraph_max_enodes then (
    last_fallback := true;
    expression)
  else
    let proof_builder = !(Rewrite.journal) in
    let initial_proof = Option.map Rewrite_proof.checkpoint proof_builder in
    let initial_cache = Rewrite.checkpoint_caches () in
    let configured_ac = !c_ac_normalization in
    let configured_fixedpoint = !c_oes_fixedpoint in
    let restore branch =
      (match proof_builder, branch.proof with
      | Some builder, Some checkpoint -> Rewrite_proof.restore builder checkpoint
      | _ -> ());
      Rewrite.restore_caches branch.cache
    in
    let checkpoint expression =
      {
        expression;
        proof = Option.map Rewrite_proof.checkpoint proof_builder;
        cache = Rewrite.checkpoint_caches ();
      }
    in
    let initial = { expression; proof = initial_proof; cache = initial_cache } in
    let seen = Nodes.create 256 in
    Nodes.add seen expression ();
    let all = ref [ initial ] and frontier = ref [ initial ] in
    last_enodes := 1;
    last_iterations := 0;
    let add_candidate ?(proved = false) ?(ring = false) base candidate =
      if List.length !all >= !c_egraph_max_enodes || Nodes.mem seen candidate then ()
      else if not (Rewrite.samples_agree base.expression candidate) then ()
      else
        let accepted =
          if E.is_equal base.expression candidate || proved then true
          else if ring then (
            let local = Rewrite_proof.create base.expression in
            Rewrite_proof.record_ring local ~pass:"egraph-ac" base.expression candidate;
            let certificate = Rewrite_proof.finish local candidate in
            let report =
              Rewrite_proof.verify ~timeouts:[ min 1. (float_of_int !c_equiv_timeout) ]
                ~original:base.expression ~candidate certificate
            in
            if Yojson.Basic.Util.member "verification" report
               = `String "proved_compositional"
            then (
              Option.iter
                (fun journal ->
                  Rewrite_proof.record_ring journal ~pass:"egraph-ac"
                    base.expression candidate)
                !(Rewrite.journal);
              true)
            else false)
          else false
        in
        if accepted then (
          Nodes.add seen candidate ();
          let branch = checkpoint candidate in
          all := branch :: !all;
          frontier := branch :: !frontier)
    in
    Fun.protect
      ~finally:(fun () ->
        c_ac_normalization := configured_ac;
        c_oes_fixedpoint := configured_fixedpoint)
      (fun () ->
        for iteration = 1 to !c_egraph_max_iters do
          check_timeout ();
          last_iterations := iteration;
          let current = !frontier in
          frontier := [];
          List.iter
            (fun branch ->
              if List.length !all < !c_egraph_max_enodes then (
                restore branch;
                let canonical = ac_normalize branch.expression in
                add_candidate ~ring:true branch canonical;
                restore branch;
                c_ac_normalization := false;
                let normalized = Normalization.run branch.expression in
                add_candidate ~proved:true branch normalized;
                restore branch;
                c_ac_normalization := true;
                let ac = Normalization.run branch.expression in
                add_candidate ~proved:true branch ac;
                if !c_oes && not !g_has_timedout then (
                  restore branch;
                  let oes = fst (Oes.linear_simplify branch.expression) in
                  add_candidate ~proved:true branch oes)))
            current;
          last_enodes := List.length !all
        done;
        let selected =
          List.fold_left
            (fun best candidate ->
              let best_cost = size_of_expr best.expression
              and candidate_cost = size_of_expr candidate.expression in
              if candidate_cost < best_cost
                 || (candidate_cost = best_cost
                     && E.compare candidate.expression best.expression < 0)
              then candidate else best)
            initial !all
        in
        restore selected;
        selected.expression)
