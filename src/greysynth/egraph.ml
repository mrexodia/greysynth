(* Bounded non-destructive equivalence exploration for preprocessing. Each
   branch owns a proof/cache checkpoint; only the globally extracted branch is
   committed. This is deliberately small while the full per-eclass congruence
   representation is developed. *)

open Greysynth_utils.Utils
open Config
module E = Sexpr.Expr

let associative = function
  | E.Plus | E.Mul | E.And | E.Or | E.Xor -> true
  | _ -> false

let ac_normalize expression =
  let memo = Sexpr.BvTbl.create 128 in
  let rec normalize node =
    match Sexpr.BvTbl.find_opt memo node with
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
        Sexpr.BvTbl.add memo node result;
        result
  in
  normalize expression

let prove_equivalent ~pass left right =
  if E.is_equal left right then true
  else if not (Rewrite.samples_agree left right) then false
  else
    let verdict, _ =
      Rewrite_proof.prove_equality
        ~timeout:(min 1. (float_of_int !c_equiv_timeout)) left right
    in
    if verdict = Yes then (
      Rewrite.record ~pass left right;
      true)
    else false

let optimize expression =
  if not !c_egraph_extraction then expression
  else
    let configured_ac = !c_ac_normalization in
    let configured_fixedpoint = !c_oes_fixedpoint in
    let proof = !(Rewrite.journal) in
    let initial_proof = Option.map Rewrite_proof.checkpoint proof in
    let initial_cache = Rewrite.checkpoint_caches () in
    let restore proof_state cache_state =
      (match proof, proof_state with
      | Some builder, Some checkpoint -> Rewrite_proof.restore builder checkpoint
      | _ -> ());
      Rewrite.restore_caches cache_state
    in
    let run ~ac ~canonical =
      restore initial_proof initial_cache;
      c_ac_normalization := ac;
      let input =
        if not canonical then expression
        else
          let candidate = ac_normalize expression in
          if prove_equivalent ~pass:"egraph-ac" expression candidate then candidate
          else expression
      in
      let result = Normalization.run input in
      let result =
        if !c_oes && not !g_has_timedout then fst (Oes.linear_simplify result)
        else result
      in
      let proof_state = Option.map Rewrite_proof.checkpoint proof in
      let cache_state = Rewrite.checkpoint_caches () in
      (result, proof_state, cache_state)
    in
    Fun.protect
      ~finally:(fun () ->
        c_ac_normalization := configured_ac;
        c_oes_fixedpoint := configured_fixedpoint)
      (fun () ->
        let branches =
          [ run ~ac:false ~canonical:false;
            run ~ac:true ~canonical:false;
            run ~ac:true ~canonical:true ]
        in
        let result, proof_state, cache_state =
          List.fold_left
            (fun ((best, _, _) as selected) ((candidate, _, _) as branch) ->
              let best_cost = size_of_expr best and candidate_cost = size_of_expr candidate in
              if candidate_cost < best_cost
                 || (candidate_cost = best_cost && E.compare candidate best < 0)
              then branch else selected)
            (List.hd branches) (List.tl branches)
        in
        restore proof_state cache_state;
        result)
