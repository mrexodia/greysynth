open Greysynth_utils.Utils
open Config
module E = Sexpr.Expr
module Nodes = Sexpr.BvTbl

type shape =
  | Var of string
  | Cst of Bitvector.t
  | Unary of Term.unary E.op * int
  | Binary of Term.binary E.op * int * int
  | Ite of int * int * int

type enode = {
  id : int;
  width : int;
  shape : shape;
  raw_children : int list;
  expr : E.t;
}

type proof = {
  lhs : E.t;
  rhs : E.t;
  smt_edges : (E.t * E.t) list;
  ring_edges : (E.t * E.t) list;
  poly_edges : (E.t * E.t) list;
  pass : string;
}

type justification = Congruence | Proof of proof

type graph = {
  limit : int;
  mutable count : int;
  enodes : enode option array;
  parent : int array;
  rank : int array;
  classes : (int, int list) Hashtbl.t;
  hashcons : ((int * shape), int) Hashtbl.t;
  expressions : int Nodes.t;
  proof_adj : (int, (int * justification) list) Hashtbl.t;
  semantic_failures : (int * int, unit) Hashtbl.t;
}

let last_enodes = ref 0
let last_iterations = ref 0
let last_fallback = ref false
let statistics () = (!last_enodes, !last_iterations)
let fell_back () = !last_fallback

let graph limit =
  {
    limit;
    count = 0;
    enodes = Array.make limit None;
    parent = Array.init limit Fun.id;
    rank = Array.make limit 0;
    classes = Hashtbl.create 128;
    hashcons = Hashtbl.create 256;
    expressions = Nodes.create 256;
    proof_adj = Hashtbl.create 128;
    semantic_failures = Hashtbl.create 128;
  }

let rec find graph id =
  if graph.parent.(id) = id then id
  else (
    graph.parent.(id) <- find graph graph.parent.(id);
    graph.parent.(id))

let node graph id = Option.get graph.enodes.(id)

let canonical_shape graph = function
  | Unary (op, child) -> Unary (op, find graph child)
  | Binary (op, left, right) -> Binary (op, find graph left, find graph right)
  | Ite (condition, yes, no) ->
      Ite (find graph condition, find graph yes, find graph no)
  | shape -> shape

let add_proof_edge graph left right justification =
  let add source target =
    let previous = Option.value (Hashtbl.find_opt graph.proof_adj source) ~default:[] in
    Hashtbl.replace graph.proof_adj source ((target, justification) :: previous)
  in
  add left right;
  add right left

let union graph left right justification =
  let left_root = find graph left and right_root = find graph right in
  if left_root = right_root then false
  else (
    let keep, merge =
      if graph.rank.(left_root) < graph.rank.(right_root) then
        (right_root, left_root)
      else (left_root, right_root)
    in
    graph.parent.(merge) <- keep;
    if graph.rank.(left_root) = graph.rank.(right_root) then
      graph.rank.(keep) <- graph.rank.(keep) + 1;
    let keep_nodes = Option.value (Hashtbl.find_opt graph.classes keep) ~default:[] in
    let merge_nodes = Option.value (Hashtbl.find_opt graph.classes merge) ~default:[] in
    Hashtbl.replace graph.classes keep (keep_nodes @ merge_nodes);
    Hashtbl.remove graph.classes merge;
    add_proof_edge graph left right justification;
    true)

exception Full
exception Egraph_budget

let raw_children = function
  | Var _ | Cst _ -> []
  | Unary (_, child) -> [ child ]
  | Binary (_, left, right) -> [ left; right ]
  | Ite (condition, yes, no) -> [ condition; yes; no ]

let add_expr graph expression =
  let allocate expression shape children =
    if graph.count >= graph.limit then raise Full;
    let id = graph.count in
    graph.count <- graph.count + 1;
    let enode =
      { id; width = E.sizeof expression; shape; raw_children = children; expr = expression }
    in
    graph.enodes.(id) <- Some enode;
    graph.parent.(id) <- id;
    Hashtbl.add graph.classes id [ id ];
    Nodes.replace graph.expressions expression id;
    id
  in
  let rec add expression =
    match Nodes.find_opt graph.expressions expression with
    | Some id -> id
    | None ->
        let shape =
          match expression with
          | E.Var variable -> Var variable.name
          | E.Cst value -> Cst value
          | E.Unary { f; x; _ } -> Unary (f, add x)
          | E.Binary { f; x; y; _ } -> Binary (f, add x, add y)
          | E.Ite { c; t; e; _ } -> Ite (add c, add t, add e)
          | E.Load _ -> raise Full
        in
        let children = raw_children shape in
        let shape = canonical_shape graph shape in
        let key = E.sizeof expression, shape in
        match Hashtbl.find_opt graph.hashcons key with
        | Some existing when E.is_equal (node graph existing).expr expression ->
            Nodes.replace graph.expressions expression existing;
            existing
        | Some existing ->
            let id = allocate expression shape children in
            ignore (union graph id existing Congruence);
            id
        | None ->
            let id = allocate expression shape children in
            Hashtbl.add graph.hashcons key id;
            id
  in
  add expression

let representatives graph =
  Hashtbl.fold
    (fun root ids result ->
      let root = find graph root in
      if List.mem_assoc root result then result else (root, ids) :: result)
    graph.classes []

let cheapest graph ids =
  List.fold_left
    (fun best id ->
      let expression = (node graph id).expr in
      match best with
      | None -> Some (id, expression)
      | Some (_, previous) ->
          let cost = size_of_expr expression and previous_cost = size_of_expr previous in
          if cost < previous_cost || (cost = previous_cost && E.compare expression previous < 0)
          then Some (id, expression) else best)
    None ids
  |> Option.get

let verify_local ?(timeout_cap = 0.5) ~local_deadline
    (candidate : Normalization.local_candidate) lhs rhs =
  if not (Rewrite.samples_agree lhs rhs) then false
  else
    let timeout =
      let local_remaining = local_deadline -. Unix.gettimeofday () in
      let global_remaining =
        if !g_total_timeout <= 0. then infinity
        else !g_total_timeout -. (Unix.gettimeofday () -. !g_start_time)
      in
      min timeout_cap (min (float_of_int !c_equiv_timeout)
                 (min local_remaining global_remaining))
    in
    let direct =
      match candidate.poly_equalities, candidate.ring_equalities,
            candidate.equalities with
      | [], [], [ (left, right) ] ->
          (E.is_equal left lhs && E.is_equal right rhs)
          || (E.is_equal left rhs && E.is_equal right lhs)
      | _ -> false
    in
    if timeout <= 0. then false
    else if direct then
      let key = Rewrite.proof_key lhs rhs in
      let cached =
        match Hashtbl.find_opt Rewrite.proofs key with
        | Some (Yes | No as verdict) -> Some verdict
        | Some (Unknown | Timeout | Disabled as verdict) ->
            let attempted =
              Option.value (Hashtbl.find_opt Rewrite.proof_budgets key)
                ~default:Float.infinity
            in
            if attempted >= timeout then Some verdict else None
        | None -> None
      in
      let verdict =
        match cached with
        | Some verdict -> verdict
        | None ->
            let verdict, _, _ =
              Rewrite_proof.prove_equality_with_model ~timeout lhs rhs
            in
            Hashtbl.replace Rewrite.proofs key verdict;
            Hashtbl.replace Rewrite.proof_budgets key timeout;
            verdict
      in
      verdict = Yes
    else
    let builder = Rewrite_proof.create lhs in
    List.iter
      (fun (left, right) ->
        Rewrite_proof.record builder ~pass:candidate.Normalization.pass left right)
      candidate.equalities;
    List.iter
      (fun (left, right) ->
        Rewrite_proof.record_ring builder ~pass:candidate.pass left right)
      candidate.ring_equalities;
    List.iter
      (fun (left, right) ->
        Rewrite_proof.record_poly builder ~pass:candidate.pass left right)
      candidate.poly_equalities;
    if candidate.equalities = [] && candidate.ring_equalities = []
       && candidate.poly_equalities = [] then
      Rewrite_proof.record builder ~pass:candidate.pass lhs rhs;
    let certificate = Rewrite_proof.finish builder rhs in
      let report =
        Rewrite_proof.verify ~timeouts:[ timeout ]
          ~original:lhs ~candidate:rhs certificate
      in
      Yojson.Basic.Util.member "verification" report
      = `String "proved_compositional"

let rebuild graph =
  let changed = ref false in
  let rec round () =
    let index = Hashtbl.create (graph.count * 2 + 1) in
    let merged = ref false in
    for id = 0 to graph.count - 1 do
      let enode = node graph id in
      let shape = canonical_shape graph enode.shape in
      let key = enode.width, shape in
      match Hashtbl.find_opt index key with
      | None -> Hashtbl.add index key id
      | Some previous ->
          if union graph previous id Congruence then (
            merged := true;
            changed := true)
    done;
    if !merged then round ()
    else (
      Hashtbl.clear graph.hashcons;
      Hashtbl.iter (fun key id -> Hashtbl.replace graph.hashcons key id) index)
  in
  round ();
  !changed

let semantic_merge ~local_deadline graph =
  let buckets = Hashtbl.create 128 in
  let changed = ref false in
  representatives graph
  |> List.iter (fun (root, ids) ->
         let id, expression = cheapest graph ids in
         let signature = !evaluator.node_to_outhash expression in
         match Hashtbl.find_opt buckets signature with
         | None -> Hashtbl.add buckets signature (root, id, expression)
         | Some (other_root, other_id, other_expression) ->
             if Unix.gettimeofday () > local_deadline then raise Egraph_budget;
             if find graph root <> find graph other_root then
               let failure_key = min root other_root, max root other_root in
               if not (Hashtbl.mem graph.semantic_failures failure_key) then (
                 let equalities, ring_equalities =
                   Option.value
                     (Normalization.minterm_ring_proof other_expression expression)
                     ~default:([ other_expression, expression ], [])
                 in
                 let candidate : Normalization.local_candidate =
                   {
                     expr = expression;
                     pass = "egraph-oes";
                     equalities;
                     ring_equalities;
                     poly_equalities = [];
                     allow_equal_cost = true;
                   }
                 in
                 if verify_local ~local_deadline candidate other_expression expression
                    && union graph other_id id
                         (Proof
                            {
                              lhs = other_expression;
                              rhs = expression;
                              smt_edges = equalities;
                              ring_edges = ring_equalities;
                              poly_edges = [];
                              pass = candidate.pass;
                            })
                 then changed := true
                 else Hashtbl.replace graph.semantic_failures failure_key ()));
  !changed

let compute_best graph =
  let best : (int * int * E.t) option array = Array.make graph.limit None in
  let changed = ref true and rounds = ref 0 in
  while !changed && !rounds <= graph.count do
    incr rounds;
    changed := false;
    let child id = best.(find graph id) in
    representatives graph
    |> List.iter (fun (root, ids) ->
           List.iter
             (fun id ->
               let enode = node graph id in
               let candidate =
                 match enode.shape with
                 | Var _ | Cst _ -> Some (1, 1, enode.expr)
                 | Unary (op, x) ->
                     Option.map
                       (fun (cost, nodes, expression) ->
                         (unary_cost !cost_model op + cost, nodes + 1,
                          E.unary op expression))
                       (child x)
                 | Binary (op, x, y) ->
                     Option.bind (child x) (fun (left_cost, left_nodes, left) ->
                         Option.map
                           (fun (right_cost, right_nodes, right) ->
                             (binary_cost !cost_model op + left_cost + right_cost,
                              left_nodes + right_nodes + 1,
                              E.binary op left right))
                           (child y))
                 | Ite (c, t, e) ->
                     Option.bind (child c) (fun (condition_cost, condition_nodes, condition) ->
                         Option.bind (child t) (fun (yes_cost, yes_nodes, yes) ->
                             Option.map
                               (fun (no_cost, no_nodes, no) ->
                                 (conditional_cost !cost_model + condition_cost
                                  + yes_cost + no_cost,
                                  condition_nodes + yes_nodes + no_nodes + 1,
                                  E.ite condition yes no))
                               (child e)))
               in
               Option.iter
                 (fun ((cost, nodes, expression) as value) ->
                   match best.(root) with
                   | None -> best.(root) <- Some value; changed := true
                   | Some (previous_cost, previous_nodes, previous) ->
                       if cost < previous_cost
                          || (cost = previous_cost && nodes < previous_nodes)
                          || (cost = previous_cost && nodes = previous_nodes
                              && E.compare expression previous < 0)
                       then (best.(root) <- Some value; changed := true))
                 candidate)
             ids)
  done;
  best

let extract graph root =
  let best = compute_best graph in
  match best.(find graph root) with
  | Some (_, _, expression) -> expression
  | None -> (node graph root).expr

let rec additive_terms = function
  | E.Unary { f = E.Minus; x; _ } -> additive_terms x
  | E.Binary { f = (E.Plus | E.Minus); x; y; _ } ->
      additive_terms x + additive_terms y
  | _ -> 1

let is_additive_expression = function
  | E.Unary { f = E.Minus; _ }
  | E.Binary { f = (E.Plus | E.Minus); _ } -> true
  | _ -> false

let interior_additive_classes graph best graph_root =
  let referenced = Array.make graph.limit false
  and additive_only = Array.make graph.limit true in
  for id = 0 to graph.count - 1 do
    let enode = node graph id in
    List.iteri
      (fun index child ->
        let spine_parent =
          match enode.shape with
          | Unary (E.Minus, _) -> true
          | Binary ((E.Plus | E.Minus), _, _) -> index = 0
          | _ -> false
        in
        let child_root = find graph child in
        referenced.(child_root) <- true;
        if not spine_parent then additive_only.(child_root) <- false)
      enode.raw_children
  done;
  let representatives = representatives graph in
  let long_spine = Array.make graph.limit false in
  List.iter
    (fun (root, _) ->
      let expression =
        match best.(root) with
        | Some (_, _, expression) -> expression
        | None -> (node graph root).expr
      in
      long_spine.(root) <-
        is_additive_expression expression && additive_terms expression >= 8)
    representatives;
  let changed = ref true in
  while !changed do
    changed := false;
    for id = 0 to graph.count - 1 do
      let enode = node graph id in
      if long_spine.(find graph id) then
        match enode.shape with
        | Unary (E.Minus, child) ->
            let child = find graph child in
            if not long_spine.(child) then (long_spine.(child) <- true; changed := true)
        | Binary ((E.Plus | E.Minus), left, _) ->
            let left = find graph left in
            if not long_spine.(left) then (long_spine.(left) <- true; changed := true)
        | _ -> ()
    done
  done;
  let interior = Array.make graph.limit false in
  List.iter
    (fun (root, _) ->
      let expression =
        match best.(root) with
        | Some (_, _, expression) -> expression
        | None -> (node graph root).expr
      in
      interior.(root) <-
        root <> graph_root && referenced.(root) && additive_only.(root)
        && long_spine.(root) && is_additive_expression expression)
    representatives;
  interior

let emit_minimal_proofs graph original target =
  let visited = Hashtbl.create 64 and emitted = Hashtbl.create 64 in
  let rec emit_equiv source destination =
    let pair = min source destination, max source destination in
    if source = destination || Hashtbl.mem visited pair then ()
    else (
      Hashtbl.add visited pair ();
      let queue = Queue.create () in
      let previous = Hashtbl.create 32 in
      Queue.add source queue;
      Hashtbl.add previous source None;
      while not (Queue.is_empty queue) && not (Hashtbl.mem previous destination) do
        let current = Queue.take queue in
        Option.value (Hashtbl.find_opt graph.proof_adj current) ~default:[]
        |> List.iter (fun (next, justification) ->
               if not (Hashtbl.mem previous next) then (
                 Hashtbl.add previous next (Some (current, justification));
                 Queue.add next queue))
      done;
      let rec path current result =
        if current = source then result
        else
          match Hashtbl.find_opt previous current with
          | Some (Some (parent, justification)) ->
              path parent ((parent, current, justification) :: result)
          | _ -> []
      in
      path destination []
      |> List.iter (fun (left, right, justification) ->
             match justification with
             | Proof proof ->
                 let edge_key = min left right, max left right in
                 if not (Hashtbl.mem emitted edge_key) then (
                   Hashtbl.add emitted edge_key ();
                   Option.iter
                     (fun journal ->
                       List.iter
                         (fun (lhs, rhs) ->
                           Rewrite_proof.record journal ~pass:proof.pass lhs rhs)
                         proof.smt_edges;
                       List.iter
                         (fun (lhs, rhs) ->
                           Rewrite_proof.record_ring journal ~pass:proof.pass lhs rhs)
                         proof.ring_edges;
                       List.iter
                         (fun (lhs, rhs) ->
                           Rewrite_proof.record_poly journal ~pass:proof.pass lhs rhs)
                         proof.poly_edges)
                     !(Rewrite.journal))
             | Congruence ->
                 let left_children = (node graph left).raw_children
                 and right_children = (node graph right).raw_children in
                 if List.length left_children = List.length right_children then
                   List.iter2 emit_equiv left_children right_children))
  in
  emit_equiv original target

let optimize expression =
  last_enodes := 0;
  last_iterations := 0;
  last_fallback := false;
  if not !c_egraph_extraction || size_of_expr expression > !c_egraph_max_enodes then (
    last_fallback := true;
    expression)
  else
    let initial_proof = Option.map Rewrite_proof.checkpoint !(Rewrite.journal) in
    let initial_cache = Rewrite.checkpoint_caches () in
    try
      let graph = graph !c_egraph_max_enodes in
      let root = add_expr graph expression in
      let constants = Sample_evaluator.make 8 in
      let visited = Nodes.create 256 in
      let iteration = ref 0 and continue = ref true in
      let local_deadline =
        Unix.gettimeofday ()
        +. (if !g_total_timeout <= 0. then 2. else min 2. (!g_total_timeout *. 0.2))
      in
      (try
      while !continue && !iteration < !c_egraph_max_iters
            && graph.count < graph.limit - 1 && not !g_has_timedout do
        incr iteration;
        check_timeout ();
        let changed = ref false in
        let best = compute_best graph in
        let root_class = find graph root in
        let root_fast = ref false in
        (match best.(root_class) with
        | Some (_, _, root_expression) when size_of_expr root_expression <= 1024 ->
            let merge_proposal ?(deadline = local_deadline) ?(timeout_cap = 1.5) lhs
                (proposal : Normalization.local_candidate) =
              if verify_local ~timeout_cap ~local_deadline:deadline proposal
                   lhs proposal.expr then (
                let root_id = add_expr graph lhs in
                let candidate_id = add_expr graph proposal.expr in
                if union graph root_id candidate_id
                     (Proof
                        { lhs; rhs = proposal.expr;
                          smt_edges = proposal.equalities;
                          ring_edges = proposal.ring_equalities;
                          poly_edges = proposal.poly_equalities;
                          pass = proposal.pass })
                then changed := true;
                true)
              else false
            in
            if size_of_expr root_expression >= 600
               && Normalization.linear_mba_compatible root_expression then
              (match
                 Normalization.linear_candidates size_of_expr root_expression
                 |> List.sort (fun left right ->
                        Int.compare (size_of_expr left) (size_of_expr right))
               with
              | candidate :: _ ->
                  let equalities, ring_equalities =
                    Option.value
                      (Normalization.minterm_ring_proof root_expression candidate)
                      ~default:([ root_expression, candidate ], [])
                  in
                  if
                    merge_proposal
                      ~deadline:(max local_deadline (Unix.gettimeofday () +. 4.0))
                      ~timeout_cap:3.0 root_expression
                      { expr = candidate; pass = "egraph-root-linear";
                        equalities; ring_equalities; poly_equalities = [];
                        allow_equal_cost = false }
                  then root_fast := size_of_expr candidate <= 10
              | [] -> ());
            let root_bitsliced =
              if !root_fast then None
              else Normalization.bitsliced_candidate size_of_expr root_expression
            in
            let root_components =
              Normalization.component_linear_candidates size_of_expr root_expression
              |> List.sort
                   (fun (left, _, _) (right, _, _) ->
                     Int.compare (size_of_expr left) (size_of_expr right))
            in
            (match
               if root_components = []
                  && List.length (Sample_evaluator.variables_of_expr root_expression) <= 2
               then Normalization.complement_linear_candidate size_of_expr root_expression
               else None
             with
            | Some (candidate, equalities, ring_equalities)
              when Option.fold ~none:true
                     ~some:(fun bitsliced -> size_of_expr candidate < size_of_expr bitsliced)
                     root_bitsliced ->
                if
                  merge_proposal root_expression
                    { expr = candidate; pass = "egraph-root-complement-linear";
                      equalities; ring_equalities; poly_equalities = [];
                      allow_equal_cost = false }
                then (
                  root_fast := size_of_expr candidate <= 6;
                  match Normalization.factor_group_candidate size_of_expr candidate with
                  | Some (factored, equalities, ring_equalities) ->
                      if
                        merge_proposal candidate
                          { expr = factored; pass = "egraph-root-complement-factor";
                            equalities; ring_equalities; poly_equalities = [];
                            allow_equal_cost = false }
                      then root_fast := !root_fast || size_of_expr factored <= 6
                  | None -> ())
            | _ -> ());
            (match root_components with
            | (candidate, equalities, ring_equalities) :: _
              when Option.fold ~none:true
                     ~some:(fun bitsliced ->
                       size_of_expr candidate < size_of_expr bitsliced)
                     root_bitsliced ->
                if
                  merge_proposal root_expression
                    { expr = candidate; pass = "egraph-root-component";
                      equalities; ring_equalities; poly_equalities = [];
                      allow_equal_cost = false }
                then
                  (match
                     Normalization.linear_candidates size_of_expr candidate
                     |> List.sort (fun left right ->
                            Int.compare (size_of_expr left) (size_of_expr right))
                   with
                  | simplified :: _ ->
                      let equalities, ring_equalities =
                        Option.value
                          (Normalization.minterm_ring_proof candidate simplified)
                          ~default:([ candidate, simplified ], [])
                      in
                      ignore
                        (merge_proposal candidate
                           { expr = simplified; pass = "egraph-root-component-linear";
                             equalities; ring_equalities; poly_equalities = [];
                             allow_equal_cost = false })
                  | [] -> ())
            | _ -> ());
            (match root_bitsliced with
            | Some candidate ->
                let proposal : Normalization.local_candidate =
                  let equalities, ring_equalities =
                    Option.value
                      (Normalization.minterm_ring_proof root_expression candidate)
                      ~default:([ root_expression, candidate ], [])
                  in
                  { expr = candidate; pass = "egraph-root-bitsliced"; equalities;
                    ring_equalities; poly_equalities = []; allow_equal_cost = false }
                in
                if merge_proposal root_expression proposal then
                  root_fast := !root_fast || size_of_expr candidate <= 5
            | None -> ())
        | _ -> ());
        if not !root_fast then (
        let interior_additive = interior_additive_classes graph best root_class in
        representatives graph
        |> List.sort (fun (left_root, _) (right_root, _) ->
               let cost = function
                 | Some (value, _, _) -> value
                 | None -> max_int
               in
               Int.compare (cost best.(left_root)) (cost best.(right_root)))
        |> List.iter (fun (class_root, ids) ->
               if Unix.gettimeofday () > local_deadline then raise Egraph_budget;
               let fallback_id, fallback = cheapest graph ids in
               let representative =
                 match best.(class_root) with
                 | Some (_, _, expression) -> expression
                 | None -> fallback
               in
               let id =
                 if E.is_equal representative fallback then fallback_id
                 else add_expr graph representative
               in
               if size_of_expr representative > 1
                  && not (Nodes.mem visited representative) then (
                 Nodes.add visited representative ();
                 let candidates =
                   Normalization.local_candidates ~cost:size_of_expr ~constants
                     ~heavy_additive:(not interior_additive.(class_root))
                     ~ac:!c_ac_normalization representative
                   |> List.filter (fun (candidate : Normalization.local_candidate) ->
                          !cost_model <> Legacy || size_of_expr expression <= 20
                          || not
                               (List.mem candidate.pass
                                  [ "bridge-shift"; "bridge-add"; "bridge-mul";
                                    "expand-distribute"; "expand-negation" ]))
                   |> List.sort (fun (left : Normalization.local_candidate) right ->
                          let order = Int.compare (size_of_expr left.expr) (size_of_expr right.expr) in
                          if order <> 0 then order
                          else Bool.compare left.allow_equal_cost right.allow_equal_cost)
                 in
                 let accepted_passes = Hashtbl.create 8 in
                 let accepted_nonmono_passes = Hashtbl.create 3 in
                 let rec process = function
                   | [] -> ()
                   | (candidate : Normalization.local_candidate) :: rest ->
                       if Unix.gettimeofday () > local_deadline then raise Egraph_budget;
                       let strictly_cheaper =
                         size_of_expr candidate.expr < size_of_expr representative
                       in
                       if (strictly_cheaper && Hashtbl.mem accepted_passes candidate.pass)
                          || (candidate.allow_equal_cost
                              && (Hashtbl.mem accepted_nonmono_passes candidate.pass
                                  || Hashtbl.length accepted_nonmono_passes >= 3))
                       then process rest
                       else if graph.count < graph.limit
                               && (candidate.allow_equal_cost || strictly_cheaper)
                               && verify_local ~local_deadline candidate representative candidate.expr
                       then (
                         let candidate_id = add_expr graph candidate.expr in
                         let merged =
                           union graph id candidate_id
                             (Proof
                                {
                                  lhs = representative;
                                  rhs = candidate.expr;
                                  smt_edges = candidate.equalities;
                                  ring_edges = candidate.ring_equalities;
                                  poly_edges = candidate.poly_equalities;
                                  pass = candidate.pass;
                                })
                         in
                         if merged then changed := true;
                         if strictly_cheaper then Hashtbl.replace accepted_passes candidate.pass ();
                         if candidate.allow_equal_cost then
                           Hashtbl.replace accepted_nonmono_passes candidate.pass ();
                         process rest)
                       else process rest
                 in
                 process candidates));
        if semantic_merge ~local_deadline graph then changed := true;
        if rebuild graph then changed := true);
        if !root_fast then continue := false;
        let root_class = find graph root in
        let root_best =
          match (compute_best graph).(root_class) with
          | Some (_, _, expression) -> expression
          | None -> (node graph root).expr
        in
        if not !changed || size_of_expr root_best <= 1 then continue := false
      done
      with
      | Timeout_exception -> g_has_timedout := true
      | Egraph_budget | Full -> continue := false);
      last_enodes := graph.count;
      last_iterations := !iteration;
      let result = extract graph root in
      let result_id = add_expr graph result in
      ignore (rebuild graph);
      emit_minimal_proofs graph root result_id;
      let replayable =
        match !(Rewrite.journal) with
        | None -> true
        | Some builder -> Rewrite_proof.is_connected builder result
      in
      if replayable then (
        Rewrite.restore_caches initial_cache;
        result)
      else (
        (match !(Rewrite.journal), initial_proof with
        | Some builder, Some checkpoint -> Rewrite_proof.restore builder checkpoint
        | _ -> ());
        Rewrite.restore_caches initial_cache;
        last_fallback := true;
        expression)
    with Full | Egraph_budget ->
      (match !(Rewrite.journal), initial_proof with
      | Some builder, Some checkpoint -> Rewrite_proof.restore builder checkpoint
      | _ -> ());
      Rewrite.restore_caches initial_cache;
      last_fallback := true;
      expression
