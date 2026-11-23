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

type enode = { id : int; width : int; shape : shape; expr : E.t }

type proof = {
  lhs : E.t;
  rhs : E.t;
  smt_edges : (E.t * E.t) list;
  ring_edges : (E.t * E.t) list;
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

let add_expr graph expression =
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
        let shape = canonical_shape graph shape in
        let key = E.sizeof expression, shape in
        match Hashtbl.find_opt graph.hashcons key with
        | Some id ->
            Nodes.add graph.expressions expression id;
            id
        | None ->
            if graph.count >= graph.limit then raise Full;
            let id = graph.count in
            graph.count <- graph.count + 1;
            let enode = { id; width = E.sizeof expression; shape; expr = expression } in
            graph.enodes.(id) <- Some enode;
            graph.parent.(id) <- id;
            Hashtbl.add graph.classes id [ id ];
            Hashtbl.add graph.hashcons key id;
            Nodes.add graph.expressions expression id;
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

let verify_local candidate lhs rhs =
  if not (Rewrite.samples_agree lhs rhs) then false
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
    if candidate.equalities = [] && candidate.ring_equalities = [] then
      Rewrite_proof.record builder ~pass:candidate.pass lhs rhs;
    let certificate = Rewrite_proof.finish builder rhs in
    let report =
      Rewrite_proof.verify ~timeouts:[ float_of_int !c_equiv_timeout ]
        ~original:lhs ~candidate:rhs certificate
    in
    Yojson.Basic.Util.member "verification" report = `String "proved_compositional"

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
    if !merged then round () else graph.hashcons |> Hashtbl.clear;
    Hashtbl.iter (fun key id -> Hashtbl.replace graph.hashcons key id) index
  in
  round ();
  !changed

let semantic_merge graph =
  let buckets = Hashtbl.create 128 in
  let changed = ref false in
  representatives graph
  |> List.iter (fun (root, ids) ->
         let id, expression = cheapest graph ids in
         let signature = !evaluator.node_to_outhash expression in
         match Hashtbl.find_opt buckets signature with
         | None -> Hashtbl.add buckets signature (root, id, expression)
         | Some (other_root, other_id, other_expression) ->
             if find graph root <> find graph other_root then
               let candidate : Normalization.local_candidate =
                 {
                   expr = expression;
                   pass = "egraph-oes";
                   equalities = [ other_expression, expression ];
                   ring_equalities = [];
                   allow_equal_cost = true;
                 }
               in
               if verify_local candidate other_expression expression
                  && union graph other_id id
                       (Proof
                          {
                            lhs = other_expression;
                            rhs = expression;
                            smt_edges = candidate.equalities;
                            ring_edges = [];
                            pass = candidate.pass;
                          })
               then changed := true);
  !changed

let extract graph root =
  let best : (int * E.t) option array = Array.make graph.limit None in
  let build shape =
    let child id =
      match best.(find graph id) with Some (_, expression) -> Some expression | None -> None
    in
    match shape with
    | Var _ | Cst _ -> None
    | Unary (op, x) -> Option.map (E.unary op) (child x)
    | Binary (op, x, y) ->
        Option.bind (child x) (fun x -> Option.map (fun y -> E.binary op x y) (child y))
    | Ite (c, t, e) ->
        Option.bind (child c) (fun c ->
            Option.bind (child t) (fun t -> Option.map (fun e -> E.ite c t e) (child e)))
  in
  for _ = 0 to graph.count do
    representatives graph
    |> List.iter (fun (root, ids) ->
           List.iter
             (fun id ->
               let enode = node graph id in
               let candidate =
                 match enode.shape with
                 | Var _ | Cst _ -> Some enode.expr
                 | shape -> build shape
               in
               Option.iter
                 (fun expression ->
                   let cost = size_of_expr expression in
                   match best.(root) with
                   | None -> best.(root) <- Some (cost, expression)
                   | Some (previous_cost, previous) ->
                       if cost < previous_cost
                          || (cost = previous_cost && E.compare expression previous < 0)
                       then best.(root) <- Some (cost, expression))
                 candidate)
             ids)
  done;
  match best.(find graph root) with Some (_, expression) -> expression | None -> (node graph root).expr

let emit_component_proofs graph root =
  let root = find graph root in
  let emitted = Hashtbl.create 64 in
  for id = 0 to graph.count - 1 do
    if find graph id = root then
      Option.value (Hashtbl.find_opt graph.proof_adj id) ~default:[]
      |> List.iter (fun (other, justification) ->
             let key = min id other, max id other in
             if not (Hashtbl.mem emitted key) then (
               Hashtbl.add emitted key ();
               match justification with
               | Congruence -> ()
               | Proof proof ->
                   Option.iter
                     (fun journal ->
                       List.iter
                         (fun (left, right) ->
                           Rewrite_proof.record journal ~pass:proof.pass left right)
                         proof.smt_edges;
                       List.iter
                         (fun (left, right) ->
                           Rewrite_proof.record_ring journal ~pass:proof.pass left right)
                         proof.ring_edges)
                     !(Rewrite.journal)))
  done

let optimize expression =
  last_enodes := 0;
  last_iterations := 0;
  last_fallback := false;
  if not !c_egraph_extraction || size_of_expr expression > !c_egraph_max_enodes then (
    last_fallback := true;
    expression)
  else
    try
      let graph = graph !c_egraph_max_enodes in
      let root = add_expr graph expression in
      let constants = Sample_evaluator.make 8 in
      let visited = Nodes.create 256 in
      let iteration = ref 0 and continue = ref true in
      while !continue && !iteration < !c_egraph_max_iters
            && graph.count < graph.limit && not !g_has_timedout do
        incr iteration;
        check_timeout ();
        let changed = ref false in
        representatives graph
        |> List.sort (fun (left_root, left_ids) (right_root, right_ids) ->
               let root_class = find graph root in
               if left_root = root_class then -1
               else if right_root = root_class then 1
               else
                 let _, left = cheapest graph left_ids
                 and _, right = cheapest graph right_ids in
                 Int.compare (size_of_expr right) (size_of_expr left))
        |> List.iter (fun (_root, ids) ->
               let id, representative = cheapest graph ids in
               if not (Nodes.mem visited representative) then (
                 Nodes.add visited representative ();
                 Normalization.local_candidates ~cost:size_of_expr ~constants
                   ~ac:!c_ac_normalization representative
                 |> List.iter (fun (candidate : Normalization.local_candidate) ->
                        if graph.count < graph.limit
                           && (candidate.allow_equal_cost
                               || size_of_expr candidate.expr < size_of_expr representative)
                           && verify_local candidate representative candidate.expr
                        then
                          let candidate_id = add_expr graph candidate.expr in
                          if union graph id candidate_id
                               (Proof
                                  {
                                    lhs = representative;
                                    rhs = candidate.expr;
                                    smt_edges = candidate.equalities;
                                    ring_edges = candidate.ring_equalities;
                                    pass = candidate.pass;
                                  })
                          then changed := true)));
        if semantic_merge graph then changed := true;
        if rebuild graph then changed := true;
        let _, root_best =
          let root_class = find graph root in
          cheapest graph (Option.value (Hashtbl.find_opt graph.classes root_class) ~default:[ root ])
        in
        if not !changed || size_of_expr root_best <= 5 then continue := false
      done;
      last_enodes := graph.count;
      last_iterations := !iteration;
      let result = extract graph root in
      let result_id = add_expr graph result in
      ignore (rebuild graph);
      emit_component_proofs graph root;
      ignore result_id;
      result
    with Full ->
      last_fallback := true;
      expression
