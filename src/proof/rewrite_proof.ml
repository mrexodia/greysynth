(* A proof certificate contains typed terms and equality obligations, not
   trusted verdicts. Replay rechecks obligations and derives endpoint equality
   by congruence closure. It does not import producer caches or sample banks. *)
module E = Sexpr.Expr
module U = Greysynth_utils.Utils
module J = Yojson.Basic.Util

type shape =
  | Variable of string
  | Value of string
  | Unary of string * int list * int
  | Binary of string * int * int
  | Conditional of int * int * int

type node = { width : int; shape : shape; expr : E.t; cost : int }
type graph = {
  mutable nodes : node array;
  mutable count : int;
  intern : (int * shape, int) Hashtbl.t;
  expressions : (E.t, int) Hashtbl.t;
}
type proof_rule = Smt | Ring_mod2w
type edge = { left : int; right : int; pass : string; rule : proof_rule }
type builder = {
  graph : graph;
  original : int;
  mutable edges : edge list;
  edge_set : (int * int, unit) Hashtbl.t;
}
type checkpoint = edge list

let format = "greysynth.rewrite-proof.v1"
let semantics = "smtlib-fixed-bitvectors-srem-v1"
let max_nodes = 200_000
let max_width = 65_536
let fail message = failwith ("invalid_certificate: " ^ message)
let dummy =
  { width = 1; shape = Value "0";
    expr = E.constant (Bitvector.of_int ~size:1 0); cost = 1 }
let graph () =
  { nodes = Array.make 128 dummy; count = 0; intern = Hashtbl.create 128;
    expressions = Hashtbl.create 128 }
let children = function
  | Variable _ | Value _ -> []
  | Unary (_, _, x) -> [x]
  | Binary (_, x, y) -> [x; y]
  | Conditional (c, t, e) -> [c; t; e]
let node g id =
  if id < 0 || id >= g.count then fail "term reference out of range";
  g.nodes.(id)

let binary_op = function
  | "bvadd" -> E.Plus | "bvsub" -> E.Minus | "bvmul" -> E.Mul
  | "bvudiv" -> E.Udiv | "bvsdiv" -> E.Sdiv
  | "bvurem" -> E.Umod | "bvsrem" -> E.Smod
  | "bvand" -> E.And | "bvor" -> E.Or | "bvxor" -> E.Xor
  | "bvshl" -> E.Lsl | "bvlshr" -> E.Lsr | "bvashr" -> E.Asr
  | "rotate_left" -> E.Rol | "rotate_right" -> E.Ror
  | "concat" -> E.Concat | "eq" -> E.Eq | "distinct" -> E.Diff
  | "bvule" -> E.Ule | "bvult" -> E.Ult | "bvuge" -> E.Uge | "bvugt" -> E.Ugt
  | "bvsle" -> E.Sle | "bvslt" -> E.Slt | "bvsge" -> E.Sge | "bvsgt" -> E.Sgt
  | _ -> fail "unknown binary operator"
let binary_name = function
  | E.Plus -> "bvadd" | E.Minus -> "bvsub" | E.Mul -> "bvmul"
  | E.Udiv -> "bvudiv" | E.Sdiv -> "bvsdiv"
  | E.Umod -> "bvurem" | E.Smod -> "bvsrem"
  | E.And -> "bvand" | E.Or -> "bvor" | E.Xor -> "bvxor"
  | E.Lsl -> "bvshl" | E.Lsr -> "bvlshr" | E.Asr -> "bvashr"
  | E.Rol -> "rotate_left" | E.Ror -> "rotate_right"
  | E.Concat -> "concat" | E.Eq -> "eq" | E.Diff -> "distinct"
  | E.Ule -> "bvule" | E.Ult -> "bvult" | E.Uge -> "bvuge" | E.Ugt -> "bvugt"
  | E.Sle -> "bvsle" | E.Slt -> "bvslt" | E.Sge -> "bvsge" | E.Sgt -> "bvsgt"
let unary_op name parameters =
  match name, parameters with
  | "bvnot", [] -> E.Not | "bvneg", [] -> E.Minus
  | "zero_extend", [n] when n >= 0 -> E.Uext n
  | "sign_extend", [n] when n >= 0 -> E.Sext n
  | "extract", [lo; hi] when lo >= 0 && hi >= lo -> E.Restrict {lo; hi}
  | _ -> fail "invalid unary operator or parameters"

(* Intern complete immutable typed descriptors. Hashes are only bucket indexes;
   equality never relies on a truncated or producer-supplied hash value. *)
let intern g width shape =
  if width <= 0 || width > max_width then fail "unsupported bit width";
  let child_ids = children shape in
  List.iter (fun id -> ignore (node g id)) child_ids;
  let expr =
    match shape with
    | Variable name -> E.var name width name
    | Value value ->
        let z = Z.of_string value in
        if Z.sign z < 0 || Z.numbits z > width then fail "constant outside its width";
        E.constant (Bitvector.create z width)
    | Unary (op, parameters, child) ->
        let child = node g child in
        let operator = unary_op op parameters in
        (match operator with
        | E.Uext n | E.Sext n when n > max_width - child.width ->
            fail "extension width overflow"
        | E.Restrict { hi; _ } when hi >= child.width ->
            fail "restriction outside operand width"
        | _ -> ());
        E.unary operator child.expr
    | Binary (op, left, right) ->
        let left = node g left and right = node g right in
        if op <> "concat" && left.width <> right.width then
          fail "binary operands have different widths";
        if op = "concat" && left.width > max_width - right.width then
          fail "concatenation width overflow";
        E.binary (binary_op op) left.expr right.expr
    | Conditional (condition, yes, no) ->
        let condition = node g condition and yes = node g yes and no = node g no in
        if condition.width <> 1 || yes.width <> no.width then
          fail "ill-typed conditional";
        E.ite condition.expr yes.expr no.expr
  in
  if E.sizeof expr <> width then fail "declared term width is incorrect";
  let shape = match shape with
    | Value value -> Value (Z.to_string (Z.of_string value))
    | shape -> shape
  in
  match Hashtbl.find_opt g.intern (width, shape) with
  | Some id -> id
  | None ->
      if g.count >= max_nodes then fail "certificate term limit exceeded";
      if g.count = Array.length g.nodes then (
        let larger = Array.make (2 * g.count) dummy in
        Array.blit g.nodes 0 larger 0 g.count;
        g.nodes <- larger);
      let cost = List.fold_left
        (fun sum id -> min 1_000_000 (sum + (node g id).cost)) 1 child_ids in
      let id = g.count in
      g.nodes.(id) <- {width; shape; expr; cost};
      g.count <- id + 1;
      Hashtbl.add g.intern (width, shape) id;
      id

let rec of_expr g expression =
  match Hashtbl.find_opt g.expressions expression with
  | Some id -> id
  | None ->
      let shape = match expression with
        | E.Var v -> Variable v.name
        | E.Cst value -> Value (Z.to_string (Bitvector.value_of value))
        | E.Unary {f; x; _} ->
            let op, parameters = match f with
              | E.Not -> "bvnot", [] | E.Minus -> "bvneg", []
              | E.Uext n -> "zero_extend", [n] | E.Sext n -> "sign_extend", [n]
              | E.Restrict {lo; hi} -> "extract", [lo; hi]
            in
            Unary (op, parameters, of_expr g x)
        | E.Binary {f; x; y; _} ->
            let x = of_expr g x in
            let y = of_expr g y in
            Binary (binary_name f, x, y)
        | E.Ite {c; t; e; _} ->
            let c = of_expr g c in
            let t = of_expr g t in
            let e = of_expr g e in
            Conditional (c, t, e)
        | E.Load _ -> fail "memory loads are outside the proof semantics"
      in
      let id = intern g (E.sizeof expression) shape in
      Hashtbl.add g.expressions expression id;
      id

let create original =
  let graph = graph () in
  let original = of_expr graph original in
  { graph; original; edges = []; edge_set = Hashtbl.create 64 }
let checkpoint builder = builder.edges

let restore builder edges =
  builder.edges <- edges;
  Hashtbl.clear builder.edge_set;
  List.iter
    (fun edge ->
      Hashtbl.replace builder.edge_set
        (min edge.left edge.right, max edge.left edge.right) ())
    edges

let record_with_rule builder ~pass ~rule left right =
  let left = of_expr builder.graph left in
  let right = of_expr builder.graph right in
  if (node builder.graph left).width <> (node builder.graph right).width then
    fail "equality changes result width";
  let key = min left right, max left right in
  if left <> right && not (Hashtbl.mem builder.edge_set key) then (
    Hashtbl.add builder.edge_set key ();
    builder.edges <- { left; right; pass; rule } :: builder.edges)

let record builder ~pass left right =
  record_with_rule builder ~pass ~rule:Smt left right

let record_ring builder ~pass left right =
  record_with_rule builder ~pass ~rule:Ring_mod2w left right

let ints xs = `List (List.map (fun x -> `Int x) xs)
let node_json node =
  let fields = match node.shape with
    | Variable name -> ["op", `String "var"; "name", `String name]
    | Value value -> ["op", `String "const"; "value", `String value]
    | Unary (op, parameters, x) ->
        ["op", `String op; "parameters", ints parameters; "args", ints [x]]
    | Binary (op, x, y) -> ["op", `String op; "args", ints [x; y]]
    | Conditional (c, t, e) -> ["op", `String "ite"; "args", ints [c; t; e]]
  in
  `Assoc (("width", `Int node.width) :: fields)
let finish builder candidate =
  let candidate = of_expr builder.graph candidate in
  `Assoc [
    "format", `String format;
    "semantics", `String semantics;
    "input", `Int builder.original;
    "output", `Int candidate;
    "nodes", `List (List.init builder.graph.count
      (fun id -> node_json (node builder.graph id)));
    "equalities", `List (List.rev_map (fun edge -> `Assoc [
      "lhs", `Int edge.left; "rhs", `Int edge.right;
      "pass", `String edge.pass;
      "rule", `String (match edge.rule with Smt -> "smt" | Ring_mod2w -> "ring_mod2w")
    ]) builder.edges);
  ]

(* Replace repeated complex subterms consistently by fresh typed variables.
   This discards constraints and therefore makes the equality STRONGER. An
   UNSAT result implies the original by substitution. SAT does not refute it. *)
let abstract_pair original candidate =
  let g = graph () in
  let left = of_expr g original in
  let right = of_expr g candidate in
  let occurs_left = Array.make g.count false in
  let occurs_right = Array.make g.count false in
  let rec mark occurrences id =
    if not occurrences.(id) then (
      occurrences.(id) <- true;
      List.iter (mark occurrences) (children (node g id).shape))
  in
  mark occurs_left left;
  mark occurs_right right;
  let names = Hashtbl.create 16 in
  for id = 0 to g.count - 1 do
    match (node g id).shape with
    | Variable name -> Hashtbl.replace names name ()
    | _ -> ()
  done;
  let replacements = Hashtbl.create 16 and rebuilt = Hashtbl.create 64 in
  let serial = ref 0 in
  let rec fresh () =
    let name = Printf.sprintf "$greysynth.proof.%d" !serial in
    incr serial;
    if Hashtbl.mem names name then fresh ()
    else (Hashtbl.add names name (); name)
  in
  let rec visit id =
    match Hashtbl.find_opt rebuilt id with
    | Some expression -> expression
    | None ->
        let current = node g id in
        let expression =
          let nontrivial_constant =
            match current.expr with
            | E.Cst value ->
                not (Bitvector.is_zeros value
                     || Bitvector.is_ones value
                     || Bitvector.is_fill value)
            | _ -> false
          in
          if occurs_left.(id) && occurs_right.(id)
             && (current.cost >= 2 || nontrivial_constant) then (
            match Hashtbl.find_opt replacements id with
            | Some expression -> expression
            | None ->
                let name = fresh () in
                let expression = E.var name current.width name in
                Hashtbl.add replacements id expression;
                expression)
          else match current.shape with
            | Variable _ | Value _ -> current.expr
            | Unary (op, parameters, x) -> E.unary (unary_op op parameters) (visit x)
            | Binary (op, x, y) -> E.binary (binary_op op) (visit x) (visit y)
            | Conditional (c, t, e) -> E.ite (visit c) (visit t) (visit e)
        in
        Hashtbl.add rebuilt id expression;
        expression
  in
  let left = visit left in
  let right = visit right in
  if Hashtbl.length replacements = 0 then None else Some (left, right)

let prove_equality_with_model ~timeout original candidate =
  if E.is_equal original candidate then U.Yes, "reflexive", None
  else if not (Float.is_finite timeout) || timeout <= 0. then
    U.Timeout, "budget", None
  else
    let deadline = Unix.gettimeofday () +. timeout in
    let solve ?(limit = infinity) ?(model = false) left right =
      let remaining = min limit (deadline -. Unix.gettimeofday ()) in
      if remaining <= 0. then U.Timeout, None
      else
        let verdict, _, counterexample =
          U.are_equivalent_seconds ~show_counter_example:model left right
            (Some remaining)
        in
        verdict, counterexample
    in
    let generalized =
      try
        match abstract_pair original candidate with
        | None -> None
        | Some (left, right) ->
            (* Reserve most of the budget for concrete fallback. Larger retry
               budgets may spend up to one second on the stronger query. *)
            Some (solve ~limit:(min 1. (timeout *. 0.25)) left right)
      with _ -> None
    in
    match generalized with
    | Some (U.Yes, _) -> U.Yes, "abstract", None
    | _ ->
        let verdict, model = solve ~model:true original candidate in
        verdict, "concrete", model

let prove_equality ~timeout original candidate =
  let verdict, method_, _ = prove_equality_with_model ~timeout original candidate in
  verdict, method_

let load certificate =
  if J.to_string (J.member "format" certificate) <> format then fail "unknown format";
  if J.to_string (J.member "semantics" certificate) <> semantics then fail "unknown semantics";
  let encoded = J.to_list (J.member "nodes" certificate) in
  if List.length encoded > max_nodes then fail "certificate term limit exceeded";
  let g = graph () in
  let mapping = Array.make (List.length encoded) (-1) in
  List.iteri (fun index json ->
    let width = J.to_int (J.member "width" json) in
    let op = J.to_string (J.member "op" json) in
    let args = match J.member "args" json with
      | `Null -> []
      | value -> J.to_list value |> List.map (fun arg ->
          let id = J.to_int arg in
          if id < 0 || id >= index then fail "terms must be topologically ordered";
          mapping.(id))
    in
    let parameters = match J.member "parameters" json with
      | `Null -> [] | value -> J.to_list value |> List.map J.to_int
    in
    let shape = match op, args, parameters with
      | "var", [], [] -> Variable (J.to_string (J.member "name" json))
      | "const", [], [] -> Value (J.to_string (J.member "value" json))
      | "ite", [c; t; e], [] -> Conditional (c, t, e)
      | ("bvnot" | "bvneg" | "zero_extend" | "sign_extend" | "extract"), [x], p ->
          Unary (op, p, x)
      | _, [x; y], [] -> ignore (binary_op op); Binary (op, x, y)
      | _ -> fail "invalid operator arity"
    in
    mapping.(index) <- intern g width shape) encoded;
  let reference value =
    let id = J.to_int value in
    if id < 0 || id >= Array.length mapping then fail "root or equality reference out of range";
    mapping.(id)
  in
  let original = reference (J.member "input" certificate) in
  let candidate = reference (J.member "output" certificate) in
  let encoded_edges = J.to_list (J.member "equalities" certificate) in
  if List.length encoded_edges > max_nodes then fail "certificate equality limit exceeded";
  let edges = List.map (fun json ->
    let left = reference (J.member "lhs" json) in
    let right = reference (J.member "rhs" json) in
    if (node g left).width <> (node g right).width then fail "equality changes width";
    let rule =
      match J.member "rule" json with
      | `Null | `String "smt" -> Smt
      | `String "ring_mod2w" -> Ring_mod2w
      | _ -> fail "unknown equality proof rule"
    in
    { left; right; pass = "untrusted"; rule }) encoded_edges in
  g, original, candidate, edges

(* This small closure checker trusts only equality edges supplied by its caller.
   The caller passes freshly SMT-proved edges, never producer verdict fields. *)
let congruent g equalities left right =
  let parent = Array.init g.count Fun.id and ranks = Array.make g.count 0 in
  let rec find id =
    if parent.(id) = id then id
    else (parent.(id) <- find parent.(id); parent.(id))
  in
  let union left right =
    let left = find left and right = find right in
    if left = right then false
    else (
      if ranks.(left) < ranks.(right) then parent.(left) <- right
      else (
        parent.(right) <- left;
        if ranks.(left) = ranks.(right) then ranks.(left) <- ranks.(left) + 1);
      true)
  in
  List.iter (fun edge -> ignore (union edge.left edge.right)) equalities;
  let changed = ref true in
  while !changed do
    changed := false;
    let representatives = Hashtbl.create g.count in
    for id = 0 to g.count - 1 do
      let n = node g id in
      let shape = match n.shape with
        | Variable _ | Value _ -> n.shape
        | Unary (op, parameters, x) -> Unary (op, parameters, find x)
        | Binary (op, x, y) -> Binary (op, find x, find y)
        | Conditional (c, t, e) -> Conditional (find c, find t, find e)
      in
      let key = n.width, shape in
      match Hashtbl.find_opt representatives key with
      | None -> Hashtbl.add representatives key id
      | Some previous -> if union previous id then changed := true
    done
  done;
  find left = find right

module Monomial = struct
  type t = int list
  let compare = Stdlib.compare
end

module Polynomial = Map.Make (Monomial)

exception Ring_limit
type ring_verdict = Ring_equal | Ring_not_equal | Ring_limit_exceeded

let ring_equal g left right =
  let width = (node g left).width in
  if width <> (node g right).width then Ring_not_equal
  else
    let operations = ref 0 in
    let modulus = Z.shift_left Z.one width in
    let normalize value =
      let value = Z.erem value modulus in
      if Z.sign value < 0 then Z.add value modulus else value
    in
    let add_term monomial coefficient polynomial =
      incr operations;
      if !operations > 200_000 || List.length monomial > 16 then raise Ring_limit;
      let coefficient = normalize coefficient in
      let old = Option.value (Polynomial.find_opt monomial polynomial) ~default:Z.zero in
      let value = normalize (Z.add old coefficient) in
      let polynomial =
        if Z.equal value Z.zero then Polynomial.remove monomial polynomial
        else Polynomial.add monomial value polynomial
      in
      if Polynomial.cardinal polynomial > 4096 then raise Ring_limit;
      polynomial
    in
    let add left right =
      Polynomial.fold add_term left right
    in
    let neg polynomial =
      Polynomial.fold
        (fun monomial coefficient result -> add_term monomial (Z.neg coefficient) result)
        polynomial Polynomial.empty
    in
    let mul left right =
      Polynomial.fold
        (fun left_monomial left_coefficient result ->
          Polynomial.fold
            (fun right_monomial right_coefficient result ->
              add_term
                (List.sort Int.compare (left_monomial @ right_monomial))
                (Z.mul left_coefficient right_coefficient) result)
            right result)
        left Polynomial.empty
    in
    let memo = Hashtbl.create 128 in
    let rec polynomial id =
      match Hashtbl.find_opt memo id with
      | Some result -> result
      | None ->
          let current = node g id in
          let opaque () = Polynomial.singleton [ id ] Z.one in
          let result =
            match current.shape, current.expr with
            | Value _, E.Cst value ->
                add_term [] (Bitvector.value_of value) Polynomial.empty
            | Unary ("bvneg", [], x), _ -> neg (polynomial x)
            | Binary ("bvadd", x, y), _ -> add (polynomial x) (polynomial y)
            | Binary ("bvsub", x, y), _ -> add (polynomial x) (neg (polynomial y))
            | Binary ("bvmul", x, y), _ -> mul (polynomial x) (polynomial y)
            | _ -> opaque ()
          in
          Hashtbl.add memo id result;
          result
    in
    try
      if Polynomial.equal Z.equal (polynomial left) (polynomial right) then Ring_equal
      else Ring_not_equal
    with Ring_limit -> Ring_limit_exceeded

let is_connected builder candidate =
  let candidate = of_expr builder.graph candidate in
  congruent builder.graph builder.edges builder.original candidate

let verify ?(timeouts = [1.]) ~original ~candidate certificate =
  let started = Unix.gettimeofday () in
  let checked = ref 0 and proved = ref 0 and unknown = ref 0 and timed_out = ref 0 in
  let abstract = ref 0 and direct = ref 0 and ring = ref 0 in
  let ring_limits = ref 0 in
  let nodes = ref 0 and edges_count = ref 0 in
  let result verification reason = `Assoc [
    "verification", `String verification;
    "equiv", `String (if verification = "proved_compositional" then "yes" else "ukn");
    "reason", `String reason;
    "equiv_time", `Float (Unix.gettimeofday () -. started);
    "nodes", `Int !nodes; "provided_equalities", `Int !edges_count;
    "checked_equalities", `Int !checked; "proved_equalities", `Int !proved;
    "abstract_proofs", `Int !abstract; "direct_proofs", `Int !direct;
    "ring_proofs", `Int !ring; "ring_limit_equalities", `Int !ring_limits;
    "unknown_equalities", `Int !unknown; "timeout_equalities", `Int !timed_out;
  ] in
  try
    if timeouts = [] || List.exists (fun t -> not (Float.is_finite t) || t <= 0.) timeouts then
      fail "proof timeouts must be positive finite seconds";
    let g, input_id, output_id, obligations = load certificate in
    nodes := g.count; edges_count := List.length obligations;
    (* Bind outside claims before accepting even a reflexive certificate. *)
    if of_expr g original <> input_id || of_expr g candidate <> output_id then
      fail "certificate endpoints do not match the supplied expressions";
    if not (congruent g obligations input_id output_id) then
      result "unknown" "incomplete_derivation"
    else if congruent g [] input_id output_id then
      result "proved_compositional" "structural_identity"
    else (
      let established = ref [] in
      List.iter (fun edge ->
        incr checked;
        let rec attempt = function
          | [] -> U.Unknown, "budget"
          | timeout :: remaining ->
              let verdict, method_ = prove_equality ~timeout
                (node g edge.left).expr (node g edge.right).expr in
              match verdict, remaining with
              | (U.Unknown | U.Timeout), _ :: _ -> attempt remaining
              | _ -> verdict, method_
        in
        let verdict, method_ =
          match edge.rule with
          | Ring_mod2w ->
              (match ring_equal g edge.left edge.right with
              | Ring_equal -> U.Yes, "ring_mod2w"
              | Ring_not_equal -> U.No, "ring_not_equal"
              | Ring_limit_exceeded -> U.Unknown, "ring_limit_exceeded")
          | Smt -> attempt timeouts
        in
        match verdict with
        | U.Yes ->
            incr proved;
            if method_ = "abstract" then incr abstract
            else if method_ = "ring_mod2w" then incr ring
            else incr direct;
            established := edge :: !established
        | U.No ->
            fail
              (Printf.sprintf
                 "a local %s equality was refuted: %s != %s; this does not refute the final output"
                 (match edge.rule with Smt -> "smt" | Ring_mod2w -> "ring_mod2w")
                 (U.pp (node g edge.left).expr) (U.pp (node g edge.right).expr))
        | U.Timeout -> incr timed_out
        | U.Unknown | U.Disabled ->
            incr unknown;
            if method_ = "ring_limit_exceeded" then incr ring_limits) obligations;
      if congruent g !established input_id output_id then
        result "proved_compositional" "smt_equalities_and_congruence"
      else if !ring_limits > 0 then result "unknown" "ring_limit_exceeded"
      else if !timed_out > 0 && !unknown = 0 then result "timeout" "unresolved_equalities"
      else result "unknown" "unresolved_equalities")
  with exn -> result "error" (Printexc.to_string exn)
