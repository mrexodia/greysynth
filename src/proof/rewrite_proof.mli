(** Independent replay of finite, unconditional bit-vector rewrite equalities.
    Producer counters and asserted verdicts are never trusted. *)

type builder
type checkpoint
val create : Sexpr.Expr.t -> builder
val checkpoint : builder -> checkpoint
val restore : builder -> checkpoint -> unit
(** Snapshot/restore equality obligations while sharing harmless interned terms. *)

val record : builder -> pass:string -> Sexpr.Expr.t -> Sexpr.Expr.t -> unit
(** Record a concrete equality. Extra unused equalities are allowed; the
    verifier must derive the externally supplied final endpoints. *)

val record_ring : builder -> pass:string -> Sexpr.Expr.t -> Sexpr.Expr.t -> unit
(** [record_ring] requests exact formal commutative-ring normalization modulo
    the common bit width. Non-ring subterms are opaque indeterminates. *)

val finish : builder -> Sexpr.Expr.t -> Yojson.Basic.t

val prove_equality_with_model : timeout:float -> Sexpr.Expr.t -> Sexpr.Expr.t ->
  Greysynth_utils.Utils.equiv_t * string * (string * Z.t) list option
(** As {!prove_equality}, retaining a concrete counterexample when refuted. *)

val prove_equality : timeout:float -> Sexpr.Expr.t -> Sexpr.Expr.t ->
  Greysynth_utils.Utils.equiv_t * string
(** Try a universally quantified abstraction of identical shared subterms,
    then the original obligation using the remaining budget. SAT on the
    abstraction is never reported as a concrete counterexample. *)

val verify : ?timeouts:float list -> original:Sexpr.Expr.t ->
  candidate:Sexpr.Expr.t -> Yojson.Basic.t -> Yojson.Basic.t
(** Validate and bind the typed DAG to [original]/[candidate], freshly prove
    the provided equalities, and compute congruence closure. An incomplete
    derivation or inconclusive SMT query never establishes equivalence.
    [timeouts] defaults to [1.] and may request larger retries for unresolved
    obligations. A refuted local edge is an invalid certificate, not a
    counterexample to whole-program equivalence. *)
