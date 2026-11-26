(** Untrusted analytical SMIR/XSMIR candidate generation.  Every returned
    expression must still cross [Rewrite.accepts]. *)

val analytical_candidates :
  width:int -> target:Z.t array -> expression:Sexpr.Expr.t ->
  values:Z.t array -> Sexpr.Expr.t list
(** Apply exact/constant, additive, XOR, multiplicative, AND-OR mask, affine,
    quadratic, rotate and shift interpolation rules. *)

val synthesize_exact : Synth_backends.problem -> Sexpr.Expr.t option
(** Deterministically enumerate operator-stratified core trees through size five
    under a 25ms/1500-core cap and analytically elevate each one. *)
