type t = { width : int; zeros : Z.t; ones : Z.t }

val analyze : Sexpr.Expr.t -> t
(** Sound DAG-memoized forward known-zero/known-one analysis. *)

val is_constant : t -> Z.t option
val possible_ones : t -> Z.t
val disjoint : t -> t -> bool
