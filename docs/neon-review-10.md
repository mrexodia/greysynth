# GreySynth Round-10 Review: Complete True Per-Eclass Milestone 4A (No More Branch Worklists)

**Reviewed commits:** `6918f30..bce1f09` (`6918f30`, `14d494c`, `205e4df`, `bce1f09`)  
**Summary:**
- `14d494c` and `6918f30` cleanly verified our smoking-gun diagnosis: removing the redundant monolithic SMT re-check eliminated the `PLDI Poly` (`0.9991x -> 0.8812x`) and `msimba` (`1.4766x -> 0.9966x`) regressions, improved `MBA-Obfuscator nonlinear` (`0.8604x`) and `QSynth EA` (`0.9653x`), and kept C-Full at **1,000/1,000 established, 984/16** (`20 better / 974 equal / 6 worse`).
- **However, for three consecutive rounds (`1a87ebe`, `715613c`, `14d494c`), `src/greysynth/egraph.ml` has remained a whole-expression branch worklist (`type branch = { expression; proof; cache }`) calling `Normalization.run` and `Oes.linear_simplify`.** Also note a minor bug in `14d494c` (`egraph.ml:108-126`): `add_candidate ~ring:true` rejects every bitwise (`And`/`Or`/`Xor`) AC canonicalization because `ring_mod2w` only covers `{+, -, neg, *}`.

This round has **one single goal**: replace the branch worklist in `src/greysynth/egraph.ml` with the actual per-eclass hash-consed e-graph and finish Milestone 4A cleanly.

---

## Hard Structural Requirements for Round 10

Do **not** iterate further on `type branch = { expression; proof; cache }`:
1. **`type branch` must be deleted from `src/greysynth/egraph.ml`.**
2. **`src/greysynth/egraph.ml` must NOT call `Normalization.run` or `Oes.linear_simplify`** anywhere (large-input fallback is already handled in `greysynth.ml` via `Egraph.fell_back ()`).
3. **Never write directly into `Rewrite.journal` during saturation** — store verified local justifications in the e-graph's spanning forest and emit ONLY the minimal BFS path edges connecting `input` to the globally extracted `output`.

---

## Step-by-Step Implementation Plan (3 Clean Atomic Commits)

### Commit 1: Expose `Normalization.local_candidates` (`src/greysynth/normalization.ml`)
Add and export a pure per-node candidate generator (no `Rewrite.journal` mutation):
```ocaml
type local_candidate = {
  expr : Sexpr.Expr.t;
  pass : string;
  equalities : (Sexpr.Expr.t * Sexpr.Expr.t) list;
  ring_equalities : (Sexpr.Expr.t * Sexpr.Expr.t) list;
  allow_equal_cost : bool;
}

val local_candidates :
  cost:(Sexpr.Expr.t -> int) ->
  constants:Sample_evaluator.t ->
  ac:bool ->
  Sexpr.Expr.t ->
  local_candidate list
```
For a single e-class representative `rep`, return:
1. `peepholes constants.eval rep` (`allow_equal_cost = false`, `equalities = [ rep, cand ]`, `ring_equalities = []`),
2. `canonical_candidates rep` when `ac = true` (`allow_equal_cost = true`; if top-level op is `Plus | Mul`, set `ring_equalities = [ rep, cand ], equalities = []`; if `And | Or | Xor`, set `equalities = [ rep, cand ], ring_equalities = []`),
3. `ring_polynomial_candidate cost rep` when `cost rep >= 5` (`ring_equalities = [ rep, cand ]`),
4. `factor_group_candidate cost rep` (returns `(cand, eqs, ring_eqs)`),
5. `minterm_polynomial_candidate cost rep` (returns `(cand, eqs, ring_eqs)`),
6. `product_partition_candidate rep` (returns `(cand, eqs)`),
7. `bitsliced_candidate cost rep` (gated on 1-var nontrivial mask, attaching `minterm_ring_proof` if available),
8. `linear_candidates cost rep` (attaching `minterm_ring_proof` or `complement_product_steps` when `Rewrite.samples_agree rep cand`).

### Commit 2: Real Per-Eclass Hash-Consed E-Graph (`src/greysynth/egraph.ml`)
Replace `src/greysynth/egraph.ml` completely with:
1. **Types & State:**
   - `shape = Var of string | Cst of Bitvector.t | Unary of E.unop * int | Binary of E.binop * int * int | Ite of int * int * int` (child IDs are canonical e-class IDs).
   - `enode = { id : int; width : int; shape : shape; expr : E.t }`.
   - `justification = Congruence | Proof of { lhs : E.t; rhs : E.t; smt_edges : (E.t * E.t) list; ring_edges : (E.t * E.t) list; pass : string }`.
   - Union-find `parent : int array`, `classes : (int, enode list) Hashtbl.t`, `hashcons : (int * shape, int) Hashtbl.t`, and undirected spanning forest `proof_adj : (int, (int * justification) list) Hashtbl.t`.
   - Default config limits restored to real e-node counts: `egraph_max_enodes = 2048`, `egraph_max_iters = 4`.
   - Fast guard: if `not !c_egraph_extraction || size_of_expr expression > !c_egraph_max_enodes`, set `last_fallback := true` and return `expression` (remove the `variable_count < 2` hack — 1-var inputs work natively through `bitsliced_candidate` / `linear_candidates`!).
2. **Pure Verification Helper (`verify_local`):**
   - Check `Rewrite.samples_agree lhs rhs`.
   - Reuse `Rewrite.proofs` cache when available (respecting budget).
   - If `ring_edges <> []` or `List.length smt_edges > 1`, verify via local `Rewrite_proof.create` + `Rewrite_proof.verify` (NEVER writing into `Rewrite.journal`!).
   - Otherwise verify single `(lhs, rhs)` via `Rewrite_proof.prove_equality` clamped to remaining `g_total_timeout`.
   - Only merge (`union id1 id2 (Proof ...)`) when verified `Yes` / `proved_compositional`.
3. **Bounded Saturation Loop (`iter = 1 .. !c_egraph_max_iters`, stop early when `not !changed` or `count >= !c_egraph_max_enodes` or timeout):**
   - **Pass A (Per-eclass algebraic + equal-cost AC saturation):**
     Compute current cheapest representative `rep` per root e-class. For each root e-class whose `rep` is not yet in `visited_reps : Nodes.t`, call `Normalization.local_candidates ~cost ~constants ~ac:!c_ac_normalization rep`. For each verified candidate, intern it (`cid = add_expr g cand.expr`) and `union g rep_id cid (Proof ...)`.
   - **Pass B (Direct E-Class OES Semantic Merging):**
     Incrementally evaluate each newly created / unhashed root e-class representative on `!evaluator` and insert into `semantic_buckets : (Sample_evaluator.outhash, int) Hashtbl.t`. When two distinct root e-classes `(r1, r2)` share a hash, verify equivalence between their cheapest representatives (trying `minterm_ring_proof` / `ring_mod2w` before SMT!) and `union` them!
   - **Pass C (Congruence Rebuild):**
     Re-canonicalize every e-node's child IDs via `find`, re-index `hashcons`, and `union` colliding e-classes with `Congruence` (0 SMT cost!) until fixed point.
4. **Global Bottom-Up DP Extraction (under `!cost_model`):**
   - Fixed-point Bellman-Ford DP computing `(best_cost, best_enode)` per root e-class (requiring finite child costs to prevent cycles, tie-breaking by `E.compare`).
   - Reconstruct `extracted = rebuild_best (find root_id)`.
5. **Minimal Spanning-Tree Proof Emission:**
   - Walk `obf` (`root_id`) and `extracted` (`best_enode (find root_id)`): for each pair `(orig_id, chosen_id)` in the same e-class (`find orig_id = find chosen_id`), BFS in `proof_adj` from `orig_id` to `chosen_id`, emit every `Proof` edge along that unique forest path into `Rewrite.journal` (deduplicated!), and recurse on matching children of any `Congruence` step and of `orig_id`/`chosen_id`.
   - Discarded saturation edges are NEVER emitted to `Rewrite.journal`.

### Commit 3: Tests, Audits & Docs
1. Focused unit tests in `test/normalization_test.ml` (or a new `test/egraph_test.ml`):
   - `egraph_max_enodes` and `egraph_max_iters` actually bound e-nodes and iterations,
   - Equal-cost child AC (`(b + a)` / `(b ^ a)`) exposes a strictly cheaper parent rewrite via congruence `rebuild` without discarding the original form,
   - E-class OES merge exposes a parent simplification via congruence `rebuild`,
   - Global DP extraction selects different winners under `legacy` vs `paper_ast`,
   - Unused saturation edges are omitted from the emitted certificate and `mba_proof` independently replays `proved_compositional`.
2. Run `make test` (all green).
3. Re-audit all five 100-case MBA datasets (`PLDI Poly`, `PLDI Non-Poly`, `MBA-Obfuscator nonlinear`, `QSynth EA`, `msimba`) with `egraph_extraction: true`, `ac_normalization: true` (verify zero regressions vs. baseline and 500/500 proved!).
4. Re-audit 1,000-case C-Full comparing baseline vs. `egraph_extraction: true` (`ac_normalization: true`, `egraph_max_enodes: 2048`, `egraph_max_iters: 4`) — verify `1,000/1,000` proved, `>= 984/16` strict reductions, and document exact better/equal/worse counts.
5. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` (mark Milestone 4A `[x]` once all acceptance criteria pass) and commit atomically (do not modify `docs/neon-review*.md`).
