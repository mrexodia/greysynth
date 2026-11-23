# GreySynth Round-9 Review: Root-Cause of E-Graph Regressions & True Per-Eclass Implementation Blueprint

**Reviewed commits:** `5dcdde1..751257b` (`5dcdde1`, `715613c`, `f3908ca`, `751257b`)  
**Summary:**
- `5dcdde1` cleanly restored the C-Full baseline to **1,000/1,000 established, 984/16 strict reductions** (great fix removing `early_bitsliced` and gating `bitsliced_candidate` on nontrivial constant masks!).
- `715613c` cut C-Full regressions under `egraph_extraction: true` from `105` down to `6` (`18 better / 976 equal / 6 worse`, `984/16`, `1,000/1,000` proved), **but** caused `msimba` to regress from `0.9966x -> 1.4766x` and `PLDI Poly` from `0.8812x -> 0.9991x`.
- Code inspection immediately pinpointed the **exact bug** behind both regressions — AND why `egraph.ml` is still doing expression-branch search instead of per-eclass e-graph saturation.

---

## 1. Smoking-Gun Bug in `src/greysynth/egraph.ml:98-149` (`715613c`)

Look at `egraph.ml:138-148`:
```ocaml
restore branch;
c_ac_normalization := false;
let normalized = Normalization.run branch.expression in
add_candidate branch normalized;
```
And inside `add_candidate` (`egraph.ml:105-113`):
```ocaml
let verdict, _ =
  Rewrite_proof.prove_equality
    ~timeout:(min 1. (float_of_int !c_equiv_timeout))
    base.expression candidate
```
**What happened:**
1. `Normalization.run` and `Oes.linear_simplify` **already** compositionally proved every single rewrite step (via `ring_mod2w`, minterms, factor grouping, etc.) and recorded all obligations into `Rewrite.journal`!
2. Then `add_candidate` ran a **redundant 1-second MONOLITHIC `Rewrite_proof.prove_equality`** on the whole 64-bit `(branch.expression, normalized)` pair!
3. On every 64-bit `msimba` and `PLDI Poly` expression whose proof requires compositional/`ring_mod2w` steps, monolithic 1s Bitwuzla **timed out**, `add_candidate` returned `accepted = false`, and **discarded the already-proved simplified output!**
4. Furthermore, `ac_normalize` on 64-bit `Plus`/`Mul` trees also hit monolithic 1s Bitwuzla instead of `ring_mod2w`, and the `for iteration = 1 to !c_egraph_max_iters` loop kept running even when `!frontier = []`.

That single bug explains **both** the `msimba` (`0.9966x -> 1.4766x`) and `PLDI Poly` (`0.8812x -> 0.9991x`) regressions.

---

## 2. Why `egraph.ml` Needs Real Per-Eclass Saturation (Not Another Branch Worklist)

In `715613c`, `egraph.ml` still stores `type branch = { expression; proof; cache }` (whole-expression snapshots), which forced `egraph_max_enodes` down to `50` and still re-runs `Normalization.run` + `Oes.linear_simplify` repeatedly on full ASTs.

The main reason `egraph.ml` fell back to whole-expression calls is that `Normalization` only exposes `Normalization.run` rather than a per-node candidate generator! **Exposing one small local-candidate API from `Normalization`** makes the true per-eclass e-graph clean, short (~250–350 lines), and zero-redundancy:

### Step 1: Expose `Normalization.local_candidates` (`src/greysynth/normalization.ml`)
Add a clean type and helper function in `Normalization`:
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
Given a single e-class representative `rep`, `local_candidates` returns all proved-ready local candidate proposals (WITHOUT mutating `Rewrite.journal` directly):
- `peepholes constants.eval rep` (strictly cheaper),
- `canonical_candidates rep` when `ac = true` (`allow_equal_cost = true`; for `Plus`/`Mul`, attach `ring_equalities = [ rep, cand ]` so AC reassociation certifies in **0.1 ms** with `ring_mod2w` instead of Bitwuzla timeouts!),
- `ring_polynomial_candidate cost rep` (`cost >= 5`, `ring_equalities = [ rep, cand ]`),
- `factor_group_candidate cost rep` (already returns `(cand, eqs, ring_eqs)`!),
- `minterm_polynomial_candidate cost rep` (already returns `(cand, eqs, ring_eqs)`!),
- `product_partition_candidate rep` (already returns `(cand, eqs)`!),
- `bitsliced_candidate cost rep` (gated on single-var nontrivial mask, attaching `minterm_ring_proof` if available),
- `linear_candidates cost rep` (attaching `minterm_ring_proof` or `complement_product_steps` when `samples_agree`).

### Step 2: Implement True Per-Eclass Hash-Consed E-Graph (`src/greysynth/egraph.ml`)
```ocaml
type shape =
  | Var of string
  | Cst of Bitvector.t
  | Unary of E.unop * int           (* child = canonical eclass id *)
  | Binary of E.binop * int * int
  | Ite of int * int * int

type enode = {
  id : int;
  width : int;
  shape : shape;
  expr : E.t;                        (* concrete term when interned *)
}

type justification =
  | Congruence
  | Proof of {
      lhs : E.t;
      rhs : E.t;
      smt_edges : (E.t * E.t) list;
      ring_edges : (E.t * E.t) list;
      pass : string;
    }
```
Core invariants:
1. **Hash-consed interning (`add_expr`) & fast guard:**
   - Restore sensible default `egraph_max_enodes = 2048` (or `4096`) and `egraph_max_iters = 4`.
   - If `size_of_expr obf > !c_egraph_max_enodes`, set `last_fallback := true` and fall back cleanly to standard `Normalization + OES` (protecting 35k-node C-Full trees).
   - Intern `obf` bottom-up ONCE (`root_id = add_expr g obf`), deduplicating identical subtrees via `hashcons : (int * shape, int) Hashtbl.t`.
2. **Proof-Spanning Forest (`proof_adj`):**
   - Union-find `parent : int array` over e-node IDs `0 .. count - 1`.
   - Whenever `union g id1 id2 just` merges two **distinct** roots `find id1 <> find id2`, record **one** undirected edge `(id1, id2, just)` in `proof_adj`. Because an edge is added *only* across distinct components, `proof_adj` is **always a forest** (at most `N - 1` edges, unique path between any two equivalent e-nodes!).
   - **Never write directly into `Rewrite.journal` during saturation** (and never run monolithic `prove_equality` on already-proved compositional steps!). Instead verify each local edge via a pure helper (using `Rewrite.proofs` cache + `Rewrite_proof.verify` for compositional/ring edges or `Rewrite_proof.prove_equality` for single SMT edges, clamped to remaining global timeout), and store the verified `Proof { ... }` inside `proof_adj`!
3. **Bounded Saturation Loop (`iter = 1 .. !c_egraph_max_iters`, early exit when `not !changed` or `count >= !c_egraph_max_enodes` or timeout):**
   - **Pass A (Bottom-up per-eclass algebraic + non-destructive AC saturation):**
     Compute current cheapest representative `rep` per root e-class. For each root e-class whose `rep` hasn't been expanded yet (`visited_reps : Nodes.t`), run `Normalization.local_candidates ~cost ~constants ~ac:!c_ac_normalization rep`. For each verified candidate `cand`, intern `cand` (`cid = add_expr g cand`) and `union g rep_id cid (Proof ...)`.
     - Equal-cost AC forms coexist in the same e-class alongside the original `rep` without overwriting it!
   - **Pass B (Direct E-Class OES Semantic Merging):**
     Incrementally evaluate each unhashed root e-class's cheapest representative on `!evaluator` and index into `semantic_buckets : (outhash, int) Hashtbl.t`. When two distinct root e-classes `(r1, r2)` share a semantic hash, verify equivalence between their cheapest representatives (trying `minterm_ring_proof` / `ring_mod2w` before SMT, respecting `Rewrite.proofs` cache!) and `union` them!
   - **Pass C (Congruence Rebuild):**
     Re-canonicalize every e-node's child IDs via `find`, re-index `hashcons`, and `union` any colliding e-classes with `Congruence` (**zero SMT cost!**), repeating until fixed point.
4. **Global Bottom-Up DP Extraction (Cost-Model Honest):**
   - Run iterative fixed-point DP over all e-classes under `!cost_model` (`legacy`, `paper_ast`, `instruction`, `readability`), requiring finite child costs (guarantees acyclicity), tie-breaking by `E.compare`.
   - Extract `result = rebuild_best (find root_id)`.
   - Since `obf` itself stays in `find root_id`, `cost result <= cost obf` is guaranteed!
5. **Minimal Spanning-Tree Proof Emission:**
   - Walk `obf` (starting at `root_id`) and `result` (starting at `best_node_of (find root_id)`):
     - For any pair `(orig_id, chosen_id)` in the same e-class (`find orig_id = find chosen_id`):
       - If `orig_id <> chosen_id`, run BFS in `proof_adj` from `orig_id` to `chosen_id` and emit every `Proof` edge along that unique forest path (`smt_edges` via `Rewrite.record`, `ring_edges` via `Rewrite_proof.record_ring`, deduplicated!).
       - Recurse on congruent children of any `Congruence` step along the path and on matching children of `orig_id` / `chosen_id`!
   - Result: **zero unused saturation edges**, **zero monolithic re-checks**, **zero cache-checkpoint hacks**, and **100% independent `mba_proof` replay**!

---

## 3. Acceptance Targets for Round 9

1. Implement `Normalization.local_candidates` and the true per-eclass `src/greysynth/egraph.ml` above (removing the `branch` worklist and its monolithic `add_candidate` re-check bug).
2. Add/update focused unit tests proving:
   - `egraph_max_enodes` and `egraph_max_iters` actually bound e-nodes and saturation rounds,
   - Equal-cost AC in a child e-class exposes a strictly cheaper parent via congruence rebuild without losing the original form,
   - E-class OES merge exposes a parent simplification via congruence rebuild,
   - Global extraction respects `legacy` vs `paper_ast` cost models,
   - Unused saturation edges are omitted from the emitted certificate and `mba_proof` independently replays `proved_compositional`.
3. Run `make test` (all green).
4. Re-audit ALL five 100-case MBA datasets with `egraph_extraction: true` (verify **ZERO regression** vs. baseline: `PLDI Poly` <= `0.8812x`, `PLDI Non-Poly` <= `0.9394x`, `MBA-Obfuscator nonlinear` <= `0.8693x`, `QSynth EA` <= `0.9673x`, `msimba` <= `0.9966x`, all 500/500 proved!).
5. Re-audit 1,000-case C-Full comparing baseline vs. `egraph_extraction: true` (with `ac_normalization: true`!) — verify `1,000/1,000` proved, `>= 984/16` strict reductions, and minimal/zero regressions!
6. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` (marking Milestone 4A complete once all gates pass!) and commit atomically (do not modify `docs/neon-review*.md`).
