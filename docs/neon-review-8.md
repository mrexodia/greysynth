# GreySynth Round-8 Review: `msimba` Verified, Prototype E-Graph Audit & True Milestone 4A Spec

**Reviewed commits:** `c13930c..cddf339` (`c13930c`, `1a87ebe`, `8dafae3`, `cddf339`)  
**Summary:**
- **Semilinear & polynomial hardening (`c13930c`) is a big win:** All 4 Round-7 normalization bugs are fixed and live-verified (`msimba_L2_bitsliced` `165 -> 5`, `msimba_L3_const_atoms` `242 -> 5` in `0.38s`, `masked_const_xor` `23 -> 7`, all `proved_compositional`). **All five 100-case MBA datasets are now `< 1.00x` geometric quality with 500/500 independently proved** (`msimba` at **0.9966x**, 45.18x compression)!
- **However, `src/greysynth/egraph.ml` (`1a87ebe`) is NOT yet an e-graph** — it is a 3-branch sequential portfolio with three concrete defects that directly explain the 105 C-Full regressions (`115 better / 105 worse`), plus one hot-path overhead in `c13930c` (`early_bitsliced`) that slowed baseline C-Full from `984/16` to `983/17`.

---

## 1. Two Hot-Path Fixes in `src/greysynth/normalization.ml` (`c13930c`)

1. **Remove `early_bitsliced` on unsimplified internal nodes (`normalization.ml:1553-1560`):**
   Currently `early_bitsliced` runs `bitsliced_candidate` (66 full AST evaluations: `f(0)`, 64 one-bit probes, `f(-1)`) on **every** internal node of `cost >= 11` *before* recursing into children. On huge C-Full ASTs (`target_1562`/`target_1565`, size 34,918), this wastes wall budget and caused baseline C-Full to slip from `984/16` to `983/17`.
   - **Fix:** Remove `early_bitsliced` and keep `bitsliced_candidate` strictly bottom-up (line 1581), additionally gating it on single-variable subtrees that actually contain at least one bitwise operation with a nontrivial constant mask (so pure arithmetic/multi-variable C-Full subtrees pay zero evaluation cost).
2. **Lower `ring_polynomial_candidate` minimum cost gate (`normalization.ml:1621`):**
   Line 1621 raised the gate to `cost !current >= 11`, skipping small 5–10 node ring cancellations (e.g., `2*x + 3*x - 5*x`, `a + b - a`). Since `ring_polynomial_candidate` is now DAG-memoized and op-capped with zero SMT calls when no cancellation occurs, gate at `cost !current >= 5`.

---

## 2. Three Concrete Defects in `src/greysynth/egraph.ml` (`1a87ebe`)

1. **Dead reported config options (`config.ml:41-42`, `greysynth.ml:349-350`):**
   `egraph_max_enodes` and `egraph_max_iters` are parsed, validated, and emitted in `report_json`, yet **neither ref is read anywhere in `egraph.ml`** — violating Milestone 2's honesty rule (*changing a reported option must change behavior in a targeted test*).
2. **Preprocessing runs 4–5x sequentially (`greysynth.ml:446-450`):**
   `Egraph.optimize obf` runs `Normalization.run + Oes.linear_simplify` **three times** (`ac=false`, `ac=true`, `ac=true+canonical`), and then `run_passes reference prepared` runs `Normalization.run + Oes.linear_simplify` a **fourth** time (plus final `run_normalization` a **fifth** time). Tripling/quadrupling sequential work under the shared 15-second C-Full deadline directly caused the 105 worse outputs!
3. **Uncached, non-ring `prove_equivalent` (`egraph.ml:54-65`):**
   - Bypasses `Rewrite.proofs` cache and does not check `!g_has_timedout` or clamp to remaining `g_total_timeout`.
   - Does not try `ring_mod2w` (so `ac_normalize` on 64-bit `Plus`/`Mul` trees pays Bitwuzla timeouts instead of 0.1 ms ring checks!).
   - Does not check `!g_has_timedout` between branches 1, 2, and 3 (`egraph.ml:105-108`).

---

## 3. Concrete Spec for True Milestone 4A: Per-Eclass Bounded E-Graph (`src/greysynth/egraph.ml`)

Replace the 3-branch prototype in `src/greysynth/egraph.ml` with a real, compact (~300–400 line) **per-eclass hash-consed e-graph** that **replaces** the separate `Normalization + OES` sequence inside `run_preprocessing` when `egraph_extraction = true`:

### 3.1 Core Data Structures
- **E-node:** `{ width : int; shape : shape; expr : E.t }` where `shape` mirrors `Rewrite_proof.shape` (`Var`, `Cst`, `Unary`, `Binary`, `Ite`), with child IDs canonicalized to e-class representatives (`find child_id`).
- **Union-find & hash-cons:**
  - `parent : int array` (path-compressed union-find over e-class IDs),
  - `nodes : (int, enode list) Hashtbl.t` (e-nodes in each root e-class),
  - `hashcons : (int * shape, int) Hashtbl.t` (structural deduplication + congruence detection),
  - `enode_count : int ref` strictly capped by `!c_egraph_max_enodes`!
  - **Large-AST fast guard:** If `size_of_expr obf > !c_egraph_max_enodes`, fall back cleanly to the standard `Normalization + OES` path (zero regression on 35k-node C-Full trees).
- **Proof-Spanning Forest (no journal pollution!):**
  - Maintain an undirected proof forest over e-class IDs: whenever two distinct e-classes `c1 <> c2` are unioned via a proved rewrite, store ONE spanning-tree edge `(c1, c2, { lhs; rhs; smt_edges; ring_edges; pass })` (and for pure congruence merges during `rebuild`, mark the edge `Congruence` — zero SMT/ring edges needed!).
  - **Do NOT write saturation edges into `Rewrite.journal` during saturation.** Only emit the spanning-tree edges actually needed to connect the input root and the extracted output (Section 3.4).

### 3.2 Bounded Saturation Loop (`iter = 1 .. !c_egraph_max_iters`)
Stop early on fixed point (no new unions/enodes), `enode_count >= !c_egraph_max_enodes`, or `check_timeout ()`:

1. **Seed:** Intern `obf` bottom-up ONCE (`root_id = add_expr obf`).
2. **Algebraic & Non-Destructive AC Saturation (per e-class):**
   - For each active e-class, extract its current cheapest representative `rep` (track `processed : Sexpr.BvTbl.t` so an already-processed `rep` is never re-normalized in subsequent iterations!).
   - Run the existing normalization candidate generators on `rep`:
     - `peepholes`, `canonical_candidates` (**allow equal-cost AC forms** to be added & unioned without overwriting `rep`!),
     - `ring_polynomial_candidate`, `factor_group_candidate`, `minterm_polynomial_candidate`, `linear_candidates`, `product_partition_candidate`, `bitsliced_candidate`.
   - For each candidate `cand`:
     - Check `Rewrite.samples_agree rep cand`.
     - Verify via `ring_mod2w` (for ring/AC `Plus`/`Mul` rewrites!), `minterm_ring_proof`, or `Rewrite.accepts` (always using the shared `Rewrite.proofs` cache and clamping to remaining `g_total_timeout`).
     - If proved and `enode_count < !c_egraph_max_enodes`, intern `cand` and **union** its e-class with `rep`'s e-class, recording the justification in the proof forest!
3. **E-Class OES Semantic Merging:**
   - Incrementally evaluate each newly created / unhashed e-class representative on `!evaluator` and insert into `semantic_buckets : (outhash, int) Hashtbl.t`.
   - When e-class `c` matches an existing bucket representative `target` (`find c <> find target`):
     - Verify equivalence between the cheaper representative and the other (`minterm_ring_proof` / `ring_mod2w` / `Rewrite.accepts` — respecting `proofs` cache & budget).
     - If proved, **union** `c` and `target` in the e-graph!
4. **Congruence Closure (`rebuild`):**
   - Re-canonicalize every e-node's child IDs via `find`, re-index `hashcons`, and union any colliding e-classes (`Congruence` edge — zero SMT cost!), repeating until no new collisions occur.
   - Newly merged child classes immediately make parent e-classes expose cheaper forms on the next iteration!

### 3.3 Global Bottom-Up DP Extraction (Cost-Model Honest)
- Run iterative fixed-point DP over all e-classes under `!cost_model` (`legacy`, `paper_ast`, `instruction`, `readability`):
  - An e-node's cost is `op_cost + sum (best_cost (find child))` (only when all children already have finite `best_cost`, guaranteeing acyclicity!).
  - Tie-break deterministically by `E.compare`.
- Extract `result = rebuild_best (find root_id)`.
- Because `obf` itself stays in `find root_id`, `cost result <= cost obf` is guaranteed!

### 3.4 Minimal Proof-Spanning-Tree Emission
- Emit ONLY the justification edges needed for `Rewrite_proof` congruence closure to connect `obf` to `result`:
  - Walk the proof forest paths connecting the e-nodes participating in `obf` and `result` (or find the connected component / shortest path in the proof forest between every pair `(src_node, dst_node)` where extraction chose a different e-node than the original child, plus all ancestor-congruent pairs — equivalently, emit the edges of the spanning forest on the reachable e-classes of `obf` and `result`, or shortest BFS path per switched e-class!).
  - Record ONLY those edges (`smt_edges` via `Rewrite.record`, `ring_edges` via `Rewrite_proof.record_ring`) into `Rewrite.journal`.
- **Pipeline wiring (`greysynth.ml`):**
  - Inside `run_preprocessing` (NOT before `run_passes`!), when `!c_egraph_extraction` is `true`, run `Egraph.run input` **instead of** separate `Normalization.run` + `Oes.linear_simplify` (keeping `fast_simplify` / `global` / `chs` cleanly afterward). No more 4x duplicate preprocessing!

---

## 4. Acceptance Targets for This Iteration

1. Fix the two `normalization.ml` hot-path items (`early_bitsliced` removal + `ring_polynomial_candidate` `cost >= 5` gate) and verify baseline C-Full returns to **984/16** (`1,000/1,000` proved).
2. Implement the real per-eclass bounded e-graph in `src/greysynth/egraph.ml` wired cleanly inside `run_preprocessing`, honoring `egraph_max_enodes` and `egraph_max_iters`.
3. Add focused unit tests proving:
   - Changing `egraph_max_iters` (`1` vs `3`) and `egraph_max_enodes` visibly changes behavior (Milestone 2 honesty!),
   - Equal-cost / non-monotonic AC reassociation in a child e-class exposes a strictly cheaper parent rewrite without losing the original form,
   - E-class OES merging exposes a parent simplification via congruence rebuild,
   - Global extraction respects `legacy` vs `paper_ast` cost models,
   - Minimal spanning-tree certificate emission drops unused saturation edges and independently passes `mba_proof` replay.
4. Run `make test` (all green), verify all 5×100 MBA datasets (`PLDI Poly`, `PLDI Non-Poly`, `MBA-Obfuscator nonlinear`, `QSynth EA`, `msimba`) with `egraph_extraction: true`, and run the 1,000-case C-Full audit comparing baseline vs. `egraph_extraction: true` (verify `1,000/1,000` proved, `>= 984` strict reductions, and dramatic reduction in cross-run regressions vs. the old 105!).
5. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` and commit atomically (do not modify `docs/neon-review*.md`).
