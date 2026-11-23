# GreySynth Round-11 Review: Real Per-Eclass E-Graph Audit — 6 Concrete Bugs Found (Including `incomplete_derivation` Replay Failure)

**Reviewed commits:** `51d69fe..0f5827f` (6 commits)  
**Summary:** Huge architectural leap! `src/greysynth/egraph.ml` is now a genuine 365-line per-eclass hash-consed e-graph (no more `type branch`, no `Normalization.run` / `Oes.linear_simplify` calls, honest `egraph_max_enodes=2048` / `egraph_max_iters=4`).  
However, careful code inspection + a 3-case live Dev Container probe exposed **6 concrete bugs** in the new `egraph.ml` — including a **reproducible `mba_proof` `incomplete_derivation` certificate bug** whenever a child e-class simplifies and feeds a parent rewrite!

---

## 1. Live Reproducers (`0f5827f`, `egraph_extraction=true`, `ac_normalization=true`, `oes=false`, `chs=false`)

```text
child_mba_inside_mul    (z * (L2_inner + y)): 31 -> 5  t=3.117s  replay=unknown (incomplete_derivation) edges=1
child_ac_expose_parent  ((b + a) ^ (a + b)):   7 -> 1  t=0.033s  replay=unknown (incomplete_derivation) edges=1
```

Both expressions simplified correctly, yet `mba_proof` rejected both certificates as `incomplete_derivation`!

---

## 2. Six Concrete Bugs in `src/greysynth/egraph.ml`

### Bug 1 (Critical — Certificate Incompleteness): `emit_component_proofs` drops ALL child e-class proofs (`egraph.ml:270-294`)
Line 274 only emits `proof_adj` edges whose endpoint `id` satisfies `find graph id = find graph root`.
- Whenever a rewrite occurs inside a **child e-class** `c1 <> root` (e.g. `b + a == a + b` inside `(b + a) ^ (a + b)`, or `L2_inner == a` inside `z * (L2_inner + y)`), `find graph c1 <> root`, so **zero edges from `c1` are emitted into `Rewrite.journal`**!
- `mba_proof` therefore sees an unconnected derivation and fails with `incomplete_derivation`!

**Fix — Recursive Minimal Shortest-Path Proof Emission:**
1. Replace `emit_component_proofs` with a recursive `emit_equiv graph orig_id target_id` (requires `find graph orig_id = find graph target_id`, deduplicating visited `(min u v, max u v)` pairs):
   - If `orig_id = target_id`: done! (Wait: also ensure that if `orig_id` was built by `add_expr_unbounded` using a canonicalized child `c'`, any `orig_child` vs `target_child` pair is handled via `Congruence`!)
   - Run **BFS in `graph.proof_adj`** from `orig_id` to `target_id` to get the unique shortest path `[u_0; u_1; ...; u_k]` in the spanning forest.
   - For each edge `(u, v, justification)` along that shortest path:
     - `Proof p`: emit `p.smt_edges` and `p.ring_edges` into `Rewrite.journal` (once per edge).
     - `Congruence`: `(node graph u)` and `(node graph v)` share the same operator and width with pairwise-congruent children `(c_u1, c_v1), ...` — **note:** store the **pre-canonical original child node IDs** (`raw_children : int list`) on each `enode` (not just canonicalized `find` IDs!), so `Congruence` knows the EXACT child node IDs `(c_u_i, c_v_i)` of `u` and `v` and recurses `emit_equiv graph c_u_i c_v_i`!!
2. **CRITICAL subtlety on `add_expr` (`egraph.ml:114-120`)!**
   - Look at `add_expr`: when `add_expr graph result` runs at line 358, suppose `result` is `z * (a + y)` where `a` is already in `L2_inner`'s e-class.
   - Line 116 finds `z * (L2_inner + y)` in `graph.hashcons` and returns `orig_id` (`root`) **WITHOUT creating a new enode for `result` or recording a `Congruence` edge** — so `result_id = root` even though `(node graph root).expr` is `z * (L2_inner + y)` (NOT `z * (a + y)`)!!
   - **Fix:** When `add_expr` interns a compound node `expr = op(x1, ...)` whose children intern to `c1, ...` and `hashcons` hits an existing `existing_id` whose `(node graph existing_id).expr` is **not** `E.is_equal expr`:
     - Either create a dedicated `emit_expr_equiv graph expr target_id` walker that walks `expr`'s syntax directly against `(node graph target_id)`:
       - First, if `expr` is syntactically equal to `(node graph target_id).expr`, done!
       - Otherwise, if `expr = op(x1, ...)` and `(node graph target_id).expr = op(y1, ...)` (same op/width, and each `x_i` is in the same e-class as `y_i`), recurse `emit_expr_equiv x_i y_i_id` directly!
       - Otherwise, find `expr`'s e-node `expr_id` (if `expr` was interned via `add_expr` returning `existing_id`, we need the `raw_children` match against `existing_id`, OR simply create a lightweight node in `graph` on hashcons hit whenever `not (E.is_equal enode.expr expr)` and link it via `add_proof_edge graph new_id existing_id Congruence` — storing `raw_children` on every `enode`!).
     - Even cleaner: store `raw_children : int list` on `enode`, and when `add_expr` hits `existing_id` with `not (E.is_equal (node graph existing_id).expr expr)`, allocate a new `enode` (bypassing `Full` during final `result` interning!) with `raw_children = [c1; ...]` and call `add_proof_edge graph new_id existing_id Congruence` (pointing `parent.(new_id) <- find graph existing_id`)!
     - Then `emit_equiv graph root result_id` handles **BOTH** child simplifications AND minimal BFS spanning-tree paths in ~45 lines, with **100% mathematical completeness AND minimality**!

### Bug 2 (Critical — Stale `hashcons` Overwrite in `rebuild`, `egraph.ml:191-192`)
```ocaml
if !merged then round () else graph.hashcons |> Hashtbl.clear;
Hashtbl.iter (fun key id -> Hashtbl.replace graph.hashcons key id) index
```
When `!merged = true`, `round ()` runs Round 2 (which clears and populates `graph.hashcons`), and then **Round 1 resumes at line 192 and overwrites `graph.hashcons` with Round 1's stale pre-merge `index`!**
- **Fix:** Move `Hashtbl.iter ...` inside the `else (...)` branch:
  ```ocaml
  if !merged then round ()
  else (
    Hashtbl.clear graph.hashcons;
    Hashtbl.iter (fun key id -> Hashtbl.replace graph.hashcons key id) index)
  ```

### Bug 3 (High — $O(N^2)$ `extract` with No Early Exit, `egraph.ml:245-267`)
`for _ = 0 to graph.count do` runs **2,001 full iterations** when `graph.count = 2000`, recomputing unmemoized `size_of_expr` on every rebuilt expression on every pass!
- **Fix:** Use `let changed = ref true in while !changed do changed := false; ...` and compute cost incrementally (`op_cost + child_cost_sum` using `!cost_model` unary/binary/conditional costs instead of recursively calling `size_of_expr`!). Converges in 3–10 passes (`< 0.5 ms`) instead of 2,001 passes!

### Bug 4 (High — Child Simplifications Don't Materialize into Parent E-Classes, `egraph.ml:124, 325-327`)
Because each `enode.expr` is frozen at intern time (`f(x + 0)`), once a child e-class `x + 0` merges with `x`, the parent e-class's `cheapest` representative is STILL the frozen `f(x + 0)` (already in `visited`!). So iteration 2 **never runs `local_candidates` on `f(x)`**, preventing child simplifications (and equal-cost child AC forms!) from unlocking parent rewrites — which is why `child_mba_inside_mul` took 3.1s and why `265a7b5` needed a stall fallback!
- **Fix:** At the start of each saturation iteration (or after `rebuild`), run the now-sub-millisecond `extract` DP to get `best_expr.(root)` for every root e-class! When `best_expr.(root)` is not in `visited`, intern it (connecting via `Congruence`) and run `Normalization.local_candidates` on `best_expr.(root)`!
  - Also, when an e-class contains an equal-cost AC variant (e.g., `a + b` alongside `b + a`), allow parent e-classes to see the AC-canonicalized child representative so `(b + a) ^ (a + b)` collapses immediately via congruence `rebuild`!

### Bug 5 (High — `verify_local` & `semantic_merge` Bypass Caches, Deadlines & `ring_mod2w`, `egraph.ml:154-174, 197-228`)
1. `verify_local` (`egraph.ml:154-174`) ignores `Rewrite.proofs` / `Rewrite.proof_budgets`, never clamps its timeout to remaining `g_total_timeout`, and calls `Rewrite_proof.verify` from scratch even on previously proved or failed pairs.
2. `semantic_merge` (`egraph.ml:197-228`) re-evaluates `!evaluator.node_to_outhash` for every e-class on every iteration, retries the exact same failed pairs every iteration, and NEVER tries `Normalization.minterm_ring_proof` or `ring_mod2w` (so 64-bit semantically equivalent e-classes time out Bitwuzla instead of proving in `1 ms`!).
- **Fix:**
  - Clamp `verify_local`'s timeout to remaining `g_total_timeout` and consult/update `Rewrite.proofs` / `Rewrite.proof_budgets` (keyed symmetrically).
  - In `semantic_merge`, memoize e-class hashes + attempted failed pairs, and try `Normalization.minterm_ring_proof` / `ring_mod2w` before monolithic SMT!

### Bug 6 (Medium — `egraph.ml:353` Premature Stop at `cost <= 5` & `265a7b5` Stall Fallback):
Line 353 stops saturation as soon as `size_of_expr root_best <= 5`, which can miss a `5 -> 1` or `5 -> 3` reduction (e.g. `(x + 0) + (y * 0)` size 5 -> `x` size 1, or `(x & y) + (x & ~y)` size 5 -> `x` size 1)! Stop early ONLY on `size_of_expr root_best <= 1` or `not !changed`.

---

## 3. Acceptance Targets for Round 11

1. Fix all **6 bugs** above in `src/greysynth/egraph.ml` (and any needed tiny helper in `rewrite.ml` / `normalization.ml`).
2. Add the two exact live reproducers above (`child_mba_inside_mul` and `child_ac_expose_parent`) plus an unused-saturation-edge pruning check as **solver-backed `mba_proof` replay tests** in `test/normalization_test.ml` (all must replay `proved_compositional` with zero `incomplete_derivation`, and the unused-edge test must prove strictly fewer edges are emitted than total `proof_adj` edges in the e-graph!).
3. Run `make test` (all green).
4. Re-audit ALL five 100-case MBA datasets (`PLDI Poly`, `PLDI Non-Poly`, `MBA-Obfuscator nonlinear`, `QSynth EA`, `msimba`) with `egraph_extraction: true`, `ac_normalization: true` — verify **500/500 `proved_compositional` / `proved`**, zero `incomplete_derivation`, and quality <= baseline across the board (expect `PLDI Non-Poly` <= `0.9394x` as well!).
5. Re-audit 1,000-case C-Full (`egraph_extraction: true`, `ac_normalization: true`) — verify **1,000/1,000 proved**, `>= 984/16`, and check whether fixing Bugs 2–5 eliminates the remaining 6 cross-run regressions!
6. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` (mark Milestone 4A `[x]` once all gates pass!) and commit atomically (do not modify `docs/neon-review*.md`).
