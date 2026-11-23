# GreySynth Round-13 Review: Root-Cause of All 17 C-Full Timeouts (Confirmed Infinite Loop in `compute_best`) & Additive-Spine Fix

**Reviewed commits:** `528e12e..2bf7aa8` (`528e12e`, `dcadca2`, `fc5e578`, `2bf7aa8`)  
**Summary:**
- Big quality leap on 3 of the 5 MBA datasets under `egraph_extraction: true`:
  - **`QSynth EA`: `0.8379x`** (beats baseline `0.9673x` by **13%**!)
  - **`PLDI Non-Poly`: `0.9388x`** (beats baseline `0.9394x`!)
  - **`PLDI Poly`: `0.8789x`** (beats baseline `0.8812x`!)
- Live diagnosis of the **17 C-Full 45-second timeouts** and the two slight quality dips (`MBA-Obfuscator nonlinear` `1.0053x`, `msimba` `1.0045x`) just found **two exact, surgical root causes** that should cleanly clear the entire Milestone 4A corpus gate (`1,000/1,000` C-Full, `0` timeouts, all 5×100 datasets `<=` baseline).

---

## 1. Smoking Gun A (Causes ALL 17 C-Full 45s Timeouts): Infinite Loop in `compute_best` on Zero-Cost `Legacy` Cast Cycles (`src/greysynth/egraph.ml:275-322`)

Inspecting `/tmp/greysynth-bench/r12-final-cfull/out.jsonl` showed that `target_3137` (baseline: **0.033s**, `436 -> 3`, 75 casts) and `target_2927` (baseline: **0.133s**, `685 -> 5`, 83 casts) both hung until the 45-second hard kill under `egraph_extraction: true`.

**Live 2-line proof on `target_3137`:**
```text
cm=legacy     HUNG >6.0s!! (INFINITE LOOP CONFIRMED)
cm=paper_ast  DONE in 0.486s: 511 -> 6
```

**Why:**
In `src/greysynth/egraph.ml:277-319`:
- Under `cost_model = Legacy`, `unary_cost Legacy (Uext _ | Sext _ | Restrict _) = 0`!
- Whenever an e-class contains a zero-cost cast cycle (e.g., `restrict(uext(e)) == e` has `cost = 0 + 0 + cost(e) == cost(e)`), line 317 tie-breaks equal costs purely by `E.compare expression previous < 0`.
- When `E.compare (cast(e)) e < 0`, `best.(root)` replaces `e` with `cast(e)` at the **exact same `Legacy` cost** and sets `changed := true` — growing `cast(cast(cast(...)))` infinitely until the 45-second process kill!
- Under `PaperAst`, `unary_cost PaperAst` is `1 > 0` for casts, so cycles strictly increase cost and `target_3137` finishes in **0.486s**!

**Surgical 5-line Fix in `compute_best` (`egraph.ml:275-322`):**
1. Track a **lexicographic triple `(cost, ast_nodes, expression)`** in `best : (int * int * E.t) option array`, where:
   - `cost` is the configured `!cost_model` cost (`unary_cost !cost_model`, `binary_cost !cost_model`, `conditional_cost !cost_model`),
   - `ast_nodes` is the **strictly-positive** AST node count (`1 + sum child_ast_nodes`, ALWAYS `>= 1` even for zero-cost `Legacy` casts!).
2. Update `best.(root)` iff:
   ```ocaml
   cost < prev_cost
   || (cost = prev_cost && ast_nodes < prev_nodes)
   || (cost = prev_cost && ast_nodes = prev_nodes && E.compare expression previous < 0)
   ```
   Because every cycle strictly increases `ast_nodes` by `>= 1`, a cycle can **never** beat a smaller acyclic term — **mathematically guaranteeing termination** for *all* cost models (and also strictly preferring fewer redundant casts under `Legacy`!).
3. Add a belt-and-suspenders `let rounds = ref 0 in while !changed && !rounds <= graph.count do incr rounds; ...` guard.
4. Add a unit regression test with a zero-cost `Legacy` cast cycle (`uext`/`restrict`) verifying `compute_best` / `Egraph.optimize` terminates immediately under `Legacy` cost!

---

## 2. Smoking Gun B (Causes `MBA-Obfuscator nonlinear` `1.0053x` & `msimba` `1.0045x`): Interior `Plus`/`Minus` Spine Prefixes Burn `local_deadline` Before Reaching Maximal Additive Roots

Inspecting `/tmp/greysynth-bench/r12b-mba/out.jsonl` showed why `MBA-Obfuscator nonlinear` slipped from `0.8693x` (baseline) to `1.0053x` (egraph):
```text
mba_obf_nonlinear/line_0000032: in=158 out=76 gt=12 (6.33x) wall=18.11s
mba_obf_nonlinear/line_0000079: in=182 out=35 gt=12 (2.92x) wall=6.91s
```
Both `MBA-Obfuscator nonlinear` (18-term sums of products) and `msimba` (20–26 term sums of masked/constant terms) are deep left-associated additive spines `(((T1 + T2) + T3) + ... + Tn)`.
- Bottom-up iteration visits all $n - 1$ interior partial-sum prefixes (`T1+T2`, `T1+T2+T3`, ..., `T1+...+T_{n-1}`) and runs heavy additive solvers (`factor_group_candidate`, `minterm_polynomial_candidate`, `ring_polynomial_candidate`, `linear_candidates`, `bitsliced_candidate`) on **every single interior prefix**!
- That does $O(n^2)$ redundant work, produces partial mid-spine factorizations (`158 -> 76`), and hits `local_deadline` before the **maximal additive root** (`T1+...+Tn`) ever gets factored as a whole!

**Surgical Fix (`src/greysynth/egraph.ml` + `Normalization.local_candidates`):**
1. Before each saturation pass, compute `is_interior_additive.(class_root)`: an e-class whose cheapest representative is `Plus | Minus | Neg`, is **not** `find graph root`, AND appears ONLY as a child of other `Plus | Minus | Neg` e-nodes (never inside `Mul`, `And`, `Or`, `Xor`, `Not`, `Ite`, casts, etc.).
2. Pass a boolean `~heavy_additive:(not is_interior_additive.(class_root))` into `Normalization.local_candidates`:
   - For **interior additive spine prefixes** (`heavy_additive = false`): run only fast `peepholes` (zero/identity cleanup) — skip `factor_group_candidate`, `minterm_polynomial_candidate`, `ring_polynomial_candidate`, `linear_candidates`, `bitsliced_candidate`, and `canonical_candidates`!
   - For **maximal additive roots** (`heavy_additive = true`, including the root itself and any additive sum directly under `Mul`/`And`/`Or`/`Xor`/`Ite`/casts — like `nonpoly_L2_inner` inside `E & y`!): run the full suite of algebraic/factor/minterm/linear solvers ONCE on the whole sum!
3. **Also wire `Rewrite.proofs` cache into `verify_local` (`egraph.ml:180-208`):** for single-edge SMT obligations (`ring_equalities = []`, `equalities = [lhs, rhs]`), consult and update `Rewrite.proofs` / `Rewrite.proof_budgets` so identical queries are never re-proved across iterations or after fallback.

---

## 3. Acceptance Targets for Round 13

1. Apply **Smoking Gun A** (lexicographic `(cost, ast_nodes, expr)` in `compute_best` + `rounds` cap + zero-cost cast-cycle unit test) and **Smoking Gun B** (`~heavy_additive` interior-spine skip + `Rewrite.proofs` caching in `verify_local`).
2. Verify `target_3137` and `target_2927` complete in `< 1s` under `Legacy` cost with `egraph_extraction: true`, and `mba_obf_nonlinear/line_0000032` drops from `76` back near `12`.
3. Run `make test` (all green).
4. Re-audit ALL **five 100-case MBA datasets** with `egraph_extraction: true`, `ac_normalization: true` — target: **500/500 proved**, **0 timeouts**, and geometric quality matching or beating baseline across all 5 (`PLDI Non-Poly <= 0.9394x`, `MBA-Obfuscator nonlinear <= 0.8693x`, `PLDI Poly <= 0.8812x`, `QSynth EA <= 0.9673x`, `msimba <= 0.9966x`).
5. Re-audit **1,000-case C-Full** with `egraph_extraction: true`, `ac_normalization: true` — target: **1,000/1,000 proved**, **0 process timeouts** (down from 17!), and `>= 984/16` strict reductions.
6. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` (if all gates pass, mark Milestone 4A `[x]`!) and commit atomically (do not modify `docs/neon-review*.md`).
