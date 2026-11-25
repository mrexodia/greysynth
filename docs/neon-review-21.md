# GreySynth Round-21 Spec: DAG-Native Simplification & Minterm-Ring Nonlinear MBA Cancellation

**Baseline commit:** `ccce9f8` (Round 20 `linear_mba_mod2w` complete — all 6/6 4–5-var SiMBA suites jumped to `966..1,000/1,000`, `MBA-Flatten` `0.9976x`, `Neureduce` 1k `0.9996x`!)  
**Target:** Crush the giant DAG-shaped C suites exposed in Wave 1:
- **`C-MBA-Obfuscator` (`500` cases):** `17/500` solved, **`463/500` weak**, **`143.16x`** geomean out/GT (e.g., `target_3218`: `54,904` tree nodes -> **312 unique DAG nodes**; `target_366`: `3,400,417` tree nodes -> **627 unique DAG nodes**!).
- **`Tigress L5–L8` (`4,000` cases):** L5 `9.14x`, L6 `12.06x`, L7 `15.15x`, L8 `33.47x` + 4 persistent timeouts (e.g., `tigress_lvl_5/target_5857`: `186,155` tree nodes -> **71 unique DAG nodes** (`2,622x` sharing!); `tigress_lvl_7/8/target_4174`: `1M–7.18M` tree nodes!).
- **`C-OMVLL` (`988` cases):** `3.03x`, 9 persistent timeouts (e.g., `omvll/target_2246`: `3,921` tree nodes -> **42 unique DAG nodes** (`93x` sharing!)!).
- **`C-Loki` (`999` cases):** `135` weak cases.

All while keeping **100% fail-closed soundness** (`0` refuted, independent `mba_proof` / `mba_equiv` replay).

---

## 1. DAG-Memoized Utilities & Eliminating Exponential Tree Walks (`src/utils/utils.ml`, `src/greysynth/oes.ml`, `src/greysynth/egraph.ml`, `src/greysynth/normalization.ml`, `src/proof/rewrite_proof.ml`)

Empirical DAG analysis of the hardest Wave-1 C suites shows massive structural sharing (`93x` to `5,423x` tree-to-DAG blowup), yet multiple hot-path functions still traverse expressions as unmemoized trees or gate on **tree size** instead of **unique DAG size**:

**Deliverables:**
1. **Add `dag_size_of_expr : Sexpr.Expr.t -> int` in `src/utils/utils.ml`** (counting distinct `Sexpr.BvTbl` nodes reachable from the root, with an optional early-stop cap `dag_size_bounded ~limit e` so checking `<= limit` is $O(\text{limit})$ even on massive DAGs!).
2. **Make `cost_of_expr` overflow-safe (`src/utils/utils.ml:227-247`):** Use saturating addition (`let sat_add a b = if a >= 1_000_000_000 - b then 1_000_000_000 else a + b`) so a 7M+ tree-size DAG never overflows `int` on 32/64-bit arithmetic in `cost_of_expr` or `Egraph.compute_best` (`egraph.ml:346`).
3. **Eliminate unmemoized tree walks on DAGs (fixes persistent Tigress L6–L8 & OMVLL timeouts!):**
   - `src/greysynth/oes.ml:33-42` (`record_semantics`): memoize visited nodes in a `Sexpr.BvTbl.t` (or record unique DAG nodes) so a 7.18M-tree-node / 150-DAG-node expression takes microseconds instead of visiting 7.18M nodes twice!
   - `src/greysynth/oes.ml:148-171` (`proof_complexity`): memoize in a `Sexpr.BvTbl.t` with saturating addition!
   - `src/greysynth/egraph.ml:382-386` (`additive_terms`): memoize in a `Sexpr.BvTbl.t` (capped at `1_000_000`)!
   - `src/proof/rewrite_proof.ml:668-691` (`linear_mba_equal`: `collect_linear` / `collect_bitwise`): memoize `seen_linear` and `seen_bitwise` by node ID (`Array.make g.count false`) AND add `tick assignments` in `scale` so `mba_proof` stays $O(\text{unique DAG nodes})$ even on 3.4M-tree-node inputs!
   - Audit `Sample_evaluator.variables_of_expr` and `Normalization.linear_mba_compatible` — ensure BOTH are memoized by `Sexpr.BvTbl.t`!

---

## 2. DAG-Size-Aware E-Graph & Memoized Bottom-Up DAG Pass (`src/greysynth/egraph.ml`, `src/greysynth/greysynth.ml`, `src/greysynth/normalization.ml`)

Currently `egraph.ml:514` checks `size_of_expr expression > !c_egraph_max_enodes` (TREE size!), immediately rejecting:
- `omvll/target_2246` (`3,921` tree / **`42` DAG**!)
- `tigress_lvl_5/target_5857` (`186,155` tree / **`71` DAG**!)
- `mba_obfuscator/target_3218` (`54,904` tree / **`312` DAG**!)
- `mba_obfuscator/target_366` (`3,400,417` tree / **`627` DAG**!)

And `greysynth.ml:246-249` gates `preserve_large_dag_budget` on `size_of_expr !best > 768` (TREE size!), skipping `Normalization.run`!

**Deliverables:**
1. **Gate `Egraph.optimize` on unique DAG size (`egraph.ml:514`):**
   - Replace `size_of_expr expression > !c_egraph_max_enodes` with `dag_size_of_expr expression > !c_egraph_max_enodes` (keeping a safe headroom check like `dag_size_of_expr expression > !c_egraph_max_enodes - 32` or `limit = max !c_egraph_max_enodes (dag_size * 2)` capped at e.g. `4096` so saturation has room to add simplified nodes without hitting `Full`!).
   - Also check `egraph.ml:540` (`when size_of_expr root_expression <= 1024`): gate on `dag_size_of_expr root_expression <= 1024` (with safe fast linear/poly checks)!
   - In `Egraph.optimize` iteration loop (`egraph.ml:671`), sort classes bottom-up by `dag_size` / `cost`, and ensure `Egraph.verify_local` and `Egraph.semantic_merge` also support `linear_mba_mod2w` (from Round 20) so bottom-up sub-DAG collapses in Tigress (like `(A + B) - (A | B) -> A & B` or `(A & B) + (A | B) -> A + B`) certify in microseconds and collapse ALL 128+ shared copies simultaneously via congruence!
   - Allow slightly more iterations when a large DAG is actively shrinking (e.g., if `dag_size` or `tree_size` dropped strictly by `>= 25%` on an iteration and budget remains, continue up to `max !c_egraph_max_iters 8` iterations — critical for 5–8 layered Tigress DAGs where each layer strips 1–2 levels of obfuscation!).
2. **Memoized Bottom-Up DAG Pre-Pass (`dag_bottom_up_simplify`) in `src/greysynth/normalization.ml` / `greysynth.ml`:**
   - For expressions with `size_of_expr !best > 768` (or `dag_size_of_expr !best > 128`), add a fast bottom-up DAG-memoized pass (each unique `Sexpr.BvTbl` node visited **at most once**!) BEFORE the e-graph / OES-first fallback:
     - Recursively simplify children first (rebuilding node with simplified children if any changed — automatically propagating every sub-DAG collapse to ALL shared parents with zero extra proof edges via congruence!).
     - At each unique node with `dag_size` in `[3 .. 1024]`, try fast zero-SMT local reducers in order:
       1. Minterm-ring nonlinear MBA cancellation (Section 3 below!)
       2. `linear_candidates` certified by `linear_mba_mod2w` (when `linear_mba_compatible` and atoms $\le 8$)
       3. `reduce_modular_polynomial` certified by `poly_mod2w` (when polynomial degree $\ge 2$)
       4. `ring_polynomial_candidate` certified by `ring_mod2w`
     - Accept any strict reduction immediately via `Rewrite.accepts_compositional` (sub-millisecond, zero Bitwuzla SMT!) and memoize `original_node -> simplified_node`!
   - Also update `greysynth.ml:246-249`: compute `preserve_large_dag_budget` using `dag_size_of_expr !best > 768` (instead of tree `size_of_expr > 768`) so a 186,155-tree-node / 71-DAG-node Tigress target isn't forced to skip normalization!

---

## 3. Minterm-Ring Nonlinear MBA Cancellation (`src/greysynth/normalization.ml`, `egraph.ml`) — Crushing `C-MBA-Obfuscator` (`463/500` weak at `143.16x`!)

Inspecting `datasets/greysynth/mba_obfuscator/mba_info/target_3218.json` (`54,904` tree / `312` DAG nodes, GT `(x0 + 0x2b6109100) * 0x989680`) reveals the exact algebraic structure of **MBA-Obfuscator's polynomial/nonlinear MBA**:
- The outer wrapper is a linear MBA over `(INNER & y)` and `(INNER & ~y)` (which collapses in 1 `linear_mba_mod2w` edge once `INNER` collapses!).
- `INNER` is a **quadratic (degree-2) polynomial over 2-variable Boolean atoms** of `(x0, y)`:
  `(x0 & y), (x0 & ~y), (x0 | y), ~(x0 | y), ~(x0 | ~y), ~(x0 & y), ~x0, x0` (45 additive terms, 39 of them quadratic products like `-0x23 * (x0 & y) * (x0 & y) - 0x2a * (x0 & y) * (x0 & ~y) + ...`).
- **Exact algebraic proof (verified directly on `target_3218`!):**
  1. Let $a_0, \dots, a_{k-1}$ ($k \in \{2, 3\}$) be the $k$ base atoms appearing inside the pure-bitwise leaf factors of a ring polynomial expression $E$ (with `dag_size <= 1024`, ring degree $\le 4$, and at least one nonlinear product of bitwise atoms).
  2. Define the $2^k - 1$ non-zero canonical minterm expressions $M_1, \dots, M_{2^k - 1}$ over $a_0, \dots, a_{k-1}$ (for $k = 2$: $m_1 = \neg a_0 \land a_1$, $m_2 = a_0 \land \neg a_1$, $m_3 = a_0 \land a_1$; for $k = 3$: the 7 non-zero minterms).
  3. Every distinct pure-bitwise factor $B_i$ appearing in $E$ has an **exact linear expansion** $B_i \equiv c_i + \sum_{b=1}^{2^k-1} \alpha_{i,b} M_b \pmod{2^w}$ (where if `truth(B_i)[0] = false`, $B_i = \sum_{b \in T} M_b$; if `truth(B_i)[0] = true`, $B_i = -1 - \sum_{b \notin T} M_b$).
     - **Each substitution $B_i \equiv L(B_i)$ is certified by ONE instant `linear_mba_mod2w` edge!**
  4. Substitute $B_i \mapsto L(B_i)$ into $E$ to obtain $E_{\text{sub}}$ (connected to $E$ by congruence over the $\le 16$ `linear_mba_mod2w` edges!), then expand $E_{\text{sub}}$ as a sparse formal polynomial mod $2^w$ in $M_1, \dots, M_{2^k - 1}$ (using `ring_mod2w` — or `poly_mod2w` if modular null terms remain!).
     - **On `target_3218`, ALL 39 quadratic terms cancel identically to `0`, leaving $m_2 + m_3 + \text{0x2b6109100}$!!**
  5. Rebuild the simplified polynomial $P(M_1, \dots, M_{2^k-1})$:
     - Certify $E_{\text{sub}} \equiv P$ by **ONE `ring_mod2w` edge** (or `poly_mod2w` if modular null terms were reduced!).
     - If $P$ is linear in $M_1, \dots, M_{2^k-1}$ (degree $\le 1$!), pass $P$ directly to `linear_candidates` to reconstruct the compact form $R$ (e.g., $x_0 + \text{0x2b6109100}$), certified by **ONE `linear_mba_mod2w` edge** $P \equiv R$!
     - **Total proof for `target_3218` `INNER` (`3,156` chars -> `3` nodes): ~8 `linear_mba_mod2w` edges + 1 `ring_mod2w` edge + 1 `linear_mba_mod2w` edge = ZERO Bitwuzla SMT calls, < 2 ms!**
     - And for the entire `target_3218` (`54,904` tree nodes) and `target_366` (`3,400,417` tree nodes): bottom-up DAG simplification collapses `INNER` ONCE, then `linear_mba_mod2w` collapses the outer wrapper ONCE $\implies$ **EXACT GROUND TRUTH in < 10 ms!!**

**Deliverables:**
- Implement `minterm_ring_poly_candidate cost expression` in `src/greysynth/normalization.ml` (handling $k = 2$ and $k = 3$ base atoms, degree $\le 4$, bounded monomial count $\le 512$, DAG-memoized parsing!).
- Wire it into:
  1. `dag_bottom_up_simplify` (Section 2)
  2. `Normalization.local_candidates` & `Normalization.run`
  3. `Egraph.optimize`
- Also check `datasets/greysynth/mba_obfuscator` for any 3-variable or degree-3/4 variants (e.g., `target_366`) and verify they collapse cleanly!

---

## 4. Focused Unit Tests & Verification Gate for Round 21

1. **Unit & regression tests (`test/normalization_test.ml`, `test/proof_test.ml`):**
   - Direct regression tests on actual giant DAG cases (with independent `mba_proof` replay verified!):
     - `datasets/greysynth/mba_obfuscator/mba_info/target_3218.json` (`54,904 -> 5`, exact GT!)
     - `datasets/greysynth/mba_obfuscator/mba_info/target_366.json` (`3,400,417 -> <= 11`, exact GT!)
     - `datasets/greysynth/tigress_lvl_5/mba_info/target_5857.json` (`186,155 -> <= 7`, exact GT!)
     - `datasets/greysynth/tigress_lvl_7/mba_info/target_4174.json` (`1,007,670 ->` dramatic collapse!)
     - `datasets/greysynth/omvll/mba_info/target_2246.json` (`3,921 -> <= 11`, exact GT!)
   - DAG-memoization performance test ensuring `dag_size_of_expr`, `cost_of_expr`, `Oes.proof_complexity`, and `Rewrite_proof.linear_mba_equal` run in milliseconds on deep shared DAGs (20+ levels of `x_i = x_{i-1} + x_{i-1}`).
2. **Run `make test`** — 100% green.
3. **Targeted Verification Audits (keep wall time ~20–30 min and container RAM well under 30 GB!):**
   - **Full `C-MBA-Obfuscator`** (`500` cases, zero `--limit`, `--workers 8`) — target: massive jump from `17/500` solved (`143.16x`, `463` weak) toward `~450–500/500` solved (`~1.0x`)!
   - **Full `Tigress L5`** (`1,000` cases, zero `--limit`, `--workers 8`) — baseline: `424/1,000` solved (`9.14x`, `86` weak).
   - **Targeted `Tigress L8` (`--limit 200` + isolated test of the 4 Wave-1 persistent timeouts: L6 `2327/2328/2491` & L8 `4174`, `--workers 4`)** — baseline L8: `369/1,000` solved (`33.47x`).
   - **Targeted `C-OMVLL` (`--limit 200` + isolated test of the 9 Wave-1 persistent OMVLL timeouts, `--workers 4`)** — baseline: `3.03x`, 9 timeouts.
   - **Targeted `C-Loki` (`--limit 200`, `--workers 8`)** — verify improvement / zero regressions.
   - **Quick 5×100 MBA smoke gate** — confirm **500/500 established, 0 refuted, 0 errors**.
4. Record concise Round-21 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `docs/FULL_AUDIT_REPORT.md`).
