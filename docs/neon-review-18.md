# GreySynth Round-18 Spec: Post-Audit Bugfixes & High-Impact Optimization Round

**Baseline commit:** `196dacb` (`72/72` PLAN items complete; full 7,011-expression audit recorded in `docs/FULL_AUDIT_REPORT.md`)  
**Goal:** Eliminate the **13 `Z.Overflow` runtime crashes** found on the full `PLDI Poly` corpus, recover the **Loki / Full-Loki / QSynth EA large-DAG regressions** (where normalization starved OES), and crush the three biggest remaining simplification gaps (**325 `mba_obf_linear`**, **288 `mba_obf_nonlinear`**, and **369 `pldi_nonpoly`** cases) — while preserving 100% fail-closed soundness (`0` refuted, `100%` independent `mba_proof` replay).

---

## 1. Fix All `Z.Overflow` Runtime Crashes (`src/greysynth/normalization.ml`)

The full 1,008-case `PLDI Poly` audit uncovered **13 crashes** (`line_0000092`, `111`, `144`, `156`, `193`, `252`, `260`, `430`, `466`, `563`, `627`, `655`, `672`) terminating with `Fatal error: exception Z.Overflow` right after a CHS rewrite like `(y<64> * (x<64> - 0xfffffffffffffffe<64>))`.

**Root cause:**
- `src/greysynth/normalization.ml:271`: `Some (base, Z.to_int (Bitvector.value_of offset))` calls `Z.to_int` on an arbitrary 64-bit unsigned `Bitvector.value_of` (which overflows OCaml's 63-bit signed `int` for any value `>= 2^62`, such as `0xfffffffffffffffe`!).
- Also audit `src/greysynth/normalization.ml:573` and `823` (and any other `Z.to_int` in `src/`): guard every `Z.to_int` on bitvector values with `bounded_count` or explicit signed/small-range checks (`Z.fits_int` / modular signed offset check) so no 64-bit or 128-bit constant can ever raise `Z.Overflow`.

**Deliverable & test:**
- Fix lines `271`, `573`, `823` (and audit all `Z.to_int` sites across `src/`).
- Add a focused regression test in `test/normalization_test.ml` running `Normalization.run` and `Egraph.optimize` on `y * (x - 0xfffffffffffffffe<64>)` and `pldi_poly/line_0000092`, verifying zero exception and independent certificate replay.

---

## 2. Large-DAG Fast Path: Constant-Root Check + OES-First + Preprocessing Budget Guard (`src/greysynth/greysynth.ml`, `src/greysynth/normalization.ml`)

The full audit showed **why** `AFTER` regressed on huge Loki trees (`11,480 -> 10,915` vs paper `3` in `0.30s`) and zero-valued QSynth expressions (`1,753 -> 192` vs paper `1` in `0.15s`): `lin_t = 0.0`! Normalization burned the entire 5s timeout before OES ever ran.

**Deliverables:**
1. **Instant proved constant-root check** at the start of `run_preprocessing`:
   - When `!c_oes` (or `!c_normalization`) is enabled, check `!evaluator.is_node_constant !best`. If all training samples agree on a single constant `c`, immediately attempt `Rewrite.accepts ~pass:"root-constant" !best (E.constant c)` — collapsing constant-valued expressions like `qsynth_ea/163`, `393`, `288` (`1,753 -> 1`) to `0` in milliseconds with a 1-edge direct SMT proof!
2. **OES-first on large DAGs (`size_of_expr !best > 512` or `> !c_egraph_max_enodes`):**
   - When `!c_oes` is enabled and the input exceeds `512` nodes (e.g. giant 1,000–11,000-node Loki / Full-Loki / QSynth trees full of semantically redundant subtrees), run a proof-gated `oes_with_logs` pass **before** `Egraph.optimize` / `Normalization.run`!
   - If OES collapses the tree below `!c_egraph_max_enodes` (2,048), `Egraph.optimize` can then run cleanly on the shrunk expression instead of falling back!
3. **Preprocessing time guard so OES + CHS are never starved:**
   - When `!g_total_timeout > 0.` and `(!c_oes || !c_chs)` is enabled, give greedy `Normalization.run` a soft internal deadline (e.g., at most `60%` of remaining total budget, raising a local soft-stop caught inside `Normalization.run` that returns the partial proved result without setting `g_has_timedout := true`), guaranteeing OES and CHS always get time to run!
4. **Focused regression tests (`test/pipeline_test.ml`):**
   - Constant-root expression collapses in 1 step with `proved_compositional` certificate replay.
   - Large (>512-node) redundant DAG collapses via OES-first before normalization/e-graph and independently replays.

---

## 3. Equal-Coefficient Minterm Grouping + Compact Boolean Reconstruction (`src/greysynth/normalization.ml`)

The 325 remaining `mba_obf_linear` "meaningful" cases (e.g., `line_0000788`: `11*(v0&v1&v2) + 11*(~v0&v1&v2) + ...` of size 63 vs GT `11*(v0|(v1|v2))` of size 7; `line_0000973`: size 37 vs GT `6*~v1` of size 4) already solved the minterm coefficients — they only stayed bloated because each minterm was emitted as a separate additive term!

**Deliverables:**
1. In `linear_candidates` / `minterm_polynomial_candidate` (when reconstructing a linear MBA from its truth-table / minterm coefficient vector):
   - Group non-zero minterms by **equal coefficient `c`** (and optionally `±c` buckets so `-c * f` uses a single negated scale when cheaper!).
   - For each coefficient bucket `c` with bitmask `M` of active minterms over the `k` atoms (`k <= 6`), synthesize a compact Boolean expression `B(atoms)` for `M` using our existing compact DNF/CNF/ANF Boolean extractor (preferring single-atom, negated-atom, 2-op OR/AND/XOR, or compact DNF/CNF over sum of individual minterms!).
   - Emit `sum_c (c * B_c(atoms)) + offset` as a candidate alongside existing reconstructions, certified through the exact same `minterm_ring_proof` / `ring_mod2w` boundary!
2. **Focused regression tests (`test/normalization_test.ml`):**
   - 3-variable `11*(v0 & v1 & v2) + 11*(~v0 & v1 & v2) + ...` collapses to `11 * (v0 | v1 | v2)` (cost `<= 7`) and replays via `mba_proof`.
   - 3-variable `mba_obf_linear/line_0000973` collapses to `6 * (~v1)` (cost `<= 4`) and replays via `mba_proof`.

---

## 4. Connected-Component Opaque-Atom Linear MBA Partitioning (`src/greysynth/normalization.ml`)

The 288 weak `mba_obf_nonlinear` cases (e.g., `line_0000949` `GT: 6*y`, `line_0000911` `GT: 11*y`) have the structure:
```text
8*(A & B) - 10*(A & ~B) + 11*~(A & B) - 6*~(A & ~B) - 5*~(A | B) - 4*~(A | ~B) + [linear MBA in x, y]
where A = ~(x ^ y), B = -11 * ~(x & ~y)
```
The first 6 terms are a **2-atom linear MBA over opaque atoms `(A, B)`** that simplifies directly to `A + B`, after which the whole expression becomes a 2-variable linear MBA in `(x, y)` that collapses straight to `6 * y`!

**Deliverables:**
1. Add a **connected-component additive subset linear-MBA solver** in `Normalization` (exposed to both `Normalization.run` and `Normalization.local_candidates`):
   - Flatten a top-level additive sum `t_1 + ... + t_m` into signed/scaled terms.
   - For each term `c_i * body_i`, extract its maximal bitwise-opaque atoms (stopping at any `Mul`, `Plus`, `Minus`, `Lsl`, etc. inside a bitwise op — e.g., `B = -11 * ~(x & ~y)` — and also treating shared non-leaf bitwise subterms like `A = ~(x ^ y)` as candidate opaque atoms when they co-occur with an arithmetic opaque atom `B`!).
   - Partition terms that share an arithmetic opaque atom `B` into their own connected component (so the 6 terms mentioning `B` form a clean 2-atom `{A, B}` component, separate from the `{x, y}` terms!).
   - Run linear-MBA reconstruction + `minterm_ring_proof` on each non-trivial component (`>= 2` terms, `<= 4` opaque atoms); replace the component by its simplified sum (`A + B`), allowing the outer pass/e-graph to immediately collapse the remaining `{x, y}` linear MBA to `6 * y`!
2. **Focused regression tests (`test/normalization_test.ml`):**
   - `mba_obf_nonlinear/line_0000949` collapses to `6 * y` (cost `3`) and replays as `proved_compositional`.
   - `mba_obf_nonlinear/line_0000911` collapses to `11 * y` (cost `3`) and replays as `proved_compositional`.

---

## 5. Complement-Offset Peepholes + Additive Linear-Residual Decomposition (`src/greysynth/normalization.ml`)

The remaining `pldi_nonpoly` weak cases (e.g., `line_0000984` `GT: x * ~y`, `line_0000938` `GT: y * (x - 3)`) contain `~((x * y) - 1)` and `~(~((y * x) - 1))` mixed with a 2-variable linear MBA in `(x, y)`.

**Deliverables:**
1. Add exact, bitwidth-safe two's-complement peephole identities (proof-gated as usual):
   - `~(a - 1)` / `~(a + (-1))` -> `-a`
   - `~(-a)` -> `a - 1`
   - `(-a) - 1` / `(-1) - a` -> `~a`
   - `~a + 1` -> `-a`
2. Ensure additive sums mixing opaque nonlinear terms (like `-(x * y)`) with linear-MBA terms in `(x, y)` partition out the linear-MBA terms in `(x, y)`, simplify them (e.g., to `-x`), and let `factor_group_candidate` factor `-(x * y) - x` -> `x * (~y)` (or `x * y - 3 * y` -> `y * (x - 3)`)!
3. **Focused regression tests (`test/normalization_test.ml`):**
   - `pldi_nonpoly/line_0000984` collapses to `x * (~y)` (cost `<= 6`) and replays as `proved_compositional`.
   - `pldi_nonpoly/line_0000938` collapses to `y * (x - 3)` (cost `<= 6`) and replays as `proved_compositional`.

---

## 6. Sanitized Full-Loki Copy (Benchmarking Only — Never Mutate Upstream!)

Do **NOT** modify `C:\CodeBlocks\ProMBA\loki_benchmark\backup\floki.txt` or weaken GreySynth's expression parser.
Instead, for clean Full-Loki measurement alongside the raw file, generate `/tmp/greysynth-bench/external/floki_sanitized.txt` by stripping only the stray leading `}` on the 249 `}`-prefixed rows (and logging the exact line numbers and unmatched-paren final row count) so we can report BOTH:
- raw `floki.txt` (250 valid rows, exact upstream denominator), and
- sanitized `floki_sanitized.txt` (499 valid rows, showing true solver performance on Full-Loki).

---

## 7. Verification Gate for Round 18

1. Run `devcontainer exec --workspace-folder . make test` — 100% green.
2. Verify all targeted failure cohorts first (fast smoke checks):
   - All **13** previously-crashing `PLDI Poly` `Z.Overflow` rows -> **0 errors**, 13/13 proved!
   - The previously-regressed `Loki` (`993`, `548`, `792`), `Full-Loki` (`433`, `371`), and `QSynth EA` (`163`, `393`, `288`) rows -> all collapse cleanly and replay!
   - The targeted `mba_obf_linear` (`788`, `973`), `mba_obf_nonlinear` (`949`, `911`), and `pldi_nonpoly` (`984`, `938`) rows -> all collapse to `<= GT` and replay!
3. Re-run the **full 8-dataset AFTER audit** (7,011 rows, identical 5s/20s budget at 8 workers, plus `floki_sanitized.txt` 499 rows!) and update `docs/FULL_AUDIT_REPORT.md` with a **BEFORE (`ec490c7`) vs. R17 (`196dacb`) vs. R18** comparison table!
4. Run a quick **C-Full / Tigress L5** sanity check (confirm zero regressions on our 1,000-case gate or targeted contention cases).
5. Commit the code/test fixes cleanly (do NOT touch `docs/neon-review*.md` or `docs/SIMPLIFICATION_WINS.md`).
