# GreySynth Round-49 Spec: True-Overlap Dual-Boundary Gate (Zero CPU Bloat!) + Small/Medium Zero-SMT DAG Pass (Unlocks `mba-majority-v1`, `mba-proof-context-v1`, `mba-extra-floor-v1` & Restores `regression_smoke <= 0.795x`!)

**Baseline:** Round 48 (`26db844` / `2364e37` — shrunk `Tigress L5` **`+45 / 251` exact `<= GT`, `6.55x`**, refreshed `core_hard` **`+25 / 341`, `5.36x`**, `mba-stress64-v1` `0 -> 5/96`, `mba-long-frontier-v1` `39 -> 41`, `0` refutations across all 1,539 cases).

**Zero proof-kernel changes required in Round 49** (`src/proof/rewrite_proof.ml` stays untouched!).

**Forensic Diagnosis of Round 48's TWO Exact Blockers (100% Pinpointed!):**

1. **Why `regression_smoke` (`0.7921x -> 0.9590x`), `oses__line_0000240` (`1355 -> 564134`), `tigress_lvl_6__target_3259` (`7 -> 195`), `multivariate64__line_0000002` (`3 -> 2403`), and `mba-frontier64-v1` (`16.05x -> 22.91x`) slowed down:**
   - In `src/greysynth/norm_linear.ml` lines 668–677 (`26db844`), whenever `Nodes.length bitwise_linear_atoms > 0`, Round 48 ran `linear_candidates_with_rings` **THREE TIMES (`3x`!)** per DAG node (`bitwise_stops=true`, `bitwise_stops=false`, AND `compatible ~ring_bridges:false ~bitwise_stops:false`)!
   - Worse, `Nodes.length bitwise_linear_atoms > 0` fires even when a compound `+`/`-`/`*` inside `&` **NEVER appears in linear position** (e.g. `((x0 + x1) & x2) + x3`), where `bitwise_stops=true` and `bitwise_stops=false` are **100% identical**! That wasted **3x CPU** on ~90% of DAG nodes across the entire corpus!
   - In addition, `dag-bitwise-ac` (`recursive_bitwise_ac_candidate`) ran unconditionally on every DAG node up to cost `512` (even pure-polynomial or giant-DAG nodes!).
2. **Why `mba-majority-v1` (`23bc7e4239e647a2_w64`, `in=89 -> out=65`), `mba-proof-context-v1` (`26d6be2a86f9fc4a_w64`, `in=87 -> out=66`), and `mba-extra-floor-v1` (`ad964e0b66737fef_w64`, `in=216 -> out=69`) did NOT fire in Round 48:**
   - Proof certificate trace of all three cases revealed `dag_bottom_up_simplify` **NEVER EVEN RAN ON THEM**!
   - Look at `src/greysynth/greysynth.ml` line 566: `if (size_of_expr !best > 256 || input_dag_size > 128) && input_dag_size <= 2048`!
   - Because all three cases had `size <= 256` and `dag_size <= 128`, they completely skipped `dag_bottom_up_simplify` (and thus skipped `dag-bitwise-ac`, `dag-disjoint-sum-xor`, `dag-semilinear-mba` with opaque atoms, `dag-linear-mba`, and `dag-ring-mod2w`!).

---

## 1. True-Boundary-Overlap Gate & 1x-CPU Fast Path in `src/greysynth/norm_linear.ml` and `src/greysynth/normalization.ml`

1. **In `src/greysynth/norm_linear.ml` (`linear_candidates_with_rings`):**
   - During `scan_linear` / `scan_bitwise`, track BOTH:
     - `bitwise_linear_atoms`: compound linear-position subterms (`canonical_ac_atom`) seen inside `&`, `|`, `^`, `~`, AND
     - `linear_candidates_seen`: compound linear-position subterms (`canonical_ac_atom`) seen directly in linear position (outside bitwise ops!).
   - Define `has_boundary_overlap`: true **ONLY** if at least one key in `bitwise_linear_atoms` is ALSO in `linear_candidates_seen`!
     - (Wait: also check `extract_product_scalar` bases in `scan_linear` when `E.Mul` is non-constant, so `a * (k * b)` matches `a * b` in `bitwise_linear_atoms`!)
   - If `not has_boundary_overlap`: **do NOT stop at `bitwise_linear_atoms` and do NOT run a second pass!** (~90% of nodes drop from **3x CPU back to 1x CPU** at ZERO loss of algebraic power!)
   - When `bitwise_stops && has_boundary_overlap`:
     1. Run `bitwise_stops = true` (`proposals`).
     2. **ONLY** run `standard` (`~bitwise_stops:false ~ring_bridges`) if `proposals = []` OR the cheapest candidate in `proposals` has `cost > 7`!
     3. **NEVER** run `compatible` (`~ring_bridges:false ~bitwise_stops:false`) unconditionally — ONLY fall back to it if `proposals @ standard = []` (or inside `with Too_complex ->`)!
2. **In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`):**
   - Scope `dag-bitwise-ac` (`recursive_bitwise_ac_candidate`) so it ONLY runs right **before `ring_polynomial_candidate`** (and ONLY when `!result` has top operator `E.Plus | E.Minus | E.Mul` with `cost !result <= 256` and contains at least one bitwise operator `& | ^`), NOT on every non-ring node or giant DAG!
   - Also check `multivariate64__line_0000002` (`in=2403`), `oses__line_0000240` (`in=564134`), and `tigress_lvl_6__target_3259` (`in=39055`) directly! Specifically inspect why `multivariate64__line_0000002` regressed from `3` (R46) to `2403` (R47/R48) and fix the exact root cause so **`regression_smoke` passes `62/62` strict decreases, `>= 54/58` exact, `<= 0.795x`** under `--workers 8`!

---

## 2. Fast Zero-SMT `dag_bottom_up_simplify` Prepass for Small/Medium Expressions (`15 <= size <= 512`) in `src/greysynth/greysynth.ml`

1. In `run_preprocessing` (`src/greysynth/greysynth.ml`):
   - For ANY expression with `size_of_expr !best >= 15 && size_of_expr !best <= 512 && dag_size_bounded ~limit:512 !best <= 512` (and `not !g_has_timedout`):
   - Run a fast **zero-SMT** `Normalization.dag_bottom_up_simplify ~zero_smt:true ~minimal:false ~deadline:(Unix.gettimeofday () +. 0.25) !best` loop (up to **4 rounds**, continuing while `size_of_expr after < size_of_expr before || not (Sexpr.Expr.is_equal after before)` — stopping immediately on fixed point!).
   - Run this **once before `run_root_minterm_poly`** (takes `< 5 ms` on typical size-80..250 expressions, **0 SMT calls!**), AND **once more right after `Normalization.run`** if `size_of_expr !best >= 15 && size_of_expr !best <= 512` and `!best` is not already tiny (`size > 7`)!
2. **Verify end-to-end (full `run_preprocessing` + `Normalization.run`, NOT isolated helpers!) on the ACTUAL three diagnostic shapes:**
   - **`mba-majority-v1` (`23bc7e4239e647a2_w64`, `in = 89`):**
     Verify that `dag-bitwise-ac` + `dag-ring-mod2w` inside the zero-SMT small/medium DAG pass collapses `(M1 + ((M1 + x2) * (x1 + x2))) - (((M2 + (x1 + x2)) * x2) + (M2 * x1))` to `M` (full expression `89 -> <= 15` in `< 0.1s`, ZERO SMT)!
   - **`mba-proof-context-v1` (`26d6be2a86f9fc4a_w64`, `in = 87`):**
     Verify that `dag-disjoint-sum-xor` rewrites `((x0 ^ x1) & x2) + (x0 & x1) -> ((x0 ^ x1) & x2) ^ (x0 & x1)` in Round 1, AND that `dag-linear-mba` (with AC `+` unification `M_xor + C == C + M_xor`) collapses `(((M_xor + C) & K) | ((C + M_xor) & ~K)) - C` to `M_xor` (full expression `87 -> <= 15` in `< 0.1s`, ZERO SMT)!
     - *(Double-check: if `((M_xor + C) & K) | ((C + M_xor) & ~K)` isn't simplified because `M_xor + C` and `C + M_xor` are inside `&` while `C` is subtracted outside, make sure `canonical_ac_atom` in `norm_linear.ml` unifies `M_xor + C` and `C + M_xor` inside `boolean` / `collect_bitwise` too — remember `M_xor + C` is a compound `+` atom inside `&`, so `norm_linear.ml` calls `canonical_ac_atom` on it!)*
   - **`mba-extra-floor-v1` (`ad964e0b66737fef_w64`, `in = 216`):**
     Verify that Round 1 collapses the inner linear sub-MBAs (`216 -> 69`) and Round 2's `dag-semilinear-mba` (with repeated opaque atoms `[B; A]`) collapses `(2 * ((B | 2) & A)) + (A ^ (B | 2)) - (B & ~2)` to **`A + 2`** (full expression `216 -> 11` in `< 0.1s`, ZERO SMT)!
     - *(Double-check: in `norm_semilinear.ml`, when `opaque_atoms = [B; A & x5; A; ...]`, verify `semilinear_mba_candidate_with_atoms ~opaque_atoms` actually produces `A + 2` — and check if `simple` variants include `variable + constant` for `constant = 2`! If `B & ~2` has constant `~2` while `B | 2` has constant `2`, both `2` and `~2` are in `constants` -> `A + 2` IS in `simple`! If `ad964e0b66737fef_w64` still doesn't collapse to `11` in the unit test, inspect and fix the exact reason before running the benchmarks!)*

---

## 3. Verification Gate for Round 49 (Target Wall Time: ~10–12 min!)

1. **End-to-End Pipeline Tests (`test/round49_test.ml`):**
   - Run the **FULL `Greysynth` pipeline** (NOT just helper functions!) on:
     1. Exact `23bc7e4239e647a2_w64` (`mba-majority-v1`, `89 -> <= 15`)
     2. Exact `26d6be2a86f9fc4a_w64` (`mba-proof-context-v1`, `87 -> <= 15`)
     3. Exact `ad964e0b66737fef_w64` (`mba-extra-floor-v1`, `216 -> <= 11`)
     4. `tigress_lvl_6__target_3259` (`39055 -> <= 7`), `multivariate64__line_0000002` (`2403 -> <= 3`), and `oses__line_0000240` (`564134 -> <= 1355`)!
   - All independently replayed by `mba_proof`, warning-clean `make test`, **zero edits to `src/proof/rewrite_proof.ml`!**
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain JSONLs under `/tmp/r49-*/out.jsonl`):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r49-smoke/out.jsonl`): **MUST PASS `62/62` strict decreases, `>= 54/58` exact, `<= 0.795x`, `0` refutations** before running the other 3 suites!
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases — **still keeping held-out `mba-balanced-v1` strictly untouched!** -> `/tmp/r49-leeky-dev64/out.jsonl` — target: **MASSIVE** jumps on `mba-majority-v1` (`34 -> ~50+`), `mba-proof-context-v1` (`12 -> ~32+`), `mba-extra-floor-v1` (`23 -> ~45+`), AND recovery of `mba-frontier64-v1` to `<= 16x`, pushing overall `dev_64` well under **`1.90x`** and **`520+ / 880`** exact hits!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r49-l5/out.jsonl` — target: **`50+` exact `<= GT`, geomean `< 6.0x`**!)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r49-core/out.jsonl` — target: **`28+` exact `<= GT`, geomean `< 5.0x`**!)
3. Record concise Round-49 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
