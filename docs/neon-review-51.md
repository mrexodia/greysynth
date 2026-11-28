# GreySynth Round-51 Spec: Unify R49+R50 Best-of-Both-Worlds + Seal `dag-lowk-homomorphism` Missing-Timeout Leak (`target_375`, `target_1514`, `target_1016`, `mba-projection-v1`!)

**Baseline:** Round 49 (`9a3d894`: `core_hard` **`66/341` exact**, `Tigress L5` **`56/251` exact (`6.51x`)**, `dev_64` **`501/880` exact (`2.02x`)**) + Round 50 (`edabe41`: Milestone-50 honest held-out `mba-balanced-v1` improved **`2.26x -> 1.8835x`** on 100% unseen expressions, `0` refutations across all 1,660 cases!).

**Zero proof-kernel changes required in Round 51** (`src/proof/rewrite_proof.ml` stays untouched!).

**Forensic Diagnosis of R49 vs R50 Ablation (100% Pinpointed!):**

1. **Missing `~timeout:0.15` Leak in `dag-lowk-homomorphism` (`src/greysynth/normalization.ml:185`):**
   - Inspecting the proof certificate of `tigress_lvl_6__target_375` (`R48: 4229 -> 5 in 5.51s` vs `R50: 4229 -> 4229 in 7.43s`!) showed **11 `dag-lowk-homomorphism` SMT calls** burning the entire `5.0s` hard timeout and discarding all 42 proved DAG steps!
   - Every other `try_smt` call in `dag_bottom_up_simplify` passes `~timeout:0.15` or `~timeout:0.25`, **EXCEPT `dag-lowk-homomorphism`**, which omitted `~timeout` and defaulted to the full multi-second `c_equiv_timeout` per call, blowing right past `smt_budget:1.0` AND `g_total_timeout:5.0`!
   - This single missing timeout caused the `Tigress L5–L8` `in == out` regressions (`target_375`, `target_1514`, `target_1461`, `target_6350`, `target_6909`)!
2. **Exact R49 vs R50 Ablation Lessons:**
   - Moving `run_small_dag ()` AFTER root passes in R50 cost **`-31` exacts on `core_hard`** (`pldi_poly` `17 -> 0`, `c_mba_obfuscator` `8 -> 2`, `mba_flatten` `5 -> 0`), `-12` exacts on `dev_64`, and `-5` exacts on `Tigress L5` — because `run_root_minterm_poly` / `run_root_polysim_poly` expanded expressions before `run_small_dag ()` simplified their bitwise/linear factors!
   - Conversely, `mba-projection-v1` (10–18 variables!) regressed (`51 -> 44`) ONLY because `run_small_dag ()` ran before `run_root_disjoint_components` / `run_root_linear_group` on high-arity (`> 8`-variable) expressions where `dag-linear-mba` (`max_atoms <= 6`) can't collapse the whole root anyway!
   - Raising `scan_count` `64 -> 256` in R50 caused `mba-frontier64-v1` to blow up `18.6x -> 47.1x` and caused 1 timeout on held-out! Keeping `scan_count = 64` avoids all of that overhead.

---

## 1. Three Surgical Fixes (Zero Proof-Kernel Edits!)

1. **Seal `dag-lowk-homomorphism` Timeout Leak (`src/greysynth/normalization.ml`):**
   - Pass **`~timeout:0.15`** to `Rewrite.accepts_compositional ~pass:"dag-lowk-homomorphism"` inside `dag_bottom_up_simplify`, gate it to `cost !result <= 256`, and cap `dag-lowk-homomorphism` SMT calls per `dag_bottom_up_simplify` pass at `<= 6` (using a local counter incremented when `lowk_restrict_homomorphism_candidate` returns `Some _`)!
   - Also inspect `tigress_lvl_8__target_1016` (`in=1,324,003`: `R46 = 9` vs `R50 = 13,422` in `regression_smoke`): check why it stopped at `13,422` under 8-worker load (compare `git diff 228b793..edabe41 -- src/greysynth/greysynth.ml src/greysynth/normalization.ml` on `target_1016`) and restore `tigress_lvl_8__target_1016 -> <= 13` so **`regression_smoke` hits `62/62` strict, `>= 54/58` exact, `<= 0.79x`**!
2. **Restore R49 Pre-Root `run_small_dag ()` with General `<= 8`-Variable Gate (`src/greysynth/greysynth.ml`):**
   - Move the first `run_small_dag ()` call BACK **before `run_root_minterm_poly`** (restoring `core_hard` `+31` exacts: `pldi_poly +17`, `c_mba_obfuscator +6`, `mba_flatten +5`, plus `Tigress L5` `56+` and `dev_64` `501+`!), **AND** guard the pre-root `run_small_dag ()` call with **`List.length (Sample_evaluator.variables_of_expr !best) <= 8`** (general arity guard: `dag-linear-mba` has `max_atoms <= 6`, so `> 8`-variable roots go to `run_root_disjoint_components` / `run_root_linear_group` first, restoring **`mba-projection-v1` `45 -> 51/54` (`1.13x`)**!).
   - Keep the post-`Normalization.run` `run_small_dag ()` call unchanged (with no variable-count limit, so any `> 8`-var expression that didn't collapse at root still gets cleaned up afterward!).
3. **Restore `scan_count < 64` in `src/greysynth/norm_linear.ml`:**
   - Change `!scan_count < 256` back to `!scan_count < 64` (immediately restores `mba-frontier64-v1` `47.1x -> <= 18.6x`, `mba-stress64-v1` `7.26x -> <= 5.74x`, and eliminates the R50 timeout!).
   - Keep R50's bounded `10_000` window in `normalization.ml` (`linear_decomposed`) and `early-pure-poly` in `greysynth.ml`!

---

## 2. Verification Gate for Round 51 (Target Wall Time: ~12 min!)

1. **Full-Pipeline Regression Tests (`test/round50_test.ml` / `test/round51_test.ml`):**
   - Verify full-pipeline recovery on:
     - `tigress_lvl_6__target_375` (`4229 -> <= 5`!)
     - `tigress_lvl_8__target_1016` (`1,324,003 -> <= 13`!)
     - `mba-projection-v1` `208deb497106ed9f_w64` (`55 -> <= 11`!)
     - `pldi_poly` exact case from `core_hard` (verifies `pldi_poly` stays at `17/25`!)
   - Run `make test` — warning-clean, 100% green, **zero edits to `src/proof/rewrite_proof.ml`!**
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r51-*/out.jsonl`, do NOT run `heldout_balanced64` in this round!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r51-smoke/out.jsonl`): **target `62/62` strict decreases, `>= 54/58` exact, `<= 0.795x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r51-leeky-dev64/out.jsonl` — target: **`>= 508/880` exact hits, geomean `<= 1.95x`**, `884/884` proved, `0` refutations, `mba-projection-v1` restored to `~50–51/54`!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r51-l5/out.jsonl` — target: **`>= 56/251` exact `<= GT`, geomean `< 6.0x`**!)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r51-core/out.jsonl` — target: **`>= 70/341` exact `<= GT`, geomean `< 4.4x`**!)
3. Record concise Round-51 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
