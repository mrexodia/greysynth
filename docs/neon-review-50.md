# GreySynth Round-50 Spec: Restore `16_384` Normalization Cap & Pipeline Order + Milestone-50 Honest Held-Out Evaluation (`mba-balanced-v1`)

**Baseline:** Round 49 (`9a3d894` / `3ec7c0f` — MASSIVE zero-SMT wins: `core_hard` **`25 -> 66` exact `<= GT` (`+41`!)** led by `pldi_poly` `+17`, `qsynth_ea` `+8`, `omvll` `+6`, `mba_flatten` `+5`, `c_mba_obfuscator` `+5`; shrunk `Tigress L5` **`45 -> 56` (`+11`!)** pushing overall `Tigress L5` past `80%`; Leeky `dev_64` **`462 -> 501` exact (`2.35x -> 2.02x`)** with `mba-proof-context-v1` `1.58x -> 1.02x`, `mba-extra-floor-v1` `1.46x -> 1.08x`, `mba-majority-v1` `1.38x -> 1.09x`, `mba-stress64-v1` `11.26x -> 5.74x`; `0` refutations across all 1,539 cases!).

**Zero proof-kernel changes required in Round 50** (`src/proof/rewrite_proof.ml` stays untouched!).

**Forensic Diagnosis of Round 49's ONLY Two Regressions (Both Are Exact 1-Line Fixes!):**

1. **`Tigress L5–L8` (`core_hard` `tigress_lvl_5..8` + `regression_smoke` `tigress_lvl_8__target_1016: 9 -> 13,466`):**
   - Look at `src/greysynth/normalization.ml:705` in `9a3d894`:
     `linear_decomposed` cap was lowered from `16_384` down to `512`!
   - Every single regressed Tigress case (`target_375` size `4229: 5 -> 4229`, `target_1514` size `9283/12240: 126 -> 9283`, `target_6350` size `4747: 5 -> 407`, `target_6909` size `4229: 5 -> 349`, `target_5339` size `6321: 5 -> 50`, `target_1016` size `13466: 9 -> 13466`) had size in **`513..16,384`** and lost `normalize-linear-mba`!
   - Also check `tigress_lvl_8__target_1562` (`933,923: R48=4872 -> R49=933923`) and `tigress_lvl_8__target_1461` (`1,390,360: R48=77245 -> R49=1390360`) — verify why those two giant DAGs regressed between R48 and R49 (check `contains_probe_shell` / `has_bitwise_operator` or `linear_candidates_with_rings` scan limit `64 -> 256`) and restore them cleanly!
2. **`mba-projection-v1` (`51/54` baseline -> `44/54` in R49, `1.14x -> 1.39x`):**
   - In `9a3d894`, `run_small_dag ()` ran **BEFORE** `run_root_minterm_poly`, `run_root_disjoint_components`, `run_root_linear_group`, and `run_root_polysim_poly`!
   - On 10–18-variable `mba-projection-v1` cases (`size 55..327`, e.g., `208deb497106ed9f_w64: 55 -> 11` baseline vs `42` in R49), running `dag_bottom_up_simplify` first partially rewrote subtrees and disrupted the outer structure that `run_root_disjoint_components` / `run_root_linear_group` previously collapsed directly to exact reference size!

---

## 1. Three Surgical Fixes (Zero Proof-Kernel Edits!)

1. **Restore `16_384` Cap in `src/greysynth/normalization.ml:705`:**
   - Change `cost !current > 512` back to `cost !current > 16_384` (since Round 49's true-boundary-overlap gate already restored 1x CPU speed for non-overlapping expressions!).
   - Verify `tigress_lvl_8__target_1016` (`-> <= 13`), `tigress_lvl_6__target_375` (`-> 5`), `tigress_lvl_5__target_6350` (`-> 5`), and `tigress_lvl_8__target_1562` / `target_1461` recover completely!
2. **Move `run_small_dag ()` After Root Decidable Passes in `src/greysynth/greysynth.ml`:**
   - Move the first `run_small_dag ()` call from line 584 (before `run_root_minterm_poly`) to **right AFTER `run_root_correlated_null ()`** (right before the `size > 256 || input_dag_size > 128` `dag_bottom_up_simplify` block!).
   - Keep the second `if size_of_expr !best > 7 then run_small_dag ()` call right after `Normalization.run`!
   - That way `run_root_minterm_poly`, `run_root_polysim_poly`, `run_root_disjoint_components`, and `run_root_linear_group` see the clean original root FIRST (restoring `mba-projection-v1` `44 -> 51/54`!), and EVERY expression that still has `15 <= size <= 512` afterward still gets the full 4-round zero-SMT `run_small_dag ()` pass (preserving ALL of R49's massive gains on `pldi_poly`, `qsynth_ea`, `omvll`, `mba_flatten`, `mba-majority-v1`, `mba-proof-context-v1`, and `mba-extra-floor-v1`!).
3. **Raise `scan_count` Limit in `src/greysynth/norm_linear.ml` (`64 -> 256`):**
   - Raising `!scan_count < 64` to `!scan_count < 256` catches compound-atom boundary overlaps on larger roots (`1,000–16,384` nodes) while staying well under `0.1 ms`!

---

## 2. Verification Gate + Milestone-50 Honest Held-Out Evaluation (`--workers 8`, RAM < 30 GB!)

1. **Regression Tests (`test/round50_test.ml`):**
   - Verify full-pipeline recovery on:
     - `tigress_lvl_8__target_1016` (`-> <= 13`)
     - `tigress_lvl_6__target_375` (`4229 -> 5`)
     - `mba-projection-v1` `208deb497106ed9f_w64` (`55 -> 11`)
   - Keep all `round49_test.ml` tests green; run `make test` warning-clean, **zero edits to `src/proof/rewrite_proof.ml`!**
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, retain `/tmp/r50-*/out.jsonl`):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r50-smoke/out.jsonl`): **target `62/62` strict decreases, `>= 54/58` exact, `<= 0.80x` (ideally new all-time record `<= 0.78x`!), `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r50-leeky-dev64/out.jsonl` — target: `>= 508/880` exact hits, geomean **`<= 1.95x`** with `mba-projection-v1` restored to `~50–51/54`!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r50-l5/out.jsonl` — target: **`>= 58/251` exact `<= GT`, geomean `< 5.8x`**!)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r50-core/out.jsonl` — target: **`>= 70/341` exact `<= GT`, geomean `< 4.3x`**!)
3. **MILESTONE-50 HONEST OUT-OF-DISTRIBUTION HELD-OUT EVALUATION (`datasets/leeky/adapted/heldout_balanced64/`, `120` cases -> `/tmp/r50-leeky-heldout/out.jsonl`):**
   - **ANTI-OVERFITTING RULE (STRICT!):** Do **NOT** inspect individual expressions in `heldout_balanced64` and do **NOT** tune anything based on its output! Run it **ONCE**, purely at the end after code is frozen, and report ONLY aggregate metrics vs the R44 zero-tuning baseline (`50/112` = `44.6%`, `2.26x`, `111/112` strict, `8/8` controls untouched, `0` refutations)!
4. Record concise Round-50 + Milestone-50 Held-Out results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
