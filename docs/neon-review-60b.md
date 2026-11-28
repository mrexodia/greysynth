# GreySynth Round-60B Spec: Full Corpus Prune Sweep #4 (`1,364` Remaining `all_non_exact` Rows) + Milestone-60 Strictly Held-Out Check (`mba-balanced-v1`, Aggregate-Only)

**Binary Under Test:** Unchanged Round-60 HEAD (`08e379d2` — stacking 7 clean, 100% general rounds R54–R60 since Round 53B's Prune Sweep #3: zero-SMT `gf2_masked_xor_equal` proof-kernel fast path, sound repeated-dead subterm abstraction, universal `1.2s` prepass with pure-linear guard, zero-recursion `lowk` dead-branch annihilation, full `run_preprocessing` & `dag_bottom_up_simplify` timeout partial-work preservation + `dag-bitwise-ac <= 32` call cap, universal `c + c * B -> (-c) * (~B)` constant absorption, and exact 2-var `{x, y, x | y}` / `{x, y, x & y}` linear bases).

**STRICT RULES FOR ROUND 60B:**
1. **NO source or test edits!** Audit the unchanged `08e379d2` binary only.
2. **RAM < 30 GB:** Always use `--workers 8`, exact R18 config (`/tmp/greysynth-bench/full-audit-after-config.json`), independent `mba_equiv` + `mba_proof` replay (`--timeout 30 --samples 256 --smt-timeout 2 --proof-timeout 5 --proof-process-timeout 90 --check-ground-truth`).
3. **STRICT HELD-OUT DISCIPLINE:** For `datasets/leeky/adapted/heldout_balanced64/` (`mba-balanced-v1`, 120 cases), report **ONLY aggregate statistics** (established, refutations, timeouts, controls untouched, transformed strict reductions, transformed reference hits, transformed geometric quality). **NEVER inspect, print, or tune on ANY individual expression, ID, or certificate from `heldout_balanced64/`!**

---

## Step 1: Audit All Remaining `all_non_exact` Suites (Reuse `/tmp/r60-l5/out.jsonl` for `tigress_l5`!)

We ALREADY have `/tmp/r60-l5/out.jsonl` (`170/170` proved & strict, `5/170` exact, `11.5052x`, `0` refutations) from the exact `08e379d2` binary! Run the remaining `1,194` rows in 4 parallel batches:
1. `datasets/hard_cases/all_non_exact/tigress_l6` (`171` rows) -> `/tmp/r60b-l6/out.jsonl` (certs `/tmp/r60b-l6-certs`)
2. `datasets/hard_cases/all_non_exact/tigress_l7` (`205` rows) -> `/tmp/r60b-l7/out.jsonl` (certs `/tmp/r60b-l7-certs`)
3. `datasets/hard_cases/all_non_exact/tigress_l8` (`248` rows) -> `/tmp/r60b-l8/out.jsonl` (certs `/tmp/r60b-l8-certs`)
4. All 12 non-Tigress remaining suites (`570` rows — stage symlinks/copies of the 12 non-Tigress subdirectories of `datasets/hard_cases/all_non_exact/` in `/tmp/r60b-other-input`, excluding `tigress_l5/l6/l7/l8`) -> `/tmp/r60b-other/out.jsonl` (certs `/tmp/r60b-other-certs`)

---

## Step 2: Milestone-60 Strictly Held-Out Evaluation (`mba-balanced-v1`, Aggregate-Only!)

- Audit `datasets/leeky/adapted/heldout_balanced64/` (`120` cases: `112` transformed + `8` controls) with the exact same `--workers 8` R18 command -> `/tmp/r60b-heldout-balanced64/out.jsonl` (certs `/tmp/r60b-heldout-balanced64-certs`).
- Compare aggregate-only metrics against our two previous honest checkpoints:
  - **R44 Zero-Tuning Baseline:** `120/120` proved, `0` refutations, `8/8` controls, `111/112` strict, `50/112` (`44.6%`) exact, `2.2599x` geomean
  - **Milestone-50:** `119/120` proved (`1` timeout), `0` refutations, `8/8` controls, `51/112` exact, `1.8835x` geomean
  - **Milestone-53:** `120/120` proved, `0` refutations, `0` timeouts, `8/8` controls, `111/112` strict, `52/112` (`46.4%`) exact, `1.7091x` geomean
  - **Milestone-60 (NEW!):** Report exact aggregate-only numbers!

---

## Step 3: Rebuild `datasets/hard_cases/` & Record Authoritative Corpus-Wide Scoreboard

- Verify **ZERO refutations** and **100% established** across all 5 sweep files (`/tmp/r60-l5`, `/tmp/r60b-l6`, `/tmp/r60b-l7`, `/tmp/r60b-l8`, `/tmp/r60b-other`) and `/tmp/r60b-heldout-balanced64`.
- Run `scripts/build_hard_dataset.py` with ALL 19 previous overlays PLUS the 5 new Round-60B overlays:
  - Previous 19:
    `/tmp/r34-all-failing/out.jsonl`, `/tmp/r34-all-failing-isolated/out.jsonl`, `/tmp/r34-untested-non-exact/out.jsonl`, `/tmp/r34-untested-non-exact-isolated/out.jsonl`,
    `/tmp/r43-l5/out.jsonl`, `/tmp/r43-l6/out.jsonl`, `/tmp/r43-l7/out.jsonl`, `/tmp/r43-l8/out.jsonl`, `/tmp/r43-other/out.jsonl`,
    `/tmp/r51-l5/out.jsonl`, `/tmp/r51b-l6/out.jsonl`, `/tmp/r51b-l7/out.jsonl`, `/tmp/r51b-l8/out.jsonl`, `/tmp/r51b-other/out.jsonl`,
    `/tmp/r53-l5/out.jsonl`, `/tmp/r53b-l6/out.jsonl`, `/tmp/r53b-l7/out.jsonl`, `/tmp/r53b-l8/out.jsonl`, `/tmp/r53b-other/out.jsonl`
  - New 5:
    `/tmp/r60-l5/out.jsonl`, `/tmp/r60b-l6/out.jsonl`, `/tmp/r60b-l7/out.jsonl`, `/tmp/r60b-l8/out.jsonl`, `/tmp/r60b-other/out.jsonl`
- Verify the rebuilt `datasets/hard_cases/manifest.json` (total audited `54,105`, malformed `3`, giant GB `7`, proved `54,095`, refuted `0`, updated exact `<= GT`, `<= 1.25x`, `<= 1.50x`, `<= 2.00x`, shrunk `all_non_exact`, refreshed `core_hard`, `untested_non_exact: 0`, `regression_smoke: 62`).
- Record a crisp **Round-60B Prune Sweep #4 & Milestone-60 Held-Out** section in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (only `docs/IMPLEMENTATION_RESULTS.md` — keep `datasets/` gitignored, do NOT edit `src/`, `test/`, or `docs/neon-review*.md`!).
