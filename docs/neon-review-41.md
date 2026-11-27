# GreySynth Round-41 Spec: Eliminate R40 Budget/SMT Leaks + Unlock `515–2048`-Node Opaque Shells & Wide-Bitwidth (`96`/`224`-bit) MBAs

**Baseline:** Round 40 (`d972829` / `3bb642d` — `Tigress L5 all_non_exact` **`+207` exact GT, `3.54x`** (`450/450`, `0` stalls), refreshed `core_hard` **`+82` exact GT, `3.09x`** (`353/353` direct parallel), `Tigress L8` `41.13x`, `0` refutations).

**Forensic Diagnosis of R40 Regressions (`oses__line_0000240` `596 -> 564k`, `tigress_lvl_8__target_6503` `96 -> 5627`, `target_2790` `7 -> 310`, `target_1169` `474 -> 4731`, `target_126` `80 -> 445`, `target_3601` `80 -> 320`, `tigress_lvl_5__target_6370` `5 -> 53`, `qsynth_ea__line_0000458` `20 -> 139`) & Top Remaining `r40-l5` Cases:**

1. **Three tiny R40 budget/SMT leaks (100% root-caused!):**
   - **Leak A (`dag-product-peel` with non-empty `equalities` bypassed `zero_smt` & `smt_budget`!):** In `normalization.ml:86`, `nonlinear_product_identity_candidate` runs BEFORE `if not zero_smt` and passes `~equalities` straight into `Rewrite.accepts_compositional`! Whenever `uext`-lifting produced a non-empty `equalities` list, `Rewrite_proof.verify` invoked Bitwuzla SMT with FULL `c_equiv_timeout` (`2.0s`) inside the `zero_smt = true` fast pass and without counting against `smt_budget`!
   - **Leak B (`probe_opaque_atoms` inside `dag_bottom_up_simplify` ran uncapped on every `9..256` node and skipped `samples_agree` pre-filter!):**
     - On `oses__line_0000240` (`candidates = 512, inconclusive = 307`), calling `probe_opaque_atoms` + `dag-semantic-probe-linear` + `dag-semantic-probe-semilinear` (neither counted in `smt_spent`!) on every intermediate node `9..256` blew the entire 5.0s timeout!
     - On `target_2790` (`sample_rejections: 5 -> 52`) and `target_3601` (`4 -> 34`), false-positive abstract 16-sample hits weren't pre-filtered by `Rewrite.samples_agree` once inside `probe_opaque_atoms`, causing triple `samples_agree` rejections across `linear` / `semilinear` / `smt`!
   - **Leak C (`nonlinear_product_identity_candidate` ran `ring_polynomial_candidate` on huge nodes inside `zero_smt = true`):** On `> 4096`-cost nodes during the fast zero-SMT pass, skip the quadratic `ring_polynomial_candidate` algebraic-complement check (it's only needed once nodes are `<= 4096`!).
2. **Two huge, 100%-general wins spotted in the Top-12 remaining `r40-l5` cases:**
   - **Root `probe_opaque_atoms` capped at `cost <= 512` (`target_6350` `515 -> 5`, `target_1596` `524 -> 9`, `target_5472` `556 -> 9`, `target_1803` `765 -> 9`):**
     - `target_6350` (`out = 515`) and `target_1596` (`out = 524`) are **literally** 2-atom bitwise/shift MBA shells over `P_cross` and `P_reg` (`((P_cross | P_reg) << 1) - (P_cross ^ P_reg) == P_cross + P_reg == A * B`), just `3` and `12` nodes over the `512` cap!
     - Raising `probe_opaque_atoms` root cost limit to **`2048`** (while keeping `dag_size_bounded ~limit:256 expression <= 256`!) + running a follow-up `nonlinear_product_identity_candidate` peel when a root probe fires collapses BOTH straight to exact GT!
   - **Wide-bitwidth (`96`/`128`/`224`-bit) sampling in `probe_opaque_atoms` (`target_4543/4537/4554/4493` `<224>`, `target_1803/1776/930/5472` `<96>`):**
     - Generate full `width`-bit independent sample values (spanning all `width` bits, not only low 64 bits!) so wide-bitwidth expressions get accurate full-width filtering and exact abstract candidates!
   - **`uext(k)` constant-mask lifting in `nonlinear_product_identity_candidate` (`target_2923` `412 -> 5`):**
     - Match `uext(k) (x & C_low)` as `(uext(k) x) & uext(k)(C_low)` AND `uext(k) (x & ~C_low)` as `(uext(k) x) & ~(uext(k) C_low)` (true because the top `k` bits of `uext(k) x` are `0`!), proved by the same tiny 1-var abstract bridge equality (gated on `not zero_smt` + `try_smt`)!

---

## 1. Fix R40 Budget, `zero_smt`, & Pre-Filter Leaks (`src/greysynth/normalization.ml`, `src/greysynth/norm_probes.ml`, `src/greysynth/norm_semilinear.ml`)

1. **Enforce strict `zero_smt` & `smt_budget` gating on `dag-product-peel` (`src/greysynth/normalization.ml`):**
   - In `dag_bottom_up_simplify`: if `nonlinear_product_identity_candidate` returns `equalities = []`, run it freely even when `zero_smt = true`.
   - If `equalities <> []` (SMT-backed bridge like `uext`-lifting), **ONLY** run it when `not zero_smt` AND wrap `Rewrite.accepts_compositional` inside `try_smt` so its wall time is charged against `smt_budget` (and never runs once `!smt_spent >= smt_budget`)!
   - In `nonlinear_product_identity_candidate` (`norm_semilinear.ml`): skip the `ring_polynomial_candidate` algebraic-complement check when `cost expression > 4096` (keeping giant-node zero-SMT peeling instant!).
2. **Eliminate false-positive sample rejections & cap `dag_bottom_up_simplify` opaque-probe overhead (`src/greysynth/norm_probes.ml`, `src/greysynth/normalization.ml`):**
   - Inside `probe_opaque_atoms`:
     - Use **full `width`-bit** deterministic independent samples (`24` samples covering low, mid, and high bits up to `width` bits for `96`/`128`/`224`-bit expressions!).
     - Filter restored concrete candidates with `Rewrite.samples_agree expression candidate` **ONCE** before returning `Some candidate`! (Eliminates all duplicate `sample_rejections` across `linear` / `semilinear` / `smt`!)
   - Inside `dag_bottom_up_simplify`:
     - Only invoke `probe_opaque_atoms` when `not minimal && not zero_smt && !smt_spent < smt_budget && cost !result >= 9 && cost !result <= 256` AND track `opaque_probe_calls = ref 0` with a hard cap of **`<= 16` probe calls per `dag_bottom_up_simplify` invocation** (skipping nodes that don't contain any bitwise/shift op)!
     - Inside `accept_probe`: ONLY attempt `dag-semantic-probe-semilinear` when `!result` or `candidate` actually contains a constant mask, `Lsl`, or `Uext`/`Restrict` (avoiding wasted certificate serialization + `inconclusive` counts on pure linear or non-semilinear shift-carried MBAs!).
     - Ensure `probe_opaque_atoms` inside `dag_bottom_up_simplify` uses `~timeout:0.15` inside `try_smt` (leaving budget for root probes & later passes!).

---

## 2. Unlock `515–2048`-Node Root Opaque Shells (`target_6350`, `target_1596`, `target_1803`, `target_5472`) + `uext` Constant-Mask Product Peeling (`target_2923`)

1. **Raise root `probe_opaque_atoms` cost cap to `2048` (`src/greysynth/norm_probes.ml`, `src/greysynth/greysynth.ml`):**
   - Parameterize `probe_opaque_atoms ?(max_cost = 512) cost expression` (still keeping `dag_size_bounded ~limit:256 expression <= 256`!).
   - In `run_root_semantic_probes` (`greysynth.ml`), allow `probe_opaque_atoms ~max_cost:2048 size_of_expr !best` even when `size_of_expr !best` is between `257` and `2048` (as long as `dag_size_bounded ~limit:256 !best <= 256`!).
   - Whenever `run_root_semantic_probes` accepts a strictly smaller candidate, immediately run a single `nonlinear_product_identity_candidate` peel + `run_root_semilinear` check on `!best` (so `target_6350`: `515 -> P_cross + P_reg -> 5` and `target_1596`: `524 -> P_cross + P_reg -> 9` collapse in ONE shot!).
   - Also run `run_root_semantic_probes` **one more time** right before `run_cleanup` / after `dag_bottom_up_simplify` + `oes` if `size_of_expr !best` shrank into `[9, 2048]` with `dag_size <= 256` and `!g_has_timedout` is false!
2. **`uext(k)` constant-mask lifting in `nonlinear_product_identity_candidate` (`src/greysynth/norm_semilinear.ml`):**
   - Handle `uext(k) (x & C_low)` matching `(uext(k) x) & uext(k)(C_low)` AND `uext(k) (x & ~C_low)` matching `(uext(k) x) & ~(uext(k) C_low)` (with the single tiny 1-var abstract bridge equality in `equalities`, gated on `not zero_smt` + `try_smt`).
   - Immediately solves `target_2923` (`412 -> 5` exact GT!).

---

## 3. Verification Gate for Round 41 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round41_test.ml`):**
   - End-to-end tests with independent `mba_proof` replay covering:
     - `target_6350`-style `> 512`-cost (`dag <= 256`) bitwise/shift shell over `(P_cross, P_reg)` -> `P_cross + P_reg -> A * B` (exact GT `5`!)
     - Wide-bitwidth (`96`-bit / `224`-bit) `probe_opaque_atoms` recovery with full-width sampling!
     - `target_2923`-style `uext(32)` constant-mask product peel `((uext(32) (x0 & 0xfffe24bd)) * (0x1db42 & ~(uext(32) x0))) + ((uext(32) (0x1db42 & x0)) * (0x1db42 | (uext(32) x0))) -> (uext(32) x0) * 0x1db42`!
     - Strict `zero_smt` non-invocation check: `dag_bottom_up_simplify ~zero_smt:true` executes **0** SMT calls even on `uext`-lifted product expressions!
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r41-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` cases — target: push exact GT past **`225+`** and geomean below **`3.0x`**!)
   - **`datasets/hard_cases/core_hard/`** (`353` cases — target: recover ALL R40 regressions (`target_2790`, `6503`, `126`, `3601`, `1169`, `6370`, `qsynth_ea__458`) AND push exact GT past **`90+`** and overall geomean well below **`2.5x`**!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — MUST recover `oses__line_0000240` (`0` `in == out` stalls!), `62/62` established, `0` refuted, **`<= 0.83x`**!)
3. Record concise Round-41 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `src/proof/rewrite_proof.ml`).
