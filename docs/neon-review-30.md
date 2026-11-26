# GreySynth Round-30 Spec: Forensic Phase-Ordering & Budget Isolation Fix, `alt_MBA`-Aware Extraction & Giant-DAG Recovery

**Baseline:** Round 29 (Known-bits abstract interpretation, arity-budgeted truncation/dead-stub filtering, low-width ANF)  
**Forensic Motivation (exact regression timeline traced across R23–R28 on `regression_smoke/` and `core_hard/`):**

Tracing `regression_smoke/` across R23–R28 pinpointed **four exact, surgical phase-ordering / budget bugs** that ALSO froze the top 15 giant `Tigress L8` and `OMVLL` expressions in `core_hard/` (`1.3M–5.4M` nodes returning unchanged!):

| Case | Baseline | R23 | R24 | R25 | R28 | Exact Root Cause |
|---|---:|---:|---:|---:|---:|---|
| `tigress_l8/target_1016` | `10` | `64,058` | `64,058` | `1,324,003` | `1,324,003` | R23 ran heavy bottom-up DAG before cheap OES; R25 `run_root_semilinear` timed out on giant DAGs! |
| `mba_obfuscator/target_3218` | `5` | `5` | `5` | `54,904` | `54,904` | R25 `run_root_semilinear` burned the 5s budget before `minterm_poly`/`dag_bottom_up_simplify` ran! |
| `tigress_l5/target_366` | `11` | `14` | `23` | `50,187` | `21` | Same R25 `run_root_semilinear` budget burn + R24 premature early exit! |
| `pldi_nonpoly/line_0000895` | `5` | `5` | `5` | `5` | `593` | R28 `run_root_semantic_probes` ran BEFORE `dag_bottom_up_simplify` and hung Bitwuzla SMT for 5s on raw 593-node nonlinear MBA! |
| `msimba/line_0000191` | `5` | `5` | `11` | `11` | `11` | R24 `root_decidable_fast` early-exit (`<= 20`) skipped `Egraph`/`bitsliced` cleanup! |
| `neureduce/line_0000242` | `10` | `10` | `15` | `15` | `15` | Same R24 premature early-exit (`<= 20`) skipping final `Normalization`/`Egraph` cleanup! |

**Goal of Round 30:** Fix all four exact bugs + add `alt_MBA`-aware extraction tie-breaking (`SaMBA` / `bsc.md` §2.3.2), restoring `regression_smoke/` back to **`62/62` strict decreases and `~0.78x–0.90x` geomean (`~0` regressions!)** while simultaneously unlocking the 15+ frozen giant `Tigress L7–L8` / `OMVLL` expressions in `core_hard/` and keeping EVERY single Round 23–29 win (`Permutation64` `13/13`, `target_366` `3.4M -> 11`, `C-MBA`, `Loki`, `ObfuscatorX`, `SiMBA`, `OMVLL target_2558` `647 -> 3`)!

---

## 1. Fix All Four Forensic Phase-Ordering & Budget-Isolation Bugs (`src/greysynth/greysynth.ml`, `src/greysynth/normalization.ml`, `src/greysynth/oes.ml`)

1. **Guard `run_root_semilinear ()` strictly (Fixes R25 giant-DAG freeze on `target_3218`, `tigress_l8/1016`, `tigress_l5/366`, and 15 giant `core_hard` cases!):**
   - `semilinear_mba_candidate` MUST immediately bail out in $O(1)$ if:
     - `dag_size_bounded ~limit:1024 expr > 1024`, OR
     - `expr` contains NO non-uniform bitwise constant (so pure linear/polynomial MBAs like `target_3218` and `tigress_l8/1016` skip it in microseconds!), OR
     - `expr` has `> 6` opaque atoms (fail fast in the atom collector BEFORE allocating any evaluation tables!).
   - Also check `check_timeout ()` inside `semilinear_mba_candidate`'s loops and enforce a hard local `0.2s` budget so it can NEVER burn the 5-second case timeout!
2. **Move & Budget-Isolate `run_root_semantic_probes ()` (Fixes R28 freeze on `pldi_nonpoly/895`, `825`, `mba_flatten/1892`!):**
   - **Remove** the premature `run_root_semantic_probes ()` call *before* `dag_bottom_up_simplify` (line 304 of `greysynth.ml`)!
   - Only run `run_root_semantic_probes ()` **AFTER** fast decidable algebraic passes (`dag_bottom_up_simplify`, `run_root_polysim_poly`, `run_root_minterm_poly`, `run_root_semilinear`) have already had their chance to collapse algebraic structure constructively!
   - Guard `run_root_semantic_probes ()` with `dag_size_bounded ~limit:1024 !best <= 1024`, AND wrap its `Rewrite.accepts` call with a **strict branch-local timeout cap** (`c_equiv_timeout` / local `0.25s` timeout, clearing branch-local timeout cleanly if global budget remains, and NEVER handing raw nonlinear expressions with `size_of_expr > 256` to monolithic SMT unless a decidable rule or proof bridge already shrank it!).
   - Verify `omvll/target_2558` STILL collapses `647 -> 3` (since `dag_bottom_up_simplify` + `semilinear` shrink it first, then post-DAG `run_root_semantic_probes` collapses it cleanly!).
3. **Strict Local Timeout Cap inside `Oes.semantic_dag_cse_pass` (`src/greysynth/oes.ml`):**
   - Currently `semantic_dag_cse_pass` calls `Rewrite.accepts` using the default `1.0s` SMT timeout, allowing a single hard collision to blow past the `0.5s` pass deadline!
   - Cap each `semantic_dag_cse_pass` SMT attempt strictly (e.g. `<= 0.15s`, using fast decidable rules first) and bail cleanly when `Unix.gettimeofday () >= deadline`, never poisoning `!g_has_timedout`!
4. **Fix R24's Premature `root_decidable_fast` Early Exit (Fixes `msimba/191`, `msimba/47`, `neureduce/242`, `pldi_poly/992`!):**
   - Never skip `Egraph`/`Normalization`/`OES` cleanup merely because a root pass hit `size <= 20`!
   - Only trigger `root_decidable_fast` (skipping later passes) when:
     - `size_of_expr !best <= 3` (already minimal!), OR
     - `size_of_expr input >= 1000 && size_of_expr !best <= 20 && has_only_decidable_proof` AND the reduced expression has NO remaining non-uniform bitwise masks and NO unfactored multi-term linear subexpression (specifically preserving the `Permutation64` zero-SMT fast path on `line_0000003/6/10` while letting `msimba/191`, `neureduce/242`, and `pldi_poly/992` finish collapsing to `5`, `10`, `8`!).
5. **Cheap Zero-Seed DAG `OES` Pre-Pass for Giant Trees (`size_of_expr > 4096 && dag_size_of_expr <= 2048`):**
   - On giant shared trees like `tigress_l8/target_1016` (`1.32M` tree nodes, tiny DAG!), run ONE ultra-fast `Oes.linear_simplify ~seed:false` pass (`< 50 ms`, DAG-memoized!) BEFORE heavy multi-pass `dag_bottom_up_simplify`, so obvious duplicate/constant sub-DAGs collapse immediately before `dag_bottom_up_simplify` runs!

---

## 2. `alt_MBA`-Aware E-Graph Extraction Tie-Breaking (`SaMBA` / `bsc.md` §2.3.2, `src/greysynth/egraph.ml`)

Define `mba_alternation : Sexpr.Expr.t -> int` (DAG-memoized count of edges crossing between arithmetic `{+, -, *, neg, <<}` and bitwise `{&, |, ^, ~}`, per Eyrolles Def. 2.20 / `bsc.md` §2.3.2 / `SaMBA`):
- In `Egraph.compute_best` (`src/greysynth/egraph.ml`), when two expressions in an e-class tie on `cost` (and `nodes`), break ties in favor of **lower `mba_alternation`** before falling back to `E.compare`!
- This gently biases e-graph representatives toward pure arithmetic or pure bitwise forms (exposing further `ring_mod2w` / `poly_mod2w` / `linear_mba_mod2w` collapses on the next saturation round) without ever increasing AST cost!

---

## 3. Fast, Focused Verification Gate for Round 30 (Target Wall Time: ~5 min!)

1. **Regression Unit Tests (`test/round30_test.ml`):**
   - Explicitly test ALL previously regressed smoke cases end-to-end with independent `mba_proof` replay:
     - `mba_obfuscator/target_3218`: **`54,904 -> 5`** (GT 5!)
     - `pldi_nonpoly/line_0000895`: **`593 -> <= 5`** (GT 5!)
     - `msimba/line_0000191`: **`248 -> <= 5`** (GT 5!)
     - `tigress_lvl_7/target_1016`: **`264,797 -> <= 13`** (GT 13!)
     - `tigress_lvl_8/target_1016`: **`1,324,003 -> <= 13`** (GT 13!)
   - Plus confirm Round 23–29 flagship regressions ALL remain 100% green (`target_366` `3.4M -> 11`, `permutation64` `11,169 -> 19` zero SMT, `omvll/target_2558` `647 -> <= 7`)!
2. **Run `make test`** — 100% green.
3. **Curated Verification Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/regression_smoke/`** (62 cases) — **PRIMARY GOAL:** `62/62` established, **`62/62` strict decreases**, geomean back down from `2.31x` to **`~0.78x–0.90x`** (near-zero regressions vs stored isolated baselines)!
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases) — watch both **exact GT count** (pushing past `210+`!) and **geomean** (dropping sharply as the 15 frozen giant `Tigress L8` / `OMVLL` cases unlock!)!
   - Also run **`datasets/hard_cases/core_hard/` with `"pipeline_portfolio": true`** (optional side-by-side check if fast!) to see whether `pipeline_portfolio` pushes `core_hard` exact GT & geomean even further!
4. Record concise Round-30 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
