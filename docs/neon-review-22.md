# GreySynth Round-22 Spec: Provenance-Preserving Dataset Adapters, Proof-Gated Pipeline Portfolio & Final Polish

**Baseline commit:** `f9975cd` (Round 21 DAG-native & minterm-ring nonlinear MBA complete — `C-MBA-Obfuscator` jumped `17 -> 205` solved and `143.16x -> 9.58x`, `MBA-Obfuscator nonlinear` `0.7284x`, all 4 persistent Wave-1 Tigress timeouts recovered!)  
**Target:** Close the remaining syntax-boundary, phase-ordering portfolio, and residual polish targets from the ~80,000-expression audit:
1. **Explicit provenance-preserving source-language adapters** (eliminating ALL **579 systemic dialect syntax errors** across `xyntia/b2_combined` [318], `cobra/oses` [12], and `greysynth/floki` [249] WITHOUT mutating source datasets or weakening GreySynth's strict parser!).
2. **Proof-gated whole-pipeline portfolio (`"pipeline_portfolio": true`, opt-in)** to capture the best of both DAG-native e-graph and OES-first/standard preprocessing with strict proof-journal checkpointing and zero cross-branch proof leakage.
3. **Final check & polish on `datasets/cobra/obfuscatorx.txt` (7 rows)** (and quick verification that Rounds 19–22 leave `make test` and all smoke gates 100% green with 0 refutations).

---

## 1. Provenance-Preserving Dataset Dialect Adapters (`scripts/adapt_dataset.py`)

**Strict invariant:** Never mutate any file under `datasets/`, and NEVER weaken GreySynth's strict parser (`src/sexpr/string_to_sexpr.ml`). Instead, provide an explicit, auditable, deterministic preprocessing tool `scripts/adapt_dataset.py` that translates documented external benchmark dialects into GreySynth-native JSON/CSV inputs and writes a sibling `.provenance.json` manifest recording:
- Source path & SHA-256
- Output path & SHA-256
- Dialect rule name & exact per-row counts of transformations applied (plus sample before/after diffs)

**Supported explicit `--dialect` modes:**
1. `--dialect xyntia-shifts`:
   - Input: single-column expression file (e.g. `datasets/xyntia/b2_combined`, 1,110 rows).
   - Output: JSON directory or JSONL/JSON cases (`{obf_expr, bitwidth: 64}`) compatible directly with `scripts/audit_dataset.py`.
   - Exact token-level rewrite: infix `\blsl\b` $\to$ `<<` (159 rows) and `\blsr\b` $\to$ `>>` (159 rows), leaving all other tokens untouched.
2. `--dialect oses`:
   - Input: tab-separated OSES file (e.g. `datasets/cobra/oses/oses_all.txt`, 479 rows).
   - Output: CSV (`obf,gt`) compatible directly with `scripts/audit_dataset.py`.
   - Exact documented rewrites (recorded per row in provenance):
     - Strip unary `+` before constants/expressions when preceded by start-of-string, `(`, or an operator (e.g., `(+2*~x)` $\to$ `(2*~x)`).
     - Replace Python floor/integer division ` // ` $\to$ ` / ` (explicitly noted in provenance as unsigned bitvector division adapter on non-negative constant divisors `0x61`, etc.).
     - Replace indexed variable notation `X[0]` / `X[1]` / `X[2]` (`([A-Za-z_]\w*)\[(\d+)\]`) $\to$ `\1_\2` (e.g., `X_0`).
3. `--dialect floki-brace`:
   - Input: `datasets/greysynth/floki/mba_info` directory (500 JSON files).
   - Output: cleaned `mba_info` JSON directory where any `obf_expr` starting with a stray leading `}` (249 rows from the Zenodo extraction artifact) has that single leading `}` stripped, preserving `gt_expr`, `bitwidth`, and `target`.

**Deliverables:**
- `scripts/adapt_dataset.py` (clean stdlib-only Python 3 CLI with `--dialect`, `--input`, `--output`, `--bitwidth`).
- Unit tests (`scripts/test_adapt_dataset.py`, invoked in `make test` or verified via `python3 -m unittest scripts/test_adapt_dataset.py`) checking all 3 dialects, provenance SHA-256 recording, idempotence, and non-mutation of inputs.

---

## 2. Opt-In Proof-Gated Preprocessing Portfolio (`src/greysynth/config.ml`, `src/greysynth/greysynth.ml`, `test/pipeline_test.ml`)

Round 21 showed that DAG-native e-graph extraction dramatically cuts geometric quality on `C-MBA-Obfuscator` (`143.16x -> 9.58x`) and `Tigress L5` (`9.14x -> 8.53x`), while on a minority of Tigress/QSynth cases a fast OES-first + standard normalization run reaches a strictly smaller expression within the 5-second budget.

**Deliverables:**
1. Add opt-in config knob `"pipeline_portfolio": false` (`c_pipeline_portfolio = ref false` in `src/greysynth/config.ml`, reported in JSON output just like `preprocessing_portfolio`).
2. In `src/greysynth/greysynth.ml`, when `!c_pipeline_portfolio` is enabled:
   - Snapshot `Rewrite_proof.checkpoint`, `Rewrite.checkpoint_caches ()`, and `snapshot_preprocessing_log ()`.
   - **Branch A (Modern DAG-native e-graph + normalization):** run under an isolated sub-budget (e.g. up to 55% of remaining total budget, capped cleanly without starving Branch B).
     - **Early exit:** if `size_of_expr branch_a <= 5` (already solved/minimal!) or `!g_has_timedout`, skip Branch B immediately and keep Branch A (zero overhead on fast wins!).
   - **Branch B (OES-first + standard normalization with `egraph_extraction = false`):** restore initial proof checkpoint, caches, and logs; temporarily set `c_egraph_extraction := false` and run standard preprocessing on the remaining budget.
   - Compare `size_of_expr branch_a` vs `size_of_expr branch_b` (tie-breaking on `Sexpr.Expr.compare`): restore the **winning branch's** exact `Rewrite_proof.checkpoint`, `Rewrite` caches, and preprocessing logs, and discard the losing branch completely!
   - **Critical safety check:** Ensure `!g_has_timedout` is NOT poisoned by Branch A hitting its local sub-budget (use a branch-local deadline, never clobbering `!g_total_timeout` for Branch B, and check global deadline cleanly!).
3. Add a focused regression test in `test/pipeline_test.ml` verifying that `pipeline_portfolio = true` chooses the strictly smaller proved branch and produces a connected, independently replayable `Rewrite_proof` certificate with zero leaked edges from the discarded branch!

---

## 3. Residual Polish on `datasets/cobra/obfuscatorx.txt` (7 Rows)

Inspect how Rounds 20–21 perform on the 7 rows of `datasets/cobra/obfuscatorx.txt` (e.g., `(~((~k) & j)) & (~((~j) & k))` $\to$ `j ^ ~k`, `((~j) & i) & (~k)` $\to$ `i & ~(j | k)`, and shared factor `(d | (a + l))` factoring).
- If any small, clean, general algebraic/Boolean rule (such as 3-var Boolean simplification via `linear_mba_mod2w` on subexpressions of size `>= 5` or factoring common multiplicative factors in `factor_group_candidate`) cleanly improves `obfuscatorx.txt` without hurting any existing suite, include it; if Rounds 20–21 already solve or meaningfully shrink it, document the exact numbers cleanly!

---

## 4. Focused Verification Gate for Round 22 (Keep Total Wall Time ~15–20 min!)

1. **Run `make test` + `python3 -m unittest scripts/test_adapt_dataset.py`** — 100% green.
2. **Full adapted dialect audits (zero `--limit`, `--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - Adapted `b2_combined` (`1,110` cases) — target: **`1,110/1,110` established (`0` syntax errors, `0` refuted!)** (up from `792/1,110`!).
   - Adapted `oses_all` (`479` cases, `--check-ground-truth`) — target: **`0` syntax errors, `0` refuted** (up from 12 syntax errors!).
   - Adapted `floki` (`500` cases, `--check-ground-truth`) — target: **`499–500/500` established, `0` refuted** (up from `251/500`!).
3. **`datasets/cobra/obfuscatorx.txt`** (7 cases, `--check-ground-truth`).
4. **Opt-in `"pipeline_portfolio": true` verification (`--workers 8`):**
   - `Tigress L5` (`--limit 200`) comparing default vs `"pipeline_portfolio": true` (confirm 200/200 established, 0 refuted, strictly better or equal solved count & geomean quality!).
   - `QSynth EA` (`100` cases) & `PLDI Non-Poly` (`100` cases) with `"pipeline_portfolio": true` (confirm 200/200 established, 0 refuted, strong quality!).
5. Record concise Round-22 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `docs/FULL_AUDIT_REPORT.md`).
