# GreySynth Round-43 Spec: Balance Internal DAG SMT Budget + Full Authoritative `Tigress L5–L8` (`1,894` Rows) Sweep

**Baseline:** Round 42 (`ffb2eb4` / `5482853` — `Tigress L5 all_non_exact` **`+200` exact GT, `3.53x`** (best yet!), `core_hard` **`+82` exact GT, `3.19x`**, `regression_smoke` **`62/62`, `54` exact GT, `0.7995x`**, `0` refutations).

**Why Round 43 Now:**
Across **Rounds 36–42** (`7` consecutive general algebraic & DAG-native rounds since our Round-34 corpus sweep), we have achieved massive verified gains across all four `Tigress L5–L8` levels (`Tigress L5`: `25.41x -> 3.53x`, `+200` exact GT; `L6`: `179x -> 11.4x`; `L7`: `257x -> 17–20x`; `L8`: `9,694x -> 16–22x`). Before pruning `datasets/hard_cases/all_non_exact/` (`3,100` rows, of which `1,894` are `Tigress L5–L8`), we make one tiny 2-line budget balance to eliminate R42's parallel DAG contention (`oses__line_0000240`, `tigress_lvl_8__target_1349`), then sweep **all `1,894` `Tigress L5–L8` non-exact rows** cleanly per level!

---

## 1. Tiny 2-Line Internal DAG SMT Budget Balance (`src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

In Round 42, keeping `0.80s` at `run_root_semantic_probes`, `0.70s` at `run_cleanup`, and the `0.5` abstract split in `rewrite_proof.ml` was a huge win, **but** raising the *internal* `dag_bottom_up_simplify` probe timeout from `0.15s -> 0.60s` and `smt_budget` from `1.2s -> 1.5s` (across up to 4 DAG passes!) caused `11` parallel core rows and `oses__line_0000240` to exhaust the 5s budget mid-DAG under 8-worker contention.

- **Fix (2 lines, zero proof-kernel changes):**
  1. In `src/greysynth/normalization.ml`: set internal `dag_bottom_up_simplify` `accept_probe` SMT fallback timeout to **`~timeout:0.25`** (down from `0.60`, still getting `0.125s` abstract via the `0.5` split) and default `?(smt_budget = 1.0)` (down from `1.5`).
  2. In `src/greysynth/greysynth.ml`: pass **`~smt_budget:1.0`** to `dag_bottom_up_simplify` inside the `run_preprocessing` loop, while **KEEPING** `run_root_semantic_probes` at **`~timeout:0.80`** and `run_cleanup` at **`~timeout:0.70`** (and keeping `opaque_probe_calls` incrementing ONLY on `Some candidate`, and keeping `rewrite_proof.ml` untouched!).
- Verify `make test` is warning-clean and 100% green, and run `datasets/hard_cases/regression_smoke/` (`62` cases -> `/tmp/r43-smoke/out.jsonl`) confirming **`62/62` established, `0` stalls (including `oses__line_0000240` strictly reduced in parallel!), `0` refutations, `<= 0.80x`!**

---

## 2. Authoritative Full `Tigress L5–L8` Sweep (`1,894` Rows, `--workers 8`, RAM Safely Under 30 GB)

Run the exact R18 benchmark configuration (`--workers 8`, with `mba_equiv` + independent `mba_proof` certificate replay, `0` refutations!) cleanly **one level at a time** so every artifact is retained and cleanly inspectable:
1. **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` rows) -> `/tmp/r43-l5/out.jsonl`
2. **`datasets/hard_cases/all_non_exact/tigress_l6/`** (`468` rows) -> `/tmp/r43-l6/out.jsonl`
3. **`datasets/hard_cases/all_non_exact/tigress_l7/`** (`475` rows) -> `/tmp/r43-l7/out.jsonl`
4. **`datasets/hard_cases/all_non_exact/tigress_l8/`** (`501` rows) -> `/tmp/r43-l8/out.jsonl`

- If ANY rows time out under 8-worker contention (expected: `0` or a tiny handful of giant L8 files), replay ONLY those rows in isolated 1-worker mode into `/tmp/r43-tigress-isolated/out.jsonl` so every single one of the `1,894` rows is strictly established with **0 refutations**!
- Report per-level results (`Established`, `Exact <= GT`, `Quality before -> after`, `Better/equal/worse`, `0` refutations) in `docs/IMPLEMENTATION_RESULTS.md`, and commit cleanly on `proof-coverage` (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `src/proof/rewrite_proof.ml`).
