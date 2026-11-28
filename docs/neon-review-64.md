# GreySynth Round-64 Spec (Single-Focus): Fix `gf2_masked_xor_candidate_with_bridges` to Canonicalize Opaque Atoms Inside `parse` Only + Fast Root Guard (`src/greysynth/norm_semilinear.ml`)

**Baseline:** Round 63 (`e4d1774f` — `aa47d91d` collapsed `12,344 -> 37`, `cb67824e` collapsed `11,925 -> 42`, `c731a7cf` collapsed `6,580 -> 39` exact, `r63-core` improved `7.73x -> 7.61x` with `16` exacts, `0` refutations!).

**Why One 20-Line Fix Turns Round 63 Into a MASSIVE Win Across ALL 4 Gates:**
- In Round 63 (`src/greysynth/norm_semilinear.ml:113-160`), `gf2_masked_xor_candidate_with_bridges` ran `canonical 0 expression` **from the root BEFORE `parse`** with `depth >= 8` and WITHOUT checking `cost`/`dag_size`/root operator first:
  1. On **non-GF2 expressions** (e.g. `f31495f8155348ff_w64: 37 -> 12,346 @ 8.86s`, and every `Plus`/`Mul` node in `dag_bottom_up_simplify`!), `canonical 0 expression` walked the AST and recorded ring/linear equalities even when `parse` returned `None`, burning seconds of CPU!
  2. On **deep masked-XOR trees** (`200901a16ddf2503_w64: 13,092 -> 6,931`, `3e50d423ac3189f6_w64: 6,200 -> 3,314`, `aa47d91d545f26c8_w64`), the outer `^` spine is **25–35 levels deep**, so `depth >= 8` stopped BEFORE reaching the opaque atoms at depth 25–35! Thus `root-gf2-masked-xor` fired **0 times**, forcing `dag-gf2-masked-xor` to fire 157–283 times over `4.0s–5.0s`!

---

## Exact Fix (`src/greysynth/norm_semilinear.ml` ONLY — ZERO `rewrite_proof.ml` Edits!)

Rewrite `gf2_masked_xor_candidate_with_bridges cost expression` (lines 113–160) as a single clean pass (reusing the exact `parse` logic of `gf2_masked_xor_candidate`, with `gf2_masked_xor_candidate` simply delegating to it or remaining untouched):

1. **Fast O(1) entry guard BEFORE any traversal:**
   - Check root operator is `E.Unary { f = E.Not; _ } | E.Binary { f = (E.Xor | E.And | E.Or); _ }`! (If the root is `Plus`/`Minus`/`Mul`/etc., immediately return `None` in **O(1)**!)
   - Check `width <= 128`, `cost expression >= 11`, `cost expression <= 65_536`, and `Greysynth_utils.Utils.dag_size_bounded ~limit:8192 expression <= 8192`!
2. **Call `canonical 0` ONLY on opaque atoms inside `parse` (NOT on the outer XOR spine!):**
   - `parse` traverses `E.Cst`, `E.Not`, `E.Xor`, `E.And` (const or disjoint), `E.Or` (const or disjoint) with **NO depth limit** (DAG-memoized in `memo` — visits 13,092 nodes in `< 1 ms`!).
   - ONLY when `parse` hits an opaque atom (`| atom ->` or non-disjoint `E.Or | E.And`):
     - Call `let atom' = canonical 0 atom in` (depth `<= 6`, flattened arity `<= 8`, DAG-memoized in `ac_memo`, recording `(rebuilt, cand)` in `ring_equalities` for `Plus`/`Mul` and `linear_mba_equalities` for `And`/`Or`/`Xor`, and `Nodes.replace replacements atom atom'` whenever `not (E.is_equal atom atom')`!)
     - Return `(Z.zero, [ atom', mask ])`!
3. **Build `rewritten_source` ONLY AFTER `parse` succeeds AND `cost candidate < cost expression`:**
   - If `Nodes.length replacements = 0` then `rewritten_source = expression` (O(1), ZERO substitution cost!).
   - Otherwise build `rewritten_source` via a cycle-guarded memoized substitution of `replacements` on `expression` (only replacing keys in `replacements`, which are the opaque atoms!).
   - Return `Some (candidate, List.rev !ring_equalities, List.rev !linear_mba_equalities, rewritten_source)`!

*(Double-check proof connectivity: for each opaque atom `atom`, `canonical 0 atom` connects `atom -> atom'` via bottom-up congruent `(rebuilt, cand)` edges in `ring_equalities` + `linear_mba_equalities`. Substituting `atom -> atom'` in `expression` yields `rewritten_source`, connected to `expression` by congruence! Then `gf2_masked_xor_equal` in `semilinear_mba_mod2w` proves `rewritten_source == candidate` in `< 5 ms` with ZERO SMT!)*

---

## Verification Gate for Round 64

1. **Regression Tests (`test/round64_test.ml`, plus warning-clean `make test`):**
   - Deep (depth 20!) left-skewed AC-permuted masked-XOR tree -> `gf2_masked_xor_candidate_with_bridges` collapses it at the **ROOT** in a single step with **ZERO SMT** and independent `mba_proof` replay!
   - `aa47d91d545f26c8_w64` (`12,344 -> <= 40` in `< 1.0s`!), `200901a16ddf2503_w64` (`13,092 -> <= 45` in `< 1.0s`!), AND `f31495f8155348ff_w64` (`12,346 -> <= 40` in `< 1.0s` — fixing the R63 `8.86s` regression!) — all with independent `mba_proof` replay!
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r64-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r64-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r64-leeky-dev64/out.jsonl` — target: **`mba-capabilities-v1` drops from `1.71x -> ~1.15x` and `dev_64` hits a MASSIVE NEW ALL-TIME RECORD `<= 1.68x`!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`165` shrunk cases -> `/tmp/r64-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`277` refreshed cases -> `/tmp/r64-core/out.jsonl`)
3. Record concise Round-64 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
