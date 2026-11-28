# GreySynth Round-68 Spec (Fast Sprint Commit 2/4): Wrapped Child-Root `gf2_masked_xor` + Nested AC `replacements` Fix + Smarter Prepass Gating (`norm_semilinear.ml` & `greysynth.ml`)

**Sprint Mode (Fast 4-Commit Cycle, Commit 2/4):** Gate ONLY with targeted regression tests (`test/round68_test.ml`) + warning-clean `make test` + **35-second `regression_smoke` gate (`/tmp/r68-smoke/out.jsonl`)**! Do NOT run `dev_64`, `L5`, `core_hard`, or `heldout_balanced64` until after Commit 4 (R70).

**Scope:** **ZERO `src/proof/rewrite_proof.ml` edits!** ONLY `src/greysynth/norm_semilinear.ml` and `src/greysynth/greysynth.ml`.

---

## Exact Edits

1. **1-Line Nested AC `replacements` Fix in `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate_with_bridges`, lines 140–175):**
   - Currently `canonical` records `Nodes.replace replacements rebuilt candidate`, so when `substitute` visits an outer opaque atom `node` whose child was also canonicalized, `Nodes.find_opt replacements node` misses and only substitutes the child without checking `replacements` on the rebuilt parent!
   - **Exact 1-line fix:** Inside `canonical` right before `Nodes.add memo node result`, record:
     ```ocaml
     if not (E.is_equal node result) then
       Nodes.replace replacements node result;
     ```
     Now `substitute` replaces any canonicalized opaque atom `node -> result` in ONE O(1) lookup, and all inner bottom-up `(rebuilt, candidate)` edges in `ring_equalities` + `linear_mba_equalities` already connect `node -> result` by congruence!

2. **Wrapped Child-Root `gf2_masked_xor` in `src/greysynth/greysynth.ml` (lines 521–529 & 605–612):**
   - Huge `mba-capabilities-v1` trees like `200901a16ddf2503_w64` (`((x2 ^ x3) + BIG_XOR_TREE)`) and `aa47d91d545f26c8_w64` (`(BIG_XOR_TREE * x0)`) wrap a 12,000-node masked-XOR tree inside a single top-level `Plus`, `Minus`, or `Mul` — so `root-gf2-masked-xor` skipped them (`root_ok = false`) and fell back to `dag_bottom_up_simplify` (`4.8s–5.1s`)!
   - Add a 15-line helper `run_root_gf2_masked_xor ~pass ()` in `src/greysynth/greysynth.ml`:
     - First try `Normalization.gf2_masked_xor_candidate_with_bridges size_of_expr !best` directly on `!best`.
     - If `!best` did not change AND `!best` is `E.Binary { f = (E.Plus | E.Minus | E.Mul as op); x; y; _ }` (or `E.Unary { f = E.Minus; x; _ }`), try `gf2_masked_xor_candidate_with_bridges` on any child `c` with `size_of_expr c >= 128`:
       - If child `c` simplifies to `c'` with `(ring_equalities, linear_mba_equalities, rewritten_c)`, rebuild `rebuilt_root` (replacing `c` with `c'`) and certify **100% ZERO-SMT** via:
         ```ocaml
         Rewrite.accepts_compositional ~pass
           ~equalities:[] ~ring_equalities ~linear_mba_equalities
           ~semilinear_mba_equalities:[ rewritten_c, c' ]
           !best rebuilt_root
         ```
   - Call `run_root_gf2_masked_xor ~pass:"root-gf2-masked-xor" ()` right after `dag_constant_cast_simplify` AND `run_root_gf2_masked_xor ~pass:"post-dag-gf2-masked-xor" ()` right after the `local_budget` loop!
   - Immediately collapses `200901a16ddf2503_w64` (`13,092 -> ~39`), `aa47d91d545f26c8_w64` (`12,344 -> ~37`), and `3e50d423ac3189f6_w64` (`6,200 -> ~35`) in **`< 20 ms`** instead of `5.0s`!

3. **Smarter Non-Shared `local_budget` Prepass Guard (`src/greysynth/greysynth.ml:588-595`):**
   - Remember Milestone-53 (`1.7091x`) vs Milestone-60 (`1.7683x`) on held-out `mba-balanced-v1`: in R54 we enabled a `1.2s` non-shared `dag_bottom_up_simplify` prepass on ALL non-shared bitwise roots (`size > 512`) BEFORE `run_root_semilinear` and `run_root_polysim_poly`!
   - Guard the non-shared `1.2s` prepass so we ONLY spend `1.2s` BEFORE root solvers when `size_of_expr !best > 1024` (or `exposed_product` or `shared`), while letting medium non-shared roots (`513..1024`) try the fast `< 20 ms` `run_root_minterm_poly` / `run_root_semilinear` / `run_root_polysim_poly` FIRST (and if those don't finish them, the existing `dag_bottom_up_simplify` at line 648 still simplifies them immediately afterward!).

---

## Fast-Sprint Verification Gate for Round 68

1. **Regression Tests (`test/round68_test.ml`, plus warning-clean `make test`):**
   - `200901a16ddf2503_w64` (`13,092 -> <= 45` in `< 1.0s`, ZERO SMT for GF(2) collapse, independent `mba_proof` replay!)
   - `aa47d91d545f26c8_w64` (`12,344 -> <= 40` in `< 1.0s`, independent `mba_proof` replay!)
   - `3e50d423ac3189f6_w64` (`6,200 -> <= 40` in `< 1.0s`, independent `mba_proof` replay!)
   - Nested AC-permuted masked-XOR inside `(x0 + XOR_TREE)` -> collapses in one root step with ZERO SMT!
2. **Fast Smoke Gate ONLY (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`):**
   - `datasets/hard_cases/regression_smoke` (`62` cases -> `/tmp/r68-smoke/out.jsonl`): **MUST PASS `62/62` proved & strict, `>= 57/58` exact, `<= 0.805x`, `0` refutations!**
3. Append a brief Round-68 sprint note to `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly!
