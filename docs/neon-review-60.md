# GreySynth Round-60 Spec (Focused): AC-Unified Zero-SMT `gf2_masked_xor_candidate` (`norm_semilinear.ml`) + 4-Line 2-Var Basis Bit-Index Fix (`norm_linear.ml`)

**Baseline:** Round 59 (`offer_linear_sum` universal `c + c * B -> (-c) * (~B)` absorption — **MASSIVE `core_hard` BREAKTHROUGH: `21 -> 57+` exact `<= GT` (`+36`!), `328/328` (`100%`) strict, `~4.4x` geomean**, closing `15/29` remaining `mba_obf_nonlinear` and `14/20` remaining `neureduce` @ `1.011x`; `170/170` (`100%`) strict on `L5`; `62/62` strict & `56/58` exact on `regression_smoke`; **`0` refutations**!).

**Scope:** Producer-side ONLY (ZERO `src/proof/rewrite_proof.ml` edits!). Two super clean, surgical changes:

---

## 1. Fix the 4-Line 2-Variable Basis Bit-Index Swap in `src/greysynth/norm_linear.ml` (lines 676–688)

- In `norm_linear.ml`, bit `0` (`index = 1`) is `atoms.(0) = 1, atoms.(1) = 0` (`f(1, 0)`), and bit `1` (`index = 2`) is `atoms.(0) = 0, atoms.(1) = 1` (`f(0, 1)`).
- Round 59 accidentally bound `v01 = shifted.(1)` and `v10 = shifted.(2)` (swapped!) and `cand = Z.sub v10 v11` (missing `- v01` and wrong sign!), causing those two calls to emit mismatched candidates that `linear_mba_mod2w` rejected (wasting ~5% CPU on 2-atom nodes and missing asymmetric `{x, y, x | y}` exacts like `6*y + 5*(~y & x) -> y + 5*(x | y)`!).
- **Exact 4-line fix (`src/greysynth/norm_linear.ml:676-688`):**
  ```ocaml
      if count = 2 then (
        let v10 = shifted.(1) and v01 = shifted.(2) and v11 = shifted.(3) in
        let cx_or = normalize (Z.sub v11 v01)
        and cy_or = normalize (Z.sub v11 v10)
        and cor = normalize (Z.sub (Z.add v10 v01) v11) in
        offer_linear_sum offset
          [ cx_or, atoms.(0); cy_or, atoms.(1);
            cor, E.binary E.Or atoms.(0) atoms.(1) ];
        let cand = normalize (Z.sub (Z.sub v11 v10) v01) in
        offer_linear_sum offset
          [ v10, atoms.(0); v01, atoms.(1);
            cand, E.binary E.And atoms.(0) atoms.(1) ])
  ```
  - **Algebraic verification (all 4 inputs `(atoms.(0), atoms.(1))`):**
    - `{x, y, x | y}`: `(0,0) -> 0`; `(1,0) -> (v11 - v01) + (v10 + v01 - v11) = v10 = shifted.(1)`; `(0,1) -> (v11 - v10) + (v10 + v01 - v11) = v01 = shifted.(2)`; `(1,1) -> (v11 - v01) + (v11 - v10) + (v10 + v01 - v11) = v11 = shifted.(3)`! EXACT!
    - `{x, y, x & y}`: `(0,0) -> 0`; `(1,0) -> v10 = shifted.(1)`; `(0,1) -> v01 = shifted.(2)`; `(1,1) -> v10 + v01 + (v11 - v10 - v01) = v11 = shifted.(3)`! EXACT!

---

## 2. AC-Unified Zero-SMT `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml` + 3 Call Sites in `greysynth.ml` & `normalization.ml`)

- Our Round-56 `gf2_masked_xor_equal` proof-kernel fast path (`max_atoms = 64`, `< 5 ms`, ZERO SMT) cut `mba-capabilities-v1` from `2.33x -> 1.50x`, but `aa47d91d545f26c8_w64` (`12,344 -> 1,165`), `200901a16ddf2503_w64` (`13,092 -> 1,261`), `c731a7cf74ac2d9b_w64` (`6,580 -> 545`), `3e50d423ac3189f6_w64` (`6,200 -> 451`), and `cb67824ea6196472_w64` (`11,925`) still have duplicate compound atoms differing only by AC operand ordering (`(3 + (x2 + (x1 ^ x3)))` vs `(((x1 ^ x3) + x2) + 3)`), pushing term count past `48` and preventing cancellation!
- **Exact fix in `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate`):**
  1. Raise the entry guard to `cost expression <= 65_536` and `dag_size_bounded ~limit:8192 expression <= 8192`, and raise the term cap from `48` -> **`64`** (matching `gf2_masked_xor_equal` in `src/proof/rewrite_proof.ml`!).
  2. Add a small DAG-memoized recursive AC canonicalizer `canonical_atom` inside `gf2_masked_xor_candidate` (bounded to `<= 8` flattened operands per operator, recursing through `Plus`, `Mul`, `And`, `Or`, `Xor`):
     - Flatten and sort `Plus` / `Mul` operands -> rebuild with `build_balanced` -> if changed, record `(original, canonical)` in `ring_edges` and `replacements`.
     - Flatten and sort `And` / `Or` / `Xor` operands -> rebuild with `build_balanced` -> if changed, record `(original, canonical)` in `linear_edges` and `replacements`.
     - Canonicalize every opaque atom via `canonical_atom` BEFORE interning it in `parse`!
  3. Build `rewritten_source` via a cycle-guarded memoized substitution of `replacements` on `expression` (same pattern as `norm_linear.ml:809-837`).
  4. Return `Some (candidate, List.rev !ring_edges, List.rev !linear_edges, rewritten_source)`!
  5. Update the 3 call sites (`root-gf2-masked-xor` & `post-dag-gf2-masked-xor` in `src/greysynth/greysynth.ml`, `dag-gf2-masked-xor` in `src/greysynth/normalization.ml`, plus any test calling `gf2_masked_xor_candidate`) to certify **100% ZERO-SMT** via:
     ```ocaml
     Rewrite.accepts_compositional ~pass:...
       ~equalities:[] ~ring_equalities ~linear_mba_equalities
       ~semilinear_mba_equalities:[ rewritten_source, candidate ]
       source candidate
     ```
     (NO SMT fallback! Zero timeout risk!)

---

## Verification Gate for Round 60

1. **Regression Tests (`test/round60_test.ml`, plus warning-clean `make test`):**
   - `6 * y + 5 * ((~y) & x)` (`mba_obf_nonlinear__line_0000892` shape) -> cost `<= 7` (`y + 5 * (x | y)`), zero-SMT `linear_mba_mod2w`!
   - `1 + b + 2 * (x & (~b))` (`pldi_nonpoly__line_0000105` shape) -> cost `<= 9` (`1 + 2 * (x | b) - b`), zero-SMT `linear_mba_mod2w`!
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 45`, `< 1.0s`, ZERO SMT for GF(2) collapse, independent `mba_proof` replay!)
   - `200901a16ddf2503_w64` (`mba-capabilities-v1`: `13,092 -> <= 49`, `< 1.0s`, independent `mba_proof` replay!)
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r60-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r60-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r60-leeky-dev64/out.jsonl` — target: **big `mba-capabilities-v1` jump `1.50x -> ~1.10x`, pushing `dev_64` to a new all-time record `>= 550/880` exact & `<= 1.65x`!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`170` shrunk cases -> `/tmp/r60-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`328` refreshed cases -> `/tmp/r60-core/out.jsonl` — target: `>= 65` exact & `<= 4.2x`!)
3. Record concise Round-60 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
