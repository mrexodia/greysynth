# GreySynth Round-34 Spec: Surgical Survivor Closure — 1-Var Shannon Factoring & De Morgan Boolean Cleanup, Zero-SMT Product Peeling, Ring-Reduced `complementary_slice_candidate` & Zero-Raw-SMT Giant-DAG Peeling

**Baseline:** Round 33 (`c07a8ec` — `Neureduce` `3.56x -> 1.11x` (`53/53` better), `QSynth EA` `11.08x -> 1.20x` (`31/60` exact, `388 -> 9`), `ObfuscatorX` `7/7` exact (`0.886x`), `OMVLL` `75.25x -> 48.63x`, `core_hard` `5.82x -> 5.28x` with `242/405` exact GT, `regression_smoke` `0.9181x`).

**Forensic Diagnosis of `/tmp/r33-core/out.jsonl` (Why Every Single Remaining Named Survivor Stopped 1 Step Short):**
1. **`mba_obf_nonlinear/972` (`7` vs GT `6`), `neureduce/798` (`15` vs GT `11`), `neureduce/140` (`16` vs GT `13`), `pldi_poly/941` (`17` vs GT `12`), `mba_flatten/2938` (`17` vs GT `12`):**
   - ALL FIVE already recovered their exact linear MBA — they only missed exact GT because `boolean_candidates`:
     - **(a)** emitted `~(y & ~x)` instead of De Morgan `x | ~y` (size 7 vs 6 on `mba_obf_nonlinear/972`!), and
     - **(b)** emitted the 11-node ANF `(y ^ z) ^ ((y & x) ^ (x & z))` instead of the 6-node 1-variable Shannon factorization `~x & (y ^ z)` (on `neureduce/798`, `neureduce/140`, `pldi_poly/941`, `mba_flatten/2938`)!
2. **`c_mba_obfuscator` ALL 5 remaining slice survivors (`3551`, `4575`, `4796`, `4543`, `4551`):**
   - In `normalization.ml:1944`, `complementary_slice_candidate` substituted `uext(w-k, restrict(0,k-1, ~x)) -> mask - uext(w-k, restrict(0,k-1, x))` and immediately checked `if cost substituted < cost expression` **WITHOUT running `ring_polynomial_candidate` on `substituted`** — since `mask - u` is 1 node larger than `uext(restrict(~x))`, `cost substituted < cost expression` was ALWAYS FALSE, so `complementary_slice_candidate` never fired!
3. **`tigress_l8/target_5856` & `5710` (`1.86M`), `omvll/target_771` & `798` (`3.07M`), and `c_mba_obfuscator/target_1685` (`29,511`, which hit `5` in Round 31!):**
   - `dag-product-peel` (`normalization.ml:4590`) called raw `Rewrite.accepts ~timeout:0.25` (sending giant children to Bitwuzla SMT -> `inconclusive: 2` on `tigress_l8/5856`!) instead of certifying `((a & ~b)*(b & ~a)) + ((a & b)*(a | b)) == a * b` with **ZERO SMT** via 3 `linear_mba_mod2w` edges (`a&~b == a - (a&b)`, `b&~a == b - (a&b)`, `a|b == a + b - (a&b)`) + 1 `ring_mod2w` edge (`(a - u)*(b - u) + u*(a + b - u) == a * b`)!
   - Raw non-compositional `Rewrite.accepts` calls inside `dag_bottom_up_simplify` (`dag-peephole`, `dag-demand-bits`, `dag-power2-pullout`, `dag-mask-lift`) ran on giant nodes (`cost > 512`), causing `2` inconclusive SMT timeouts on `c_mba_obfuscator/target_1685` and `5` inconclusive SMT timeouts on `omvll/target_771`!

---

## 1. 1-Variable Shannon Factoring & De Morgan Cleanup in `boolean_candidates` (`src/greysynth/normalization.ml`)

**Deliverables:**
1. **De Morgan simplification helper `demorgan_not`:**
   - Simplify `~(a & b) -> ~a | ~b`, `~(a | b) -> ~a & ~b`, `~(~a) -> a`, `~(0xfff... ^ a) -> a`, `~0 -> 0xfff...`, `~0xfff... -> 0` (choosing the cheaper of `E.unary E.Not e` vs `demorgan_not e` — e.g. `~(y & ~x)` (size 5) becomes `~y | x` (size 4), immediately turning `mba_obf_nonlinear/972` into **`7 * (x | ~y)` (size 6 = EXACT GT, 30/30 on `mba_obf_nonlinear`!)**!).
   - Apply `demorgan_not` when generating `boolean1` in the exact 2-value offset synthesizer AND inside `boolean_candidates`.
2. **1-variable Shannon factoring for `count = 3` inside `boolean_candidates` (both full and active-projected tables!):**
   - Write a tiny exact 2-variable Boolean synthesizer `synth2 a b t00 t01 t10 t11` covering all 16 truth tables with minimal ASTs (`0`, `~0`, `a`, `~a`, `b`, `~b`, `a & b`, `a | b`, `a ^ b`, `~(a ^ b)`, `a & ~b`, `~a & b`, `a | ~b`, `~a | b`, `~(a & b)`/`~a | ~b`, `~(a | b)`/`~a & ~b`).
   - For any 3-variable truth table `truth` over atoms `[|a0; a1; a2|]`, for each pivot `i in {0, 1, 2}` with other two atoms `(u, v)`:
     - Extract the 4-bit cofactor `f0` (at `a_i = 0`) and `f1` (at `a_i = 1`).
     - If `f1 = all false`: emit `~a_i & synth2 u v f0` (emits **`~x & (y ^ z)`** and **`~v0 & (v1 ^ v2)`** — size 6 instead of 11!)
     - If `f0 = all false`: emit `a_i & synth2 u v f1`
     - If `f1 = all true`: emit `a_i | synth2 u v f0`
     - If `f0 = all true`: emit `~a_i | synth2 u v f1`
     - If `f1 = not f0`: emit `a_i ^ synth2 u v f0` (and `~(a_i ^ synth2 u v (not f0))` if smaller!)
   - Also check `neureduce/798` (`-(~v0 & (v1 ^ v2)) + (v3 | v4)` -> size 11), `neureduce/140` (`-(~v0 & (v1 ^ v2)) - (v3 & v4) - 1` -> size 13), `pldi_poly/941` (`x*y + 3*(~x & (y ^ z))` -> size 12), and `mba_flatten/2938` (`-> 12`) — ALL FOUR collapse directly to exact GT!

---

## 2. Fix `complementary_slice_candidate` to Run `ring_polynomial_candidate` After Substitution (`src/greysynth/normalization.ml`)

**Deliverables:**
- In `complementary_slice_candidate cost expression`:
  - Handle BOTH `uext(w - k, restrict(0, k - 1, ~base))` AND nested `uext(w - k, restrict(0, k - 1, ~ (uext(w - k, restrict(0, k - 1, base)))))` $\to$ `((1 << k) - 1) - uext(w - k, restrict(0, k - 1, base))`!
  - After building `substituted`, ALWAYS run `ring_polynomial_candidate cost substituted` (and also `linear_candidates ~max_atoms:6 cost substituted` when `linear_mba_compatible substituted`)!
  - Let `best` be the smallest of `[substituted; ring_opt; linear_opt]`.
  - If `cost best < cost expression`, return `Some (best, List.rev !equalities, ring_edges, linear_edges)`!
  - Also certify each `(rebuilt, replacement)` equality via **1-variable abstract equality** when `base` is non-atomic (or tiny `cost rebuilt <= 32`) so it never hangs on giant `base`!
  - Verify `c_mba_obfuscator/target_3551` (`506 -> <= 7`, GT 5) and `target_4575` / `4796` / `4543` / `4551` collapse dramatically!

---

## 3. Zero-SMT Compositional Product Peeling & Giant-DAG Raw-SMT Guard (`src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

**Deliverables:**
1. **Zero-SMT compositional certification for `nonlinear_product_identity_candidate` (`((a & ~b)*(b & ~a)) + ((a & b)*(a | b)) == a * b`):**
   - Return `(candidate, linear_mba_equalities, ring_equalities)` instead of calling raw `Rewrite.accepts ~timeout:0.25`!
   - Specifically, let `u = E.binary E.And a b`, `e1 = E.binary E.And a (E.unary E.Not b)` (exact subtree matching the input's left/right operand order!), `e2 = E.binary E.And b (E.unary E.Not a)`, `e3 = E.binary E.Or a b`:
     - `linear_mba_equalities`:
       - `(e1_actual, E.binary E.Minus a u)`
       - `(e2_actual, E.binary E.Minus b u)`
       - `(e3_actual, E.binary E.Minus (E.binary E.Plus a b) u)`
     - `ring_equalities`:
       - `(substituted_sum, E.binary E.Mul a b)` where `substituted_sum` replaces `e1_actual`, `e2_actual`, `e3_actual` in `!result` with `a - u`, `b - u`, `(a + b) - u`!
   - Certify via `Rewrite.accepts_compositional ~pass:"dag-product-peel" ~equalities:[] ~ring_equalities ~linear_mba_equalities !result candidate`!
   - **ZERO SMT! Works in `< 0.5 ms` on 10-million-node children!** Peels all 3 layers of `tigress_l8/target_5856` & `5710` (`1,858,527 -> 7` exact GT!)!
2. **Guard ALL raw non-compositional `Rewrite.accepts` calls inside `dag_bottom_up_simplify` to `cost !result <= 512`:**
   - Guard `dag-peephole`, `dag-demand-bits`, `dag-power2-pullout`, and `dag-mask-lift` so they NEVER fire raw Bitwuzla SMT on nodes with `cost !result > 512` (unless certified via a decidable `ring_mod2w`/`linear_mba_mod2w`/`semilinear_mba_mod2w` compositional proof)!
   - **Restore `c_mba_obfuscator/target_1685` (`29,511 -> 5`!):** Check why Round 31 (`7489c64`) solved `target_1685` to `5` (`74` ring proofs + `19` linear MBA proofs in `2.75s`) while Round 32/33 stalled at `29,511` with `candidates: 3, inconclusive: 2` — removing the raw SMT timeout on `cost > 512` in `dag_bottom_up_simplify` (and ensuring `run_root_complementary_slice` does not burn SMT time on giant `size > 10_000` trees without `uext/restrict`) directly restores `target_1685 -> 5`!
   - **Unblock `omvll/target_771` & `798` (`3,070,823 -> <= 100`):** With raw SMT guarded out of giant DAG nodes (`cost > 512`), the 12 shrinking rounds of zero-SMT `ring_mod2w` + `linear_mba_mod2w` peel all 6 layers of `omvll/target_771` (`(((U - (U|V)) + V) + (U|V)) -> U + V`) cleanly inside the 5s budget!

---

## 4. Fast, Focused Verification Gate for Round 34 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round34_test.ml`):**
   - Load and verify end-to-end with `mba_proof` replay:
     - `mba_obf_nonlinear/line_0000972` (`166 -> <= 6`, exact GT `7*(x|~y)`!)
     - `neureduce/line_0000798` (`79 -> <= 11`, exact GT!), `neureduce/line_0000140` (`74 -> <= 13`, exact GT!)
     - `pldi_poly/line_0000941` (`83 -> <= 12`, exact GT!)
     - `c_mba_obfuscator/target_1685` (`29,511 -> <= 7`, restored!), `c_mba_obfuscator/target_3551` (`506 -> <= 10`)
     - `tigress_l8/target_5856` (`1,858,527 -> <= 9`, exact GT `7`!)
     - `omvll/target_771` (`3,070,823 -> <= 100`!)
   - Keep ALL Round 23–33 flagship tests green (`target_3218`, `target_366`, `permutation64`, `pldi_nonpoly/895`, `msimba/191`, `tigress_l7/l8 target_1016`, `qsynth_ea/388`, `neureduce/98,632,489`).
2. **Run `make test`** — 100% green.
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB, retain JSONLs under `/tmp/r34-*/out.jsonl`):**
   - **`datasets/hard_cases/all_failing/neureduce/`** (53 cases)
   - **`datasets/hard_cases/all_failing/pldi_poly/`** (62 cases)
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases — target: push exact GT past **`265+`** and slash geomean from `5.28x` toward **`~3x`**!)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted, geomean `<= 0.95x`!)
4. Record concise Round-34 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
