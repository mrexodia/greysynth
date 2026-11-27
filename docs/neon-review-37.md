# GreySynth Round-37 Spec: Opaque-Atom Semi-Linear Synthesis, Constant-Cast Folding, Bit-0 Parity Homomorphism & Exact `Known_bits` Add/Sub Propagation

**Baseline:** Round 36 (`5a51a9e` / `58fff14` — `Tigress L5 all_non_exact` `25.41x -> 14.88x` with **`+59` new exact GT**, refreshed `core_hard` `24.31x -> 17.14x` with **`+17` new exact GT**, `regression_smoke` `62/62`, `53` exact GT, `0.8860x`).

**Forensic Diagnosis of `/tmp/r36-final-l5/out.jsonl` (Why `391` Tigress L5 Rows Remained > GT):**
Inspecting the exact Round-36 outputs of the remaining `391` Tigress L5 rows uncovered **four 100%-general algebraic gaps** (zero obfuscator-specific hacks!):

1. **Unfolded constant casts `uext(k) C` / `sext(k) C` broke 96/128-bit shifts & `Known_bits` (`106 / 391 = 27.1%` of remaining Tigress L5!):**
   - E.g. `(uext(32) x0<64>) << (uext(32) 0x6<64>)` and `<< (sext(32) 0x6<64>)` in `target_2135`, `2497`, `6367`, `1868`, `1413`, `2246`, `2511`, `1433`, `5250`.
   - `norm_peepholes.ml` already generates the folded constant `C'`, **but under Legacy cost `uext`/`sext`/`restrict` have cost 0**, so `size_of_expr C' == size_of_expr (uext(k) C) == 1` and `allow_equal_cost = false` rejected every constant-cast fold and redundant-cast collapse!
2. **`semilinear_mba_candidate` synthesized over leaf variables instead of collected `opaque` atoms (`target_2377`, `6533`, `1739`, `1481`, `551`, `254`):**
   - In `norm_semilinear.ml`, preflight already collects the exact `opaque` atom set, yet candidate generation used `Sample_evaluator.variables_of_expr` instead of those opaque atoms! Whenever a 1-atom semi-linear MBA wrapped a compound opaque atom `B = (0x2db + x0) - x1` or `E = x0 / sext(32) x1`, `(2 * (B | 1)) - (B ^ 1) -> B + 1` and `((uext(63)(restrict(0,0) E)) << 1) + (1 ^ E) -> E + 1` were completely missed!
3. **Bit-0 parity homomorphism & `Known_bits` add/sub low-bit propagation (`186 / 391 = 47.6%` of remaining Tigress L5 contain `mask_-2`!):**
   - Arithmetic inside a bit-0 mask (`(-2) | (B + c)`, `1 & (B + c)`, `(-2) | (B - c)`, `1 & (B - c)`) blocked `semilinear_mba` even though bit 0 has **zero incoming carry**, so `(-2) | (B + c) == (-2) | (~B)` (odd `c`) or `(-2) | B` (even `c`), and `1 & (B + c) == 1 & (~B)` (odd `c`) or `1 & B` (even `c`) identically for EVERY `B`! (Immediately exposes pure 1-atom semi-linear MBAs on `target_551`, `target_254`, `target_1868`, `target_2511`!)
   - And `Known_bits.analyze` on `Plus`/`Minus` did not propagate bit-0 parity (`bit0(x ± y) = bit0(x) ^ bit0(y)`) or trailing known zeros (`tz(x ± y) >= min(tz(x), tz(y))`), nor did `known_bits_candidate` collapse bit-0-known odd/even masks (`Y & -2 -> Y - 1` when bit 0 of `Y` is known `1`, fixing `target_6367`: `((-2) & (E - 1)) + 2 -> E`!).
4. **Zero-SMT product peeling missing from `local_candidates` (`45 / 391 = 11.5%`!) + `abstract_slice_candidate` using concrete SMT (`target_3500`):**
   - `target_2618` ended at size `17` outputting `((~a & b)*(~b & a)) + ((a | b)*(a & b))` (GT `3`: `a * b`) purely because `nonlinear_product_identity_candidate` was only wired into `dag_bottom_up_simplify` (not `local_candidates`), plus constant-folded `~C` variants (`target_5511`, `target_3168`).
   - `target_3500` stayed at `restrict(0, 31) (0xffffffff00000000 | ((x0/x1) * ...))` because `abstract_slice_candidate` ran concrete SMT on 64-bit divisions instead of a 1-variable abstract equality `restrict(0, 31) (0xffffffff00000000 | a) == restrict(0, 31) a`!

---

## 1. Opaque-Atom Basis in `semilinear_mba_candidate` (`src/greysynth/norm_semilinear.ml`)

**Deliverables:**
- In `semilinear_mba_candidate`:
  - Use the collected `opaque` atoms (from the preflight walk, sorted deterministically by `E.compare`, up to 4 atoms — and up to 2 atoms in `minimal = true` mode!) as the basis expressions (`atoms`) instead of `Sample_evaluator.variables_of_expr expression`!
  - Evaluate `canonical` and `Smir_interp` against those opaque atoms using a fresh-variable substitution (or `eval_label` with each opaque atom bound to a distinct label — note `eval_label` already accepts arbitrary subexpressions in its `Hashtbl`!) so `((2 * (B | 1)) - (B ^ 1)) -> B + 1` (`target_2377`) and `((uext(63)(restrict(0,0) E)) << 1) + (1 ^ E) -> E + 1` (`target_6533`, where `E = x0 / sext(32) x1`) and `(uext(63)(restrict(0,0) E)) + (E | 1) -> E + 1` (`target_1739`, `1481`) are generated directly and certified by **ONE `semilinear_mba_mod2w` edge** (ZERO SMT)!
  - Also ensure `semilinear_mba_candidate` includes single-atom offset forms `atom + k` and `k - atom` and `(~atom) + k` in `variants` (in addition to `atom & C`, `atom | C`, `atom ^ C`), and add additive sub-sum semi-linear partitioning (`((~x1 | M) + x1 + 1) + rest -> (x1 & M) + rest`, certified by `ring_mod2w` + `semilinear_mba_mod2w`, ZERO SMT — fixes `target_2558`, `target_2536`)!

---

## 2. Constant-Cast Folding, Bit-0 Parity Homomorphism & `Known_bits` Add/Sub Propagation (`src/greysynth/norm_peepholes.ml`, `src/greysynth/known_bits.ml`, `src/greysynth/norm_semilinear.ml`, `src/greysynth/normalization.ml`)

**Deliverables:**
1. **Allow equal-Legacy-cost constant-cast folding & nested-cast collapse (gated strictly on `ast_nodes candidate < ast_nodes original`!):**
   - Add a tiny helper `constant_cast_fold_candidate expression` (run in `dag_bottom_up_simplify` for ALL sizes — even `minimal = true` — and in `local_candidates` with `allow_equal_cost = true` whenever `ast_nodes candidate < ast_nodes original`!):
     - `uext(k) C` / `sext(k) C` / `restrict(lo, hi) C` $\to$ folded `E.Cst` (certified via `< 0.5 ms` constant-equality SMT or `Rewrite.accepts`!).
     - `uext(a) (uext(b) X)` $\to$ `uext(a + b) X`, `sext(a) (sext(b) X)` $\to$ `sext(a + b) X`, `restrict(0, hi) (uext(a) X)` $\to$ `X` (when `E.sizeof X = hi + 1`) or `restrict(0, hi) X` (when `E.sizeof X > hi + 1`) — certified via 1-variable abstract equality!
   - Also allow `Lsl` in `linear_mba` / `semilinear_mba` / `Known_bits` to fold `constant_value y` (which already handles `uext(k) C` and `sext(k) C`!).
2. **Exact low-bit `Known_bits` transfer for `Plus` / `Minus` (`src/greysynth/known_bits.ml`):**
   - For `E.Plus` (`x + y`):
     - Compute exact trailing known-zero count `tz = min (trailing_zeros x.zeros) (trailing_zeros y.zeros)` — all bits `0 .. tz - 1` of `x + y` are guaranteed `0`!
     - If bit 0 of both `x` and `y` is known (either in `zeros` or `ones`), bit 0 of `x + y` is known `bit0(x) ^ bit0(y)`!
     - If `x` and `y` are bitwise disjoint (`(x.zeros | y.zeros) == full_mask`), keep the exact existing disjoint-add transfer (`x + y == x | y`)!
   - For `E.Minus` (`x - y`):
     - Trailing known-zero count is `min (trailing_zeros x.zeros) (trailing_zeros y.zeros)`!
     - If bit 0 of both `x` and `y` is known, bit 0 of `x - y` is known `bit0(x) ^ bit0(y)`!
   - For `E.Lsl` (`x << y`): use `Norm_common.constant_value` (so `x << (uext(32) 6)` gets exact 6 trailing known zeros even before cast folding!).
   - In `known_bits_candidate` (`norm_semilinear.ml`): add sound bit-0-known simplifications:
     - When bit 0 of `Y` is known `1`: `Y & (-2) -> Y - 1` (when inside an additive context or when strictly cheaper via `ring`), `Y | 1 -> Y`, `Y ^ 1 -> Y - 1`.
     - When bit 0 of `Y` is known `0`: `Y & (-2) -> Y`, `Y | (-2) -> -2`, `Y & 1 -> 0`!
3. **Universal Bit-0 Parity Homomorphism (`bit0_parity_candidate`, certified via 1-variable abstract equality — `< 0.5 ms` on ANY subtree size!):**
   - `(-2) | (B + c)` and `(B + c) | (-2)` (and `B - c`):
     - When `c` is odd: $\to$ `(-2) | (~B)` (size strictly smaller: `(-2) | (B + c)` has size 5 $\to$ `(-2) | (~B)` has size 4!)
     - When `c` is even: $\to$ `(-2) | B` (size 5 $\to$ 3!)
   - `1 & (B + c)` and `(B + c) & 1` (and `B - c`):
     - When `c` is odd: $\to$ `1 & (~B)` (size 5 $\to$ 4!)
     - When `c` is even: $\to$ `1 & B` (size 5 $\to$ 3!)
   - `uext(w-1, restrict(0, 0, B + c))` (and `B - c`):
     - When `c` is even: $\to$ `uext(w-1, restrict(0, 0, B))` (size strictly smaller!)
     - When `c` is odd: $\to$ `uext(w-1, restrict(0, 0, ~B))` (size strictly smaller!)
   - Certify EVERY one via 1-variable abstract equality (`(-2) | (a + c) == (-2) | (~a)`, etc.) and wire into BOTH `dag_bottom_up_simplify` and `local_candidates`!

---

## 3. Wire Zero-SMT Product Peeling into `local_candidates`, True Abstract Certification for `abstract_slice_candidate`, & Permanent Proof-Kernel Counterexample (`src/greysynth/norm_nonlinear.ml`, `src/greysynth/norm_probes.ml`, `src/greysynth/normalization.ml`, `test/proof_test.ml`)

**Deliverables:**
1. **Wire `nonlinear_product_identity_candidate` into `local_candidates` (`norm_probes.ml`)** (using its zero-SMT compositional proof `linear_mba_equalities` + `ring_equalities`!) AND generalize it to match constant-folded complementary constants `C1, C2` (`C2 == ~C1`, fixing `target_5511` & `target_2618`!).
2. **True 1-variable abstract certification for `abstract_slice_candidate` (`norm_semilinear.ml`, `normalization.ml`, `norm_probes.ml`):**
   - Have `abstract_slice_candidate` also return the abstract 1-var equality `(orig, cand)` (or certify with `Rewrite.accepts_compositional` / `Rewrite.accepts` where `Rewrite`'s existing abstract-generalization replaces `base` with a fresh variable `a` FIRST — check why `target_3500` didn't abstract `((x0/x1) * (x2/x3) * (x4/x5))`! Ensure `abstract_slice_candidate` is wired into BOTH `dag_bottom_up_simplify` AND `local_candidates`, and abstract-generalizes `base` before calling Bitwuzla so it proves in `< 0.5 ms` even when `base` contains 64-bit `Udiv` or 1,000,000 nodes!).
3. **Permanent regression test in `test/proof_test.ml`:**
   - Add the exact Round-36 soundness counterexample:
     `uext(6, restrict(0, 1, sx + 1)) == 1 + (sx & 3)`
     to BOTH the `semilinear_mba_equal` kernel negative list AND the Bitwuzla negative cross-test list (`verdict = No`)!

---

## 4. Fast Verification Gate for Round 37 (Target Wall Time: ~6–8 min!)

1. **Unit & Regression Tests (`test/round37_test.ml` + `test/proof_test.ml`):**
   - `test/proof_test.ml` verifies `uext(6, restrict(0, 1, sx + 1)) == 1 + (sx & 3)` is rejected by BOTH kernel and Bitwuzla.
   - `test/round37_test.ml` verifies:
     - Constant-cast folding `uext(32) 0x6<64> -> 0x6<96>` & `sext(32) 0x6<64> -> 0x6<96>`
     - Opaque-atom semi-linear MBA `(2 * (B | 1)) - (B ^ 1) -> B + 1` (with `B = (0x2db + x) - y`) and `((uext(63)(restrict(0,0) E)) << 1) + (1 ^ E) -> E + 1` (with `E = x / sext(32) y`)
     - Bit-0 parity homomorphism `(-2) | (B + 1) -> (-2) | (~B)` and `target_254` / `target_551` style collapse (`((-2 * (-2 | (B + 1))) + B) ^ 1 - 3 -> B`)
     - `Known_bits` add/sub parity (`((x << 12) + (y << 13) - 1) & (-2) -> ((x << 12) + (y << 13)) - 2`)
     - `local_candidates` zero-SMT product peeling on `((~a & b)*(~b & a)) + ((a | b)*(a & b)) -> a * b` AND constant-folded `C, ~C` variant (`0x1e` / `0xffffffffffffffe1`)
     - `abstract_slice_candidate` on `restrict(0, 31) (0xffffffff00000000 | ((x0/x1) * (x2/x3))) -> restrict(0, 31) ((x0/x1) * (x2/x3))` in `< 0.1s`!
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r37-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` cases — target: push new exact GT past **`120+`** and slash geomean from `14.88x` well below `10x`!)
   - **`datasets/hard_cases/core_hard/`** (`353` cases — target: big leap in `Tigress L5–L8` & `OMVLL` exact count and geomean!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — must stay `62/62` established, `0` refuted, `<= 0.95x`!)
3. Record concise Round-37 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
