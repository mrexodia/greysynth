# GreySynth Round-52 Spec: Factored Linear-MBA Synthesis (Non-Zero Offset 2-Term + Signed-GCD / Coefficient-Grouped Möbius) + Scalar-Mul/Shift Boundary Consistency + Distributive Common-Factor Pullout

**Baseline:** Round 51B (`0d78d6b` / `453f120` — **NEW AUTHORITATIVE CORPUS-WIDE SCOREBOARD across 32 suites, 54,105 audited:** **`54,095 / 54,095` (`100.000%`) of all non-GB parseable expressions formally proved (`99.9871%` overall), `0` refutations, `50,998 / 52,648` (`96.866%`) exact `<= GT`**, `97.54% <= 1.25x`, `98.10% <= 2.00x`; `datasets/hard_cases/all_non_exact/` shrunk **`2,234 -> 1,650`** (`tigress_l5`: `195`, `tigress_l6`: `203`, `tigress_l7`: `231`, `tigress_l8`: `275`, `mba_flatten`: `263`, `pldi_poly`: `110`, `qsynth_ea`: `77`, `omvll`: `74`, `pldi_nonpoly`: `70`, `c_mba_obfuscator`: `46`, `mba_obf_nonlinear`: `36`, `oses`: `27`, `neureduce`: `23`, `floki`: `14`, `loki`: `4`, `loki_tiny`: `2`); refreshed `core_hard/`: `334` rows!).

**Zero proof-kernel changes required in Round 52** (`src/proof/rewrite_proof.ml` stays untouched!). All three upgrades below are 100% general, zero-SMT algebraic passes proved by existing `linear_mba_mod2w`, `semilinear_mba_mod2w`, and `ring_mod2w`.

---

## 1. Factored Linear-MBA Reconstruction in `src/greysynth/norm_linear.ml` (Targets `148` Near-Exact `mba_flatten` + `58` `pldi_poly` + `31` `pldi_nonpoly` + `22` `qsynth_ea` + `23` `neureduce`!)

Forensic inspection of the new `1,650`-row non-exact frontier showed **>250 remaining cases** (`mba_flatten__line_0001870`: `out=34, gt=11`; `pldi_poly__line_0000682`: `out=41, gt=21`; `pldi_nonpoly__line_0000873`: `out=34, gt=11`) are **exact small-variable linear MBAs whose truth table `norm_linear.ml` ALREADY computed**, but reconstructed as unfactored flat sums of AND-monomials:
- Example (`mba_flatten__line_0001870`, `out = 34 -> gt = 11`):
  `(-5) + 5*(x & z) - 5*(b & ~z) + 10*(b & x) - 5*z - 5*(x + (b & (x & z)))`
  Every coefficient is a multiple of `5` AND `target.(0) = -5 <> 0`!
- Look at `src/greysynth/norm_linear.ml` lines 560–588 and 626–650:
  1. Line 561 restricted 2-term Boolean sum synthesis to `Z.equal target.(0) Z.zero && List.length distinct = 4`, completely missing EVERY linear MBA with non-zero constant offset `v0 = target.(0)` OR 3 distinct shifted values `{0, a, -a}` / `{0, a, 2a}`!
  2. Lines 634–650 emitted each Möbius term `scale coefficient term` independently with NO common-coefficient grouping (`c*t1 - c*t2 + c*t3` emitted 3 multiplications by `c` instead of `c * (t1 - t2 + t3)`!) and NO signed-GCD pullout!

**100% General Fixes in `src/greysynth/norm_linear.ml` (all zero-SMT, proved by `linear_mba_mod2w`):**
1. **Non-Zero-Offset Shifted 2-Term & Signed-Difference Boolean Synthesis (`count <= min 4 !c_normalization_max_atoms`, `not !saw_nonlinear`):**
   - Let `v0 = target.(0)` and `shifted.(i) = normalize (Z.sub target.(i) v0)`, with `s_distinct` = sorted distinct values of `shifted` (always includes `0`).
   - Helper `add_offset offset expr`: if `Z.equal offset Z.zero` return `expr` else `E.binary E.Plus (constant width offset) expr`. Also remember the constant-absorption identity: `(-c) + c * B == (-c) * (~B)` (via `demorgan_not B` for `count <= 3`!), saving 2 nodes whenever `offset = normalize (Z.neg c)`!
   - **Case 3 values `{0, a, b}`:**
     - If `Z.equal (normalize (Z.add a b)) Z.zero` (i.e. `{0, a, -a}`): synthesize minimal `B_pos` for `{i : shifted.(i) = a}` and `B_neg` for `{i : shifted.(i) = b}`; offer `add_offset v0 (scale a (E.binary E.Minus B_pos B_neg))` (and with `a`/`b` swapped!).
     - If `Z.equal (normalize (Z.add a a)) b` (i.e. `{0, a, 2a}`, and symmetrically `{0, 2b, b}`): synthesize minimal `B1` for `{i : shifted.(i) = a || shifted.(i) = b}` and `B2` for `{i : shifted.(i) = b}`; offer `add_offset v0 (scale a (E.binary E.Plus B1 B2))`! Also check `v0 = -a`: `scale a (E.binary E.Minus B1 (demorgan_not B2))` and `scale a (E.binary E.Minus B2 (demorgan_not B1))` (using `B - ~B' = B + B' + 1`, wait: `B1 + B2 - 1` -> `B1 - ~B2` is `B1 + B2 + 1`, whereas `-(~B1) + B2` = `B1 + B2 + 1`; check exact sign: `~B = -1 - B`, so `B1 + B2 - 1 == -(~B1) + B2 - 2`? No! `B - 1` is NOT `~B`; rather **`(-1) - B == ~B`**, so `-a - a*B == a*(~B)`, and `a*(~B1) + a*B2 == -a + a*(B2 - B1)`! Check every formula via `offer` + exact `linear_mba_mod2w` proof gate — zero soundness risk!).
     - Also for any 3 distinct values `{0, a, b}`: offer `add_offset v0 (E.binary E.Plus (scale a B_a) (scale b B_b))` where `B_a = {shifted = a}`, `B_b = {shifted = b}`!
   - **Case 4 values `{0, a, b, c}` where `c = normalize (Z.add a b)`:**
     - Generalize existing lines 560–587 to ANY `v0 = target.(0)` (not just `v0 = 0`!): synthesize `B_a` for `{a, c}` and `B_b` for `{b, c}`, and offer:
       - `add_offset v0 (E.binary E.Plus (scale a B_a) (scale b B_b))`
       - If `Z.equal (normalize (Z.add a b)) Z.zero` (wait, then `c = 0`), or if `Z.equal (normalize (Z.sub v0 (Z.neg a))) Z.zero` (`v0 = -a`): try `E.binary E.Plus (scale (normalize (Z.neg a)) (demorgan_not B_a_inv)) (scale b B_b)` where `B_a_inv` is the complement truth table of `B_a` (since `(-a) + a*B_a == (-a)*(1 - B_a) == a*(~B_a_inv)`? Wait: `~X = -1 - X`, so `a*(~X) = -a - a*X`; setting `X = not B_a` gives `a*(~(not B_a)) = -a - a*(1 - B_a)`? No, bitwise `~(not B_a) = B_a`! Wait: over integers mod 2^w, for a Boolean indicator `B in {0, -1}` (NO! Bitwise outputs are in `{0, 1}` per bit, and `~B = -1 - B`!), so `-a + a*B_a = -a*(1 - B_a)` — wait: `1 - B_a` is NOT `~B_a`, rather **`-1 - B_a = ~B_a`**, so **`-a - a*B_a = a*(~B_a)`**! That means whenever `v0 = -a` and the term is `-a * B` (i.e. coefficient `-a`), `-a - a*B == a*(~B)`!).
2. **Coefficient-Grouped & Signed-GCD Möbius Reconstruction (`norm_linear.ml` lines 634–650):**
   - Given the Möbius `coefficients.(0..2^n-1)` array:
     - Convert each non-zero coefficient to its signed representative in `[-2^(width-1), 2^(width-1))`.
     - **Pass A (Group by `|c|`):** Bucket all non-zero terms `(term, sign)` by `abs(signed_coeff)` (including constant `coefficients.(0)` as term `1` if `abs(signed_coeff.(0))` matches an existing bucket!). For each bucket `k`:
       - Build the unscaled signed sum `S_k = (pos_terms) - (neg_terms)` (using `~t` if `-1 - t` appears!).
       - Scale once: `scale k S_k` (saving `2*(bucket_size - 1)` AST nodes!).
       - Offer the balanced sum across all buckets!
     - **Pass B (Signed GCD Pullout):** Compute `g = gcd` of `abs(signed_coeff)` over all non-zero `coefficients.(0..2^n-1)` (when all non-zero `abs(signed_coeff) <= 65536` and `g > 1`). Divide every coefficient by `g`, reconstruct the grouped Möbius sum `E` (and ALSO if `count <= 4`, try the 2-term/3-term/4-term shifted Boolean synthesis on the `target_div_g` array divided by `g` over `Z`!), and offer `scale g E`!

---

## 2. Scalar-Mul & Shift Bitwise-Boundary Consistency in `src/greysynth/norm_linear.ml` (Collapses `tigress_lvl_5__target_1349`, `target_1417`, `target_6350` — ZERO Proof-Kernel Edits!)

Forensic inspection of `tigress_lvl_5__target_1349` (`out=209, gt=5`), `target_1417` (`out=201, gt=5`), and `target_6350` (`out=463, gt=5`) showed WHY they stalled:
- Each contains a compound scalar-scaled term `X = 2 * (Q & P)` or `X = 2 * (P | Q)` (or `(P | Q) << 1`) appearing **BOTH** inside a bitwise operator (`X | Y`, `(~X) ^ Y`, `(~X) & Q`) **AND** in linear position!
- In `src/greysynth/norm_linear.ml`:
  1. `scan_linear` descended through `E.Mul` with constant `k` WITHOUT calling `add_linear node`!
  2. `linear` matched `E.Binary { f = E.Mul; x; y; _ }` with `Some k` **BEFORE** checking `| _ when is_bitwise_linear_atom expression -> atom expression`!
- **Fix (zero proof-kernel edits — `rewrite_proof.ml` ALREADY checks `stop_ids` before `bvmul`/`bvshl`!):**
  1. In `scan_linear`: call `add_linear node` on `E.Mul` with a constant (before descending), AND on `E.Lsl { x; y = E.Cst k }` when `0 < k < width`, also record `canonical_ac_atom (E.binary E.Mul (constant width (Z.shift_left Z.one k)) x)` in `linear_candidates_seen`!
  2. In `linear`: check `if is_bitwise_linear_atom expression then atom expression` **BEFORE** constant-scaled `E.Mul` and constant `E.Lsl`! (Keep `extract_product_scalar` for *non-constant* `E.Mul` BEFORE `is_bitwise_linear_atom` so Round 46's `a * (k * b)` still extracts `k`!).
  3. On `E.Lsl { x; y = E.Cst k }` (`0 < k < width`) when `has_boundary_overlap`: if the equivalent `scaled = canonical_ac_atom (E.binary E.Mul (constant width (1 << k)) x)` is in `bitwise_linear_atoms`, record the `ring_mod2w` bridge `(expression, scaled)` and return `atom scaled`!

---

## 3. Distributive Common-Factor Pullout (`F*B + F*C -> F*(B + C)`) in `src/greysynth/norm_peepholes.ml` & `src/greysynth/normalization.ml` (`mba_obfuscator__target_483`, General Factoring!)

Forensic inspection of `mba_obfuscator__target_483` (`out=1159, gt=9`):
`20 * ((~(0x55555555 | x1)) * (0x55555555 | x1)) + 20 * ((0x55555555 | x1) * (0xaaaaaaaa & x1))`
- Pulling out the common multiplicative factor `20 * (0x55555555 | x1)` yields:
  `20 * (0x55555555 | x1) * ((~(0x55555555 | x1)) + (0xaaaaaaaa & x1))`
- Then `dag-semilinear-mba` immediately collapses `(~(0x55555555 | x1)) + (0xaaaaaaaa & x1)` to **`0xaaaaaaaa`** with **ZERO SMT**!
- **100% General Fix (`common_factor_pullout_candidate`):**
  - Flatten additive sums (`E.Plus` / `E.Minus`, up to 16 terms, `cost expression <= 2048`).
  - For each term, collect its flat multiplicative factors (`E.Mul`, up to 8 factors; include constant scalars!).
  - Look for any pair of terms `(i, j)` sharing a non-empty subset of identical multiplicative factors `shared` whose combined cost is **`>= 3`** (e.g., a compound subexpression `A` of cost `>= 3`, OR a scalar `k` plus a factor `A` of cost `>= 2`)!
  - Replace `(sign_i * shared * rem_i) + (sign_j * shared * rem_j)` with `shared * (sign_i * rem_i + sign_j * rem_j)` (strictly smaller AST cost whenever `cost(shared) >= 3`!).
  - Run in `dag_bottom_up_simplify` (ZERO SMT, proved via `Rewrite.accepts_compositional ~pass:"dag-factor-pullout" ~equalities:[] ~ring_equalities:[ !result, candidate ]`!).

---

## 4. Verification Gate for Round 52 (Target Wall Time: ~10–12 min — Shrunk Datasets!)

1. **Full-Pipeline Regression Tests (`test/round52_test.ml`):**
   - `mba_flatten__line_0001870` (`472 -> <= 11`, ZERO SMT!)
   - `pldi_poly__line_0000682` (`63 -> <= 21`, ZERO SMT!)
   - `tigress_lvl_5__target_1349` (`15770 -> <= 5`!) and `tigress_lvl_5__target_6350` (`4747 -> <= 5`!)
   - `mba_obfuscator__target_483`-style distributive common-factor pullout (`20*(~(M|x)*(M|x)) + 20*((M|x)*(~M&x))` -> strictly reduced via `ring_mod2w` + `semilinear_mba_mod2w`, ZERO SMT!)
   - All independently replayed by `mba_proof`, warning-clean `make test`, **zero edits to `src/proof/rewrite_proof.ml`!**
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r52-*/out.jsonl`, do NOT run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r52-smoke/out.jsonl`): must keep **`62/62` strict decreases, `>= 54/58` exact, `<= 0.80x`, `0` refutations**!
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (**NEW SHRUNK `195` cases!** -> `/tmp/r52-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (**NEW SHRUNK `334` cases!** -> `/tmp/r52-core/out.jsonl` — target: **BIG jump** on `mba_flatten`, `pldi_poly`, `pldi_nonpoly`, `c_mba_obfuscator`, `tigress_l5..l8`!)
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r52-leeky-dev64/out.jsonl`)
3. Record concise Round-52 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
