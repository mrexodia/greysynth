# GreySynth Round-38 Spec: Opaque-Atom Abstract Semantic Interpolation (`probe_opaque_atoms`) + Complementary-Constant Product Peeling & Common `restrict` Lifting

**Baseline:** Round 37 (`8e55272` / `c56c93a` — `Tigress L5 all_non_exact` `25.41x -> 10.33x` with **`+87` new exact GT**, refreshed `core_hard` `24.31x -> 15.60x` with **`+16` new exact GT**, `regression_smoke` `62/62`, `52` exact GT, `0.8910x`).

**Forensic Diagnosis of `/tmp/r37-l5/out.jsonl` (Why `363` Tigress L5 & Multi-Layer `Tigress L6–L8` / `OMVLL` Rows Still Stall):**
Inspecting the exact Round-37 outputs of medium and large stuck expressions (`target_1373`, `target_158`, `target_2968`, `target_3728`, `target_1024`, `target_226`, `target_549`, `target_1499`, `target_2618`, `target_3500`, `target_4671`) revealed **one extraordinarily general, high-leverage architectural win** plus three small cleanup fixes:

1. **Multi-layer nested shift/bitwise MBAs over `1–3` repeated opaque atoms (`target_1373`, `target_158`, `target_2968`, `target_3728`, `target_1024`, `target_226`, `target_549`, and hundreds of `Tigress L5–L8` & `OMVLL` rows!):**
   - Look at `target_158` (`115,776 -> 96`, GT `9`): over the **two** repeated opaque atoms `A = x2*x4 + x0` and `B = x3*x1`, the entire 96-node expression is a nested 2-layer shift-MBA (`2*(((2*(A|B)) | ~(A^B)) << 1) & ...`) that equals **`A + B`**!
   - Look at `target_1373` (`4,264 -> 71`, GT `5`): over the **two** opaque atoms `A = x2` and `B = uext(32)(x0*x1)`, the entire 71-node expression equals **`A + B`**!
   - Look at `target_2968` (`5,664 -> 121`, GT `5`): over `A = x0` and `B = uext(38)(restrict(0, 25) x1)`, the entire 121-node expression equals **`A + B`**!
   - Look at `target_3728` (`30,238 -> 211`, GT `5`): over the **single** repeated opaque atom `A = x0 + x1`, the entire 211-node expression equals **`A - 0x775cd0c7`**!
   - Look at `target_1024` (`10,177 -> 45`, GT `37`): over `A = x0 + (x1 + x5)` and `B = (x2 ror 14) ^ (x2 ror 18) ^ (x2 ror 41)`, the entire expression equals **`A + B`**!
   - **Why current probes missed ALL of them:** `probe_semantic_linear_mba` & `probe_semantic_poly` only probed over **leaf variables** (skipping `target_158` with 5 vars, `target_1024` with 4+ vars, and failing on nonlinear/cast atoms like `uext(32)(x0*x1)`), AND sent the **concrete** expression (with 64-bit multiplications, divisions, and rotates) to Bitwuzla instead of proving the **1–3 variable abstracted identity `E_abs(p_1, ..., p_k) == C_abs(p_1, ..., p_k)`** (which contains ZERO nonlinear multiplies/divisions and proves in **`5–30 ms`** via `Rewrite_proof` abstract proofs!!)!
2. **Three small concrete gaps spotted in `/tmp/r37-l5/out.jsonl`:**
   - **Complementary constant in zero-SMT product peeling (`target_1499`, `target_5511`, `target_3168`):** `((x1 & 0x3e) * (x1 | 0x3e)) + ((x1 & 0xffffffffffffffc1) * ((~x1) & 0x3e))` needs complementary constant `C1, C2` (`C2 == ~C1`) matching in `nonlinear_product_identity_candidate` — plus check why `target_2618` (`((~A & B) * (~B & A)) + ((B | A) * (B & A))`, `to=0`, size 17) didn't fire `local_candidates` after OES/CHS!
   - **`abstract_slice_candidate` not wired into `local_candidates` (`target_3500`, `to=0`, size 13):** `restrict(0, 31) (0xffffffff00000000 | ((x0/x1) * ...))` finished at size 13 (`<= 256`, skipping `dag_bottom_up_simplify`) and never hit `abstract_slice_candidate`!
   - **Common `restrict(lo, hi)` factoring out of bitwise `|`/`&`/`^` (`target_4671`, `4191`, `4192`, `4785`):** `(restrict(0, 7) (~B & A)) | (restrict(0, 7) B)` $\to$ `restrict(0, 7) ((~B & A) | B)` $\to$ `restrict(0, 7) (A | B)` (exact GT size 7!).

---

## 1. Opaque-Atom Abstract Semantic Interpolation (`probe_opaque_atoms`, `src/greysynth/norm_probes.ml`, `src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

**100% General, Strictly Proof-Gated Algorithm:**
Given an expression `expression` with `cost expression >= 9 && cost expression <= 512` and `dag_size_bounded ~limit:256 expression <= 256`:

1. **Extract maximal opaque base atoms `{a_1, ..., a_k}` (`1 <= k <= 3`) using DAG frequency + operator boundaries:**
   - First pass (DAG frequency count): count how many times each unique subexpression of width `w = E.sizeof expression` appears in `expression`.
   - Second pass (top-down abstraction walk through linear/bitwise/constant-shift shell `+`, `-`, `* C`, `<< C`, `&`, `|`, `^`, `~`):
     - Stop and record a subtree `node` as an opaque atom when:
       - **(a)** `node` is a non-shell node (`E.Var`, non-const `E.Mul`, `E.Udiv`, `E.Sdiv`, `E.Urem`, `E.Srem`, `E.Lsr`, `E.Asr`, `E.Rol`, `E.Ror`, `E.Uext`, `E.Sext`, `E.Restrict`, `E.Ite`, variable shift), OR
       - **(b)** `node` is a compound subexpression (`cost node >= 3`, width `w`) that appears **`>= 2` times** in `expression` AND occurs directly beneath a bitwise/shift operator (`&`, `|`, `^`, `~`, `<<`) or as a shared leaf of a `<= 2`-atom structure (e.g., `A = x2*x4 + x0` in `target_158`, `A = x0 + x1` in `target_3728`, `A = x0 + (x1 + x5)` and `B = (x2 ror 14) ^ ...` in `target_1024`)!
     - **Two clean abstraction levels (try both if `1 <= k <= 3`!):**
       - *Level 1 (strict operator boundary):* stop ONLY at non-shell nodes (`Var`, `Mul`, `Div`, `Cast`, `Shift-right`, `Rotate`, `Ite`).
       - *Level 2 (shared-subterm boundary):* ALSO stop at maximal repeated subtrees (`freq >= 2`, `cost >= 3`, width `w`) that are NOT themselves single-var constants — whenever Level 1 yields `> 3` atoms OR fails to find a strictly cheaper candidate!
   - Abort cleanly if `k = 0` or `k > 3`, or if the abstracted expression `abstract_expr` has `size_of_expr abstract_expr <= 3` (already minimal).
2. **Replace each `a_i` with a fresh typed variable `p_i` of width `w`**, producing `abstract_expr(p_1, ..., p_k)`.
3. **Generate untrusted candidate expressions `cand_abs(p_1, ..., p_k)` in `< 1 ms` using our existing interpolation engines on `abstract_expr`:**
   - **Boolean-corner `{0, 1}^k` Möbius + structured linear MBA synthesis (`probe_semantic_linear_mba`):** recovers `p1 + p2`, `p1 - p2`, `p1 | p2`, `p1 & p2`, `p1 ^ p2`, `~p1`, `c1*p1 + c2*p2 + c0`, etc.!
   - **1-variable analytical XSMIR (`Smir_interp.analytical_candidates`) when `k = 1`:** recovers `p1 + C`, `p1 - C`, `p1 ^ C`, `p1 & C`, `p1 | C`, `a*p1 + b`, `(p1 & M) + C`, etc.! (Directly solves `target_3728 -> A - 0x775cd0c7` and `target_226`!)
   - **2-variable affine-constant / semi-linear probe when `k = 1..2`:** evaluate `abstract_expr` on 16 random full-width samples of `(p_1, ..., p_k)` and ALSO test simple `p1 + p2 + C`, `p1 - p2 + C`, `(p1 | p2) + C`, `(p1 & p2) + C`, `(p1 ^ p2) + C` (recovering `C = f(0, 0)` directly!)!
   - **Polynomial probe (`probe_semantic_poly`) when `k <= 2`:** recovers `p1 * p2`, `a*p1^2 + b*p1 + c`, etc.!
4. **Fast full-width sample filter on `abstract_expr` (`16` random full-width samples of `p_1..p_k`, `< 0.1 ms`!):** discard immediately if ANY sample disagrees or if the instantiated candidate `cand_concrete = subst (p_i -> a_i) cand_abs` does NOT strictly reduce `cost` (`cost cand_concrete < cost expression`).
5. **Proof-gated acceptance (`Rewrite.accepts` with strict budget `~timeout:0.25`):**
   - **CRITICAL:** Prove the **abstracted** equality `abstract_expr == cand_abs` (remember `Rewrite.accepts` already tries generalized/abstract proof FIRST, OR pass it explicitly so `Rewrite_proof` records the abstract proof over `p_1..p_k` — containing ZERO `Mul`/`Udiv`/`Ror` from `a_i`, so Bitwuzla proves `target_158`, `target_1373`, `target_2968`, `target_3728`, `target_1024` in **`5–30 ms`** and `mba_proof` independently replays it as `abstract_proofs`!!)!
   - **NEVER** accept without a strict Bitwuzla/compositional proof; `Unknown`/`Timeout` is ALWAYS rejected!
6. **Where to wire `probe_opaque_atoms`:**
   - Inside `dag_bottom_up_simplify` (when `not minimal && cost !result >= 9 && cost !result <= 256` with a `0.3s` cumulative per-pass cap on abstract-probe attempts so it can never slow down giant DAGs!), AND
   - At root in `run_preprocessing` (`run_root_semantic_probes`, for `cost !best <= 512`, `dag_size <= 256`, `0.5s` local budget), AND
   - In post-CHS cleanup (`run_cleanup`) when `cost !best >= 9 && cost !best <= 256`!

---

## 2. Three High-Signal Local Cleanup Fixes (`src/greysynth/norm_nonlinear.ml`, `src/greysynth/norm_peepholes.ml`, `src/greysynth/norm_probes.ml`, `src/greysynth/greysynth.ml`)

1. **Complementary-constant zero-SMT product peeling & post-CHS cleanup (`target_1499`, `target_5511`, `target_2618`):**
   - In `nonlinear_product_identity_candidate` (`norm_nonlinear.ml`): also match `((a & C1) * (a | C1)) + ((a & C2) * ((~a) & C1))` (and all commuted operand orders!) whenever `C1, C2` are constants with `C2 == ~C1`, emitting the exact same zero-SMT `linear_mba_mod2w` + `ring_mod2w` proof for `a * C1`!
   - Check why `target_2618` (`1705 -> 17`, `to=0`) stopped at `((~A & B) * (~B & A)) + ((B | A) * (B & A))`: make sure `run_cleanup` (post-CHS) and `Normalization.run` invoke `nonlinear_product_identity_candidate` (and fix any `parse_cross` operand-order mismatch when BOTH factors have `(~x) & y` with `~` on the left!).
2. **Wire `abstract_slice_candidate` into `local_candidates` (`norm_probes.ml`):**
   - Expose `abstract_slice_candidate` in `local_candidates` (with `timeout:0.15` abstract proof!) so small roots like `target_3500` (`size = 13 <= 256`) collapse `restrict(0, 31) (0xffffffff00000000 | E) -> restrict(0, 31) E` cleanly!
3. **Factor common `restrict(lo, hi)` out of bitwise `|`/`&`/`^` (`norm_peepholes.ml`):**
   - Add `(restrict(lo, hi) X) | (restrict(lo, hi) Y) -> restrict(lo, hi) (X | Y)` (and `&`, `^`) to `peepholes` (strictly reducing AST node count via `allow_equal_cost` or strict cost reduction once the inner `(~B & A) | B -> A | B` simplifies!). Even better: directly simplify `(restrict(lo, hi) X) | (restrict(lo, hi) Y)` when `X` and `Y` simplify inside `restrict(lo, hi) (X | Y)` via `linear_candidates` -> strictly shrinks `target_4671`, `4191`, `4192`, `4785` straight from `10` to **`7` (exact GT)**!

---

## 3. Fast Verification Gate for Round 38 (Target Wall Time: ~6–8 min!)

1. **Unit & Regression Tests (`test/round38_test.ml`):**
   - End-to-end tests with independent `mba_proof` replay covering:
     - `probe_opaque_atoms` on nested 2-layer shift-MBA over 2 opaque nonlinear atoms (`target_158`-style `A = x2*x4 + x0, B = x3*x1` -> `A + B`, proved as `abstract_proofs` in `< 0.1s`!)
     - `probe_opaque_atoms` on 1-atom shared arithmetic subterm (`target_3728`-style `A = x0 + x1` -> `A - 0x775cd0c7`)
     - Complementary-constant zero-SMT product peeling `((x & 0x3e)*(x | 0x3e)) + ((x & ~0x3e)*(~x & 0x3e)) -> x * 0x3e` AND `target_2618`-style `((~A & B)*(~B & A)) + ((B | A)*(B & A)) -> A * B` with `A = sext(24) x1<8>, B = sext(24) x0<8>`!
     - `local_candidates` `abstract_slice_candidate` on `restrict(0, 31) (0xffffffff00000000 | ((x0/x1) * (x2/x3))) -> restrict(0, 31) ((x0/x1) * (x2/x3))`
     - Common `restrict` factoring `(restrict(0, 7) ((~B) & A)) | (restrict(0, 7) B) -> restrict(0, 7) (A | B)`
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r38-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` cases — target: big jump past **`140+`** new exact GT and slash geomean from `10.33x` well below `6x`!)
   - **`datasets/hard_cases/core_hard/`** (`353` cases — target: big jump in exact GT and slash geomean from `15.60x`!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — must stay `62/62` established, `0` refuted, `<= 0.95x`!)
3. Record concise Round-38 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
