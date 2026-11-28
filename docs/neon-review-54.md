# GreySynth Round-54 Spec: Exact `GF(2)` Masked-XOR Normalizer + Universal Repeated-Dead-Subterm Abstraction (`mba-capabilities-v1`!) + Universal Zero-SMT Prepass (`mba-frontier64-v1`/`stress64`!) + De Morgan `-(~B)` & General Factor Pullout

**Baseline:** Round 53B (`0dad3c7` / `a251fe0` — **NEW AUTHORITATIVE CORPUS-WIDE SCOREBOARD across 32 suites, 54,105 audited:** **`54,095 / 54,095` (`100.000%`) of all non-GB parseable expressions formally proved (`99.9871%` overall), `0` refutations, `51,284 / 52,648` (`97.409%`) exact `<= GT`**, `98.00% <= 1.25x`, `98.36% <= 2.00x`; `Tigress L5–L8` **`80.15%` exact (`3,206/4,000`: L5 `83.0%`, L6 `82.9%`, L7 `79.5%`, L8 `75.2%`)**; Milestone-53 strictly held-out `mba-balanced-v1` **`120/120` proved, `0` refutations, `0` timeouts, `1.7091x` (down from `2.26x` baseline!)**; `datasets/hard_cases/all_non_exact/` shrunk **`1,650 -> 1,364`** (`tigress_l5`: `170`, `core_hard`: `328`)!).

---

## 1. Exact `GF(2)` Masked-XOR Normalizer (`norm_semilinear.ml`) + Universal Repeated-Dead-Subterm Abstraction in `Rewrite_proof.abstract_pair` (`src/proof/rewrite_proof.ml`) — Crushes `mba-capabilities-v1` (`30/71 -> ~70/71`, `3.06x -> ~1.05x`!)

Forensic inspection of `aa47d91d545f26c8_w64` (`mba-capabilities-v1`, `in = 12,344 -> out = 12,203, ref = 35`) and `200901a16ddf2503_w64` (`in = 13,092 -> out = 12,933, ref = 39`) revealed that the remaining 41 `mba-capabilities-v1` expressions are **pure `GF(2)` masked-XOR trees** (`^`, `~`, `& Cst`, `| Cst`) over opaque compound atoms (`A_1..A_k`):
```
((((((A & M1) ^ B) & M2) ^ (A & M1)) ^ C) & M3) ^ ...
```
1. **Linear-Time Exact `GF(2)` Masked-XOR Normalizer (`gf2_masked_xor_candidate` in `src/greysynth/norm_semilinear.ml`):**
   - For any expression of width `<= 128`, `dag_size <= 4096`, `cost >= 11 && cost <= 32_768`:
   - Memoize over the DAG a representation `(const_mask : Z.t, terms : (E.t, Z.t) list_or_tbl)` denoting `const_mask ^ XOR_i (atom_i & mask_i)` (with all masks normalized mod `2^width` and zero-mask entries deleted; bail out cleanly if `distinct_atoms > 48`):
     - `E.Cst v` -> `(v, {})`
     - `E.Unary { f = E.Not; x }` -> `(const ^ all_ones, terms)`
     - `E.Binary { f = E.Xor; x; y }` -> `(cx ^ cy, xor_merge tx ty)` (canceling any atom whose mask becomes `0`!)
     - `E.Binary { f = E.And; x; y = E.Cst m }` (and commuted) -> `(cx & m, map_masks (fun k -> k & m) tx)`
     - `E.Binary { f = E.Or; x; y = E.Cst m }` (and commuted) -> `((cx & ~m) | m, map_masks (fun k -> k & ~m) tx)`
     - `E.Binary { f = E.Or; x; y }` where both `x` and `y` have **pairwise disjoint active bit-masks** (`(active_x & active_y) == 0`, where `active(c, t) = c | OR_i m_i`): same as `Xor`!
     - `E.Binary { f = E.And; x; y }` where `(active_x & active_y) == 0`: `(0, {})`!
     - Any other node -> opaque atom `(0, { node -> all_ones })`!
   - Reconstruct a compact candidate (only if at least one `^` or `& Cst` or `| Cst` step was simplified and `cost candidate < cost expression`):
     - For each `(atom, mask)` with `mask <> 0`: emit `atom` if `mask = all_ones` else `E.binary E.And atom (constant width mask)`.
     - Combine terms with pairwise-disjoint masks using `E.Or` (or `E.Xor` otherwise; include `const_mask` if non-zero, or fold `all_ones` as `E.Not` if cheaper!).
   - Run `gf2_masked_xor_candidate` both as an early root pass (`run_root_gf2_masked_xor` in `greysynth.ml`, right after `dag_constant_cast_simplify`) AND inside `dag_bottom_up_simplify` (for `cost !result >= 15`), certifying via `semilinear_mba_mod2w` (when `<= 6` atoms) or `Rewrite.accepts ~timeout:0.50`!
2. **Universal-Instantiation Repeated-Dead-Subterm Abstraction in `src/proof/rewrite_proof.ml` (`abstract_pair`, lines 250–305):**
   - **Soundness Theorem (100% Universal Instantiation):**
     Currently `abstract_pair` replaces node `id` with a fresh variable `v_id` of width `current.width` when `occurs_left.(id) && occurs_right.(id)`.
     If a compound node `id` (`current.cost >= 2`) occurs **with `>= 2` parent edges in `left`** (`refcount_left.(id) >= 2`, e.g. a dead nonlinear atom `A` cancelled out by `(A & M) ^ (A & M) == 0`) AND **contains NO node that occurs in `right`** (`not contains_right.(id)`), replacing ALL occurrences of `id` in `left` with a fresh bitvector variable `v_id` of width `current.width` is **100% SOUND by universal instantiation** ($\forall v.\, L[id := v] = R \implies L = R$)!
   - **CRITICAL SOUNDNESS GUARDRAILS:**
     - Never change width (`E.var name current.width name`).
     - Compute `contains_right.(id)` bottom-up (true if `occurs_right.(id)` or any child has `contains_right`). Only abstract a `left`-only repeated node if `refcount_left.(id) >= 2 && not contains_right.(id) && current.cost >= 2` (and not `Variable`/`Value`).
     - If the abstracted query returns `No` or `Timeout`, `prove_equality_with_model` STILL falls back cleanly to concrete Bitwuzla (zero false positives, zero regressions!).
   - **MANDATORY PROOF-KERNEL TESTS (`test/proof_test.ml`):**
     - Positive test: dead nonlinear multiplication `((A & M) ^ (A & M)) ^ x == x` where `A = (x0 + 3) * (x1 ^ 5)` proves via `abstract` in `< 20 ms` (and independent `mba_proof` replay passes!).
     - Negative test: false identity `((A & M) ^ (A & M2)) ^ x == x` with `M <> M2` is REJECTED by BOTH `abstract` AND concrete Bitwuzla (`U.No`)!

---

## 2. Universal `1.2s` Zero-SMT Prepass for All Bitwise Roots (`size > 512`) & Safe Partial-Work Preservation (`src/greysynth/greysynth.ml`, `src/greysynth/normalization.ml`) — Crushes `mba-frontier64-v1` & `mba-stress64-v1` & `target_2233`!

Forensic inspection of `mba-frontier64-v1` (`7507b8965666bc39_w64: in=2119 -> out=2119`, `d4603d6de6798c6d_w64: 2110 -> 2110`), `mba-stress64-v1` (`7a3c5b5205027e63_w64: 3066 -> 3066`), and `tigress_lvl_5__target_2233` (`15899 -> 15899`) showed why they stalled at `in == out`:
- In `greysynth.ml:537`: `let local_budget = if shared then 1.5 else if exposed_product then 1.0 else 0.0` gave **`0.0s`** to non-shared bitwise roots whose `Mul` wasn't within depth 8! They then hit `dag_bottom_up_simplify ~zero_smt:false` and timed out before returning partial work!
- **Fix (100% general):**
  1. In `greysynth.ml:537`: set `local_budget = if shared then 1.5 else if contains_bitwise !best then 1.2 else 0.0` (so ALL bitwise roots with `size > 512 && early_dag_size <= 4096` get a fast zero-SMT `dag_bottom_up_simplify` prepass first!).
  2. In `normalization.ml` (`dag_bottom_up_simplify`): ensure `Config.Timeout_exception` caught inside `visit` sets `soft_stopped := true` and returns `!result` (preserving ALL already-proved memoized subtrees instead of aborting out of `dag_bottom_up_simplify` and discarding partial work!). Also check why `7a3c5b5205027e63_w64` (`3066 -> 3066`) stalled and verify it strictly reduces well under `2.0s`!

---

## 3. De Morgan Two's-Complement `1 + B -> -(demorgan_not B)` (`norm_linear.ml`) + General `cost(shared) >= 1` Factor Pullout (`norm_peepholes.ml`) + Raised `max_monomials` on `dag-ring-not-mod2w` (`norm_poly.ml`)

1. **De Morgan `1 + B -> -(~B)` (`src/greysynth/norm_linear.ml`):**
   - Look at `mba_flatten__line_0000046`, `0000085`, `0000116`, `pldi_nonpoly__line_0000086`: all output `1 + (y & ~x)` (cost 6) vs GT `-(~y | x)` (cost 5)!
   - Whenever `norm_linear.ml` offers `1 + B` (`v0 = 1`, `delta = 1` on lines 487–488 or `add_offset`), ALSO offer `E.unary E.Minus (demorgan_not B)` (and for `-1 - B`, ALSO offer `demorgan_not B`)! Proved in `< 0.1 ms` with ZERO SMT by `linear_mba_mod2w`!
2. **General `cost(shared) >= 1` Distributive Factor Pullout (`src/greysynth/norm_peepholes.ml`):**
   - Lower the shared-factor threshold in `common_factor_pullout_candidate` from `cost(shared) >= 3` down to **`cost(shared) >= 1`** (since `Rewrite.accepts_compositional` already requires strict `cost candidate < cost expression`, e.g. `x1 * x3 - x1 * x2` (cost 7) -> `x1 * (x3 - x2)` (cost 5)!). Immediately closes `mba_obfuscator__target_1565` and dozens of polynomial sums!
3. **Raise `max_monomials` on `ring_not_bridge_candidate` (`256 -> 1024`) in `src/greysynth/norm_poly.ml`:**
   - Allows `96`-bit ring cancellations like `tigress_lvl_5__target_1776` (`568` nodes) to expand and cancel `(~A)*(A&B) + (1+A)*(A&B) -> 0` cleanly with ZERO SMT!

---

## 4. Verification Gate for Round 54 (Target Wall Time: ~12 min!)

1. **Proof-Kernel Positive + Negative Soundness Tests (`test/proof_test.ml`):**
   - Positive & negative Bitwuzla cross-tests for `abstract_pair`'s repeated-dead-subterm universal instantiation!
2. **Full-Pipeline Regression Tests (`test/round54_test.ml`):**
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 39`, `< 1.0s`, independent `mba_proof` replay!)
   - `7507b8965666bc39_w64` (`mba-frontier64-v1`: `2,119 ->` major reduction, no `in == out` stall!)
   - `7a3c5b5205027e63_w64` (`mba-stress64-v1`: `3,066 ->` major reduction, no `in == out` stall!)
   - `mba_flatten__line_0000046` (`-> <= 5`, exact!) and `mba_obfuscator__target_1565` (`-> <= 11`, exact!)
   - Run `make test` — warning-clean, 100% green!
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r54-*/out.jsonl`, do NOT run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r54-smoke/out.jsonl`): must keep **`62/62` strict decreases, `>= 54/58` exact, `<= 0.81x`, `0` refutations**!
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r54-leeky-dev64/out.jsonl` — target: **MASSIVE** jump on `mba-capabilities-v1` `30 -> ~65+/71` (`3.06x -> ~1.1x`!), `mba-frontier64-v1` `19.78x -> < 10x`, `mba-stress64-v1` `5.92x -> < 4.5x`, pushing overall `dev_64` to **`>= 540/880` exact & `<= 1.65x`!!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (**NEW SHRUNK `170` cases!** -> `/tmp/r54-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (**NEW SHRUNK `328` cases!** -> `/tmp/r54-core/out.jsonl`)
4. Record concise Round-54 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
