# GreySynth Round-57 Spec: AC-Unified Zero-SMT `gf2_masked_xor_candidate` + `run_preprocessing` / `dag_bottom_up_simplify` Partial-Work Preservation + Zero-Recursion `lowk` Dead-Branch Annihilation + `c + c*B -> (-c)*(~B)` & `{x,y,x|y}` Linear Reconstruction

**Baseline:** Round 56 (`96983e96` — zero-SMT `gf2_masked_xor_equal` proof-kernel fast path audited 100% sound; **ALL-TIME RECORDS**: `dev_64` **`521/880` exact & `1.8885x`** with `mba-capabilities-v1` `2.33x -> 1.74x`; refreshed `core_hard (328)` **`5.29x`**; `regression_smoke` **`56/58` exact, `62/62` strict, `0.8018x`**; **`0` refutations** across all 1,444 cases!).

**Scope Note:** Zero `src/proof/rewrite_proof.ml` edits needed in Round 57! Everything below is 100% producer-side and reuses our existing sound proof rules (`semilinear_mba_mod2w`, `linear_mba_mod2w`, `ring_mod2w`, and local abstract SMT).

---

## 1. AC-Unified `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml` + `greysynth.ml` + `normalization.ml`)

- In Round 56, `gf2_masked_xor_equal` in `rewrite_proof.ml` cut `mba-capabilities-v1` from `2.33x -> 1.74x`, but `aa47d91d545f26c8_w64` (`12,344 -> 1,165`), `200901a16ddf2503_w64` (`13,092 -> 1,261`), `c731a7cf74ac2d9b_w64` (`6,580 -> 545`), `3e50d423ac3189f6_w64` (`6,200 -> 451`), and `cb67824ea6196472_w64` (`11,925 -> 11,925`) still stalled because identical compound atoms appear in different AC permutations (`((x1 ^ x3) + x2)` vs `(x2 + (x3 ^ x1))`, `(3 + (A + B))` vs `((B + 3) + A)`), multiplying distinct atom count past `48` and blocking cancellation!
- **Fix in `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate`):**
  1. Raise the term cap from `48` -> **`64`** (matching `gf2_masked_xor_equal` in `rewrite_proof.ml`!) and raise the entry guard to `cost expression <= 65_536` and `dag_size_bounded ~limit:8192 expression <= 8192`.
  2. Add a small DAG-memoized AC canonicalizer for opaque atoms (bounded to `<= 8` flattened operands per operator, recursing cleanly through `+`, `*`, `&`, `|`, `^`):
     - Flatten and sort `+` / `*` operands -> record `(original, canonical)` in `ring_edges` + `replacements`.
     - Flatten and sort `&` / `|` / `^` operands -> record `(original, canonical)` in `linear_edges` + `replacements`.
     - Canonicalize every opaque atom BEFORE interning it in `parse`!
  3. Build `rewritten_source` via a cycle-guarded memoized substitution of `replacements` on `expression` (same pattern as `norm_linear.ml:809-837`).
  4. Return `Some (candidate, List.rev !ring_edges, List.rev !linear_edges, rewritten_source)`!
  5. Update the three call sites (`root-gf2-masked-xor` & `post-dag-gf2-masked-xor` in `src/greysynth/greysynth.ml`, `dag-gf2-masked-xor` in `src/greysynth/normalization.ml`) to certify **100% ZERO-SMT** via:
     ```ocaml
     Rewrite.accepts_compositional ~pass:...
       ~equalities:[] ~ring_equalities ~linear_mba_equalities
       ~semilinear_mba_equalities:[ rewritten_source, candidate ]
       source candidate
     ```
     (NO SMT fallback! Zero timeout risk!)

---

## 2. Seal ALL Timeout Partial-Work Discards & Replace `dag-bitwise-ac` `<= 128` Cutoff with `<= 256` + `<= 32` Call Cap (`src/greysynth/greysynth.ml` & `src/greysynth/normalization.ml`)

- Forensic proof-certificate inspection of `r56-l5` proved **BOTH** causes of the R55/R56 L5 regression (`11.58x -> 13.51x`):
  - `target_2266` (`162,571 -> 162,571`, was `107` in R54) and `target_1461` (`54,590 -> 54,590`, was `222` in R54) BOTH ran `root-polysim-poly-mod2w`, collapsed to ~200 nodes, and then hit `Timeout_exception` later inside `run_preprocessing` — unwinding out of `run_preprocessing` and throwing away `!best`! Same exact bug on `2dda45799bcf74a9_w64` (`mba-frontier64-v1`, 810 proved steps discarded!) and `7a3c5b5205027e63_w64` (`mba-stress64-v1`, 253 proved steps discarded!).
  - `target_5334` (`7 -> 102`) needed `30` `dag-bitwise-ac` steps in the `129..256` cost range that R55's `(not zero_smt || cost !result <= 128)` cut off, whereas `2dda4579` and `7a3c5b52` ran `541` and `207` `dag-bitwise-ac` steps!
- **Fixes:**
  1. In `src/greysynth/greysynth.ml` (`run_preprocessing`): wrap the ENTIRE body after `let best = ref input in` in:
     ```ocaml
     try
       ...
       !best
     with Timeout_exception ->
       g_has_timedout := true;
       !best
     ```
     So `Timeout_exception` inside `run_preprocessing` can **NEVER** discard `!best`!
  2. In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`):
     - Wrap `semantic_child` AND child recursion (`visit x`, `visit y`, `visit c`, etc.) in `try ... with Timeout_exception -> soft_stopped := true; node`.
     - Check `if not (should_stop ()) then ...` before every heavy per-node step (`dag-linear-mba`, `dag-gf2-masked-xor`, `dag-semilinear-mba`, `dag-minterm-ring-poly`, `dag-semantic-probe`, `dag-poly-mod2w`, `dag-ring-not-mod2w`, `dag-bitwise-ac`, `dag-ring-mod2w`).
     - In `dag-bitwise-ac` (`normalization.ml:407`): **REMOVE** `(not zero_smt || cost !result <= 128)` (restore `cost !result <= 256`!) and instead add a `bitwise_ac_calls = ref 0` counter capped at `!bitwise_ac_calls < 32` per `dag_bottom_up_simplify` pass (incrementing on each attempted/accepted `dag-bitwise-ac` rewrite)!

---

## 3. Zero-Recursion 2-Edge Dead-Branch Annihilation in `lowk_restrict_pushdown` & `bit0_restrict_pushdown` (`src/greysynth/norm_peepholes.ml` & `src/greysynth/norm_probes.ml`)

- Currently `lowk_restrict_pushdown` (`norm_peepholes.ml:668-698`) emits `E.binary E.Mul (low y) zero`, `E.binary E.And (low y) zero`, `E.binary E.Or (low y) fill`, and `E.binary E.And (low x) zero`, which **recurses into the dead subtree `y`** AND prevents `simp_add`/`simp_sub`/`simp_mul`/`simp_and`/`simp_or`/`simp_xor` from recognizing `is_zero`/`is_fill` — stalling all **23 remaining `mba-ladders-v1` cases** (`0c7ee9bf12c23841_w64`, `b17c84ccbe3ed7c6_w64`, `3e4ccbc2f3672749_w64`, etc.)!
- **Fix:**
  - In `lowk_restrict_pushdown` (`norm_peepholes.ml:589-713`): track `ring_equalities = ref []` and `linear_mba_equalities = ref []` alongside `equalities = ref []`.
  - On any annihilated node:
    - `Mul(Cst, y)` or `Mul(y, Cst)` with `divisible value`: DO NOT call `low y`! Emit `bridge = E.binary E.Mul (E.restrict ~lo:0 ~hi y) zero`, record `(lhs, bridge)` in `equalities` (abstracts `y` as a single opaque leaf -> `< 0.1 ms`!) and `(bridge, zero)` in `ring_equalities` (ZERO SMT!), set `annihilated := true`, and return **`zero`** directly!
    - `And(Cst, y)` or `And(y, Cst)` with `divisible value`: DO NOT call `low y`! Emit `bridge = E.binary E.And (E.restrict ~lo:0 ~hi y) zero`, record `(lhs, bridge)` in `equalities` and `(bridge, zero)` in `linear_mba_equalities`, set `annihilated := true`, and return **`zero`** directly!
    - `Or(Cst, y)` or `Or(y, Cst)` with `full value`: DO NOT call `low y`! Emit `bridge = E.binary E.Or (E.restrict ~lo:0 ~hi y) fill`, record `(lhs, bridge)` in `equalities` and `(bridge, fill)` in `linear_mba_equalities`, set `annihilated := true`, and return **`fill`** directly!
    - `Lsl(x, Cst)` with `count >= width`: DO NOT call `low x`! Emit `bridge = E.binary E.And (E.restrict ~lo:0 ~hi x) zero`, record `(lhs, bridge)` in `equalities` and `(bridge, zero)` in `linear_mba_equalities`, set `annihilated := true`, and return **`zero`** directly!
  - Skip the outer `if not (E.is_equal lhs result) then equalities := (lhs, result) :: !equalities` for those 4 annihilated cases (already connected via `lhs -> bridge -> zero/fill`!).
  - Do the exact same 2-edge dead-branch fix for `bit0_restrict_pushdown` (`hi = 0`), and propagate `extra_linear` + `extra_ring` into `lowk_restrict_homomorphism_candidate` (`src/greysynth/norm_probes.ml:18-49`)!

---

## 4. Universal Two's-Complement Constant Absorption `c + c * B -> (-c) * (~B)` & 2-Variable `{x, y, x | y}` Basis (`src/greysynth/norm_linear.ml`)

- In `src/greysynth/norm_linear.ml`:
  1. Add a helper `offer_with_complement_absorption offset terms` for `(offset : Z.t)` and `(terms : (Z.t * E.t) list)`:
     - Filter out zero-coefficient terms and always offer `offset + sum_i (scale c_i b_i)`.
     - Whenever `not (Z.equal offset Z.zero)`, for each term `(c_j, b_j)` where `Z.equal c_j offset`:
       - Replace `offset + offset * b_j` with `scale (normalize (Z.neg offset)) (demorgan_not b_j)` and offer the constant-free sum! (Universal identity `c + c * B == (-c) * (~B)` mod `2^w`, automatically covering `1 + B -> -(~B)` and `-1 - B -> ~B`, e.g. `x1 - (x0 + 1) -> x1 + (~x0)`!)
  2. Call `offer_with_complement_absorption` in:
     - The 2/3/4-value shifted reconstructor (`norm_linear.ml:600-645`),
     - A 5-line 2-variable (`count = 2`) `{x, y, x | y}` basis right next to it: with `v01 = shifted.(1)`, `v10 = shifted.(2)`, `v11 = shifted.(3)`, compute `c_x = normalize (Z.sub v11 v01)`, `c_y = normalize (Z.sub v11 v10)`, `c_or = normalize (Z.sub (Z.add v10 v01) v11)`, and pass `[ c_x, atoms.(0); c_y, atoms.(1); c_or, E.binary E.Or atoms.(0) atoms.(1) ]` to `offer_with_complement_absorption offset`,
     - The Möbius-inversion reconstructor (`norm_linear.ml:720-736`, when `not (Z.equal coefficients.(0) Z.zero)` and non-zero terms `<= 4`)!

---

## 5. Verification Gate for Round 57

1. **Full-Pipeline Regression Tests (`test/round57_test.ml`, plus `make test` warning-clean 100% green):**
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 45`, `< 1.0s`, ZERO SMT, independent `mba_proof` replay!)
   - `200901a16ddf2503_w64` (`mba-capabilities-v1`: `13,092 -> <= 49`, `< 1.0s`, ZERO SMT, independent `mba_proof` replay!)
   - `0c7ee9bf12c23841_w64` (`mba-ladders-v1`: `100 -> <= 20`, independent `mba_proof` replay!)
   - `7a3c5b5205027e63_w64` (`mba-stress64-v1`: `3,066 ->` strict major reduction, no `in == out` partial-work discard!)
   - `mba_obf_nonlinear__line_0000860` (`<= 10`), `mba_obf_nonlinear__line_0000892` (`<= 7`), and `tigress_lvl_5__target_1802` (`4` exact)!
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r57-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r57-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.80x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r57-leeky-dev64/out.jsonl` — target: **`mba-capabilities-v1` `34 -> 55+/71`, `mba-ladders-v1` `49 -> 68+/72`, `mba-stress64-v1` & `mba-frontier64-v1` big drops, overall `dev_64 >= 565/880` exact & `<= 1.60x`!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`170` shrunk cases -> `/tmp/r57-l5/out.jsonl` — recover `target_2266`, `target_1461`, `target_5334`, target `< 10.5x`!)
   - **`datasets/hard_cases/core_hard/`** (`328` refreshed cases -> `/tmp/r57-core/out.jsonl` — target `>= 35` exact & `< 4.8x`!)
3. Record concise Round-57 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
