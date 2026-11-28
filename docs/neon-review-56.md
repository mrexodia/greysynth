# GreySynth Round-56 Spec: Zero-SMT `GF(2)` Masked-XOR Proof Fast Path + Partial-Work Timeout Preservation + Zero-Recursion `lowk` Dead-Branch Annihilation + Universal `c + c*B -> (-c)*(~B)` & `{x,y,x|y}` Linear Reconstruction

**Baseline:** Round 55 (`e0ed661c` / `354cb41` — `regression_smoke`: **ALL-TIME RECORD `56/58` exact, `62/62` strict, `0.8018x`**; `dev_64`: **ALL-TIME RECORD `517/880` exact, `1.9111x`**; `0` refutations across all 1,444 cases).

**Why Round 55 Left Huge Wins on the Table (Forensic Root Causes):**
1. **Section 1 of Round 55 (`gf2_masked_xor_equal` in `src/proof/rewrite_proof.ml` + AC-unified `gf2_masked_xor_candidate`) was NOT implemented in `e0ed661c`**, and adding `post-dag-gf2-masked-xor-smt ~timeout:0.50` without the zero-SMT kernel fast path stole 0.50s+ from borderline 4.9s `Tigress L5` & `core_hard` cases (`target_2266: 107 -> 162,571`, `target_1461: 222 -> 54,590`, `tigress_lvl_8__target_1481: 259 -> 153,612`, `mba_obfuscator__target_5641: 61 -> 29,053`), pushing them over the 5.0s cliff!
2. **`run_preprocessing` (`src/greysynth/greysynth.ml`) has NO `try ... with Timeout_exception -> g_has_timedout := true; !best` wrapper**, and `dag_bottom_up_simplify` (`src/greysynth/normalization.ml:153-171`) runs `visit x`, `visit y`, and `semantic_child` OUTSIDE `try ... with Timeout_exception` and never checks `should_stop ()` between per-node passes — so ANY 5.0s timeout discards ALL partial progress (`in == out`), including **810 proved steps** on `2dda45799bcf74a9_w64` (`mba-frontier64-v1`) and **253 proved steps** on `7a3c5b5205027e63_w64` (`mba-stress64-v1`)! Plus `dag-bitwise-ac` fired **541 times** on `2dda4579` and **207 times** on `7a3c5b52`!
3. **`lowk_restrict_pushdown` (`src/greysynth/norm_peepholes.ml:668-695`) emits `E.binary E.Mul (low y) zero` instead of `zero`** (and `And (low y) zero`, `Or (low y) fill`) — recursing into the entire dead subtree `y`, keeping it alive so `simp_add`/`simp_xor`/`simp_or`/`simp_and` NEVER annihilate it, and blowing the 0.15s SMT timeout on all **24 remaining `mba-ladders-v1` cases** (`0c7ee9bf12c23841_w64`, `b17c84ccbe3ed7c6_w64`, etc.)!
4. **`norm_linear.ml` misses two 100% general two's-complement / 2-var basis identities:**
   - **`c + c * B == (-c) * (~B)`** (which generalizes R54's `1 + B -> -(~B)` to arbitrary `c`, including `c = -1` -> `-1 - B == ~B` so `x1 - (x0 + 1) -> x1 + (~x0)`!) — saves 2–3 AST nodes across `mba_obf_nonlinear` (`lines 639, 860, 879`), `neureduce` (`line 445`), `mba_flatten`, and `Tigress L5` (`target_1802`).
   - **2-variable `{x, y, x | y}` basis**: `c_x * x + c_y * y + c_or * (x | y)` where `c_x = v11 - v01`, `c_y = v11 - v10`, `c_or = v10 + v01 - v11` — turns `6*y + 5*(~y & x)` (cost 10) into `y + 5*(x | y)` (cost 7) and `1 + b + 2*(x & ~b)` (cost 10) into `1 + 2*(x | b) - b` (cost 9)!

---

## 1. Zero-SMT Linear-Time `GF(2)` Masked-XOR Fast Path in `semilinear_mba_equal` (`src/proof/rewrite_proof.ml`) + AC-Unified `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml`) + Remove `0.50s` Root/Post-DAG SMT Fallbacks (`src/greysynth/greysynth.ml`)

1. **In `src/proof/rewrite_proof.ml` (at the top of `semilinear_mba_equal g left right`, AFTER `width <> (node g right).width` and `width > 128`, ZERO certificate format changes!):**
   - Add a 35-line, **100% sound** DAG-memoized `gf2_masked_xor_equal g left right` helper BEFORE the `max_atoms = 6` truth-table path:
     - Represent each node `id` by `(const_mask : Z.t, terms : (int * Z.t) list)` (sorted by `Int.compare` on `id`, normalized mod `2^width`, strictly dropping any `(id, Z.zero)` entry, bounded by `max_atoms = 64`, `max_visited = 16_384`, `max_ops = 2_000_000`):
       - `Value _, E.Cst v` -> `(Bitvector.value_of v, [])`
       - `Unary ("bvnot", [], x)` -> `(Z.logxor cx mask, tx)`
       - `Binary ("bvxor", x, y)` -> `(Z.logxor cx cy, xor_merge tx ty)`
       - `Binary ("bvand", x, y)` where one child is `E.Cst m` -> `(Z.logand c m, mask_terms m t)`
       - `Binary ("bvor", x, y)` where one child is `E.Cst m` -> `(Z.logor (Z.logand c (Z.logxor mask m)) m, mask_terms (Z.logxor mask m) t)`
       - `Binary (("bvor" | "bvand") as op, x, y)` where `Z.equal (Z.logand (active left_form) (active right_form)) Z.zero` (with `active (c, t) = List.fold_left (fun a (_, m) -> Z.logor a m) c t`):
         - `op = "bvand"` -> `(Z.zero, [])`
         - `op = "bvor"` -> `(Z.logxor cx cy, xor_merge tx ty)`
       - Any other node `id`: opaque atom `(Z.zero, [ id, mask ])`!
     - **Soundness invariant (CRITICAL):**
       - Never skip `width` checks! Check `(node g left).width = (node g right).width` first.
       - Never treat `bvor`/`bvand` as `bvxor`/`0` unless `Z.equal (Z.logand (active left_form) (active right_form)) Z.zero`.
       - Return `Ring_equal` **ONLY** when `Z.equal c_left c_right` AND `t_left` and `t_right` have identical `(id, mask)` sorted lists!
       - If not equal or limit exceeded, fall through cleanly to the existing `semilinear_mba_equal` truth-table verifier!
   - **MANDATORY PROOF-KERNEL TESTS (`test/proof_test.ml`):**
     - **Positive test:** 10-opaque-atom masked-XOR + disjoint-OR cancellation identity (well above `max_atoms = 6`!) proves via `semilinear_mba_mod2w` in `< 5 ms` AND independent `mba_proof` replay passes!
     - **Negative test 1:** Unequal mask (`(a & 0x55) ^ (a & 0x54) == 0`) REJECTED by `semilinear_mba_mod2w` AND Bitwuzla `U.No`!
     - **Negative test 2:** Non-disjoint OR (`((a & 0x3) | (b & 0x6)) == ((a & 0x3) ^ (b & 0x6))`, overlapping bit 1!) REJECTED by `semilinear_mba_mod2w` AND Bitwuzla `U.No`!
2. **In `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate`) & `src/greysynth/greysynth.ml` / `src/greysynth/normalization.ml`:**
   - Before interning an opaque atom `atom` in `gf2_masked_xor_candidate`, AC-canonicalize `atom` under `+`, `*` (recording `ring_equalities`) and `&`, `|`, `^` (recording `linear_mba_equalities`) via a small bounded memoized helper (e.g. `<= 6` flattened terms, recording `replacements` and building `rewritten_source` with a cycle-guarded substitution — identical to `norm_linear.ml`!).
   - Return `Some (candidate, ring_equalities, linear_mba_equalities, rewritten_source)` so callers certify in **`< 10 ms` WITH ZERO SMT** via `Rewrite.accepts_compositional ~pass:"root-gf2-masked-xor" ~equalities:[] ~ring_equalities ~linear_mba_equalities ~semilinear_mba_equalities:[ rewritten_source, candidate ]`!
   - **REMOVE** the `|| Rewrite.accepts ~timeout:0.50 ~pass:"root-gf2-masked-xor-smt"`, `~pass:"post-dag-gf2-masked-xor-smt"`, and `~pass:"dag-gf2-masked-xor-smt"` fallbacks (zero-SMT proof ONLY — zero timeout cliff risk on L5 & `core_hard`!).

---

## 2. Seal ALL Timeout Partial-Work Discards & Stop `dag-bitwise-ac` Thrashing (`src/greysynth/greysynth.ml` & `src/greysynth/normalization.ml`)

1. **In `src/greysynth/greysynth.ml` (`run_preprocessing`):**
   - Wrap the body of `run_preprocessing` (right after `let best = ref input in`) with:
     ```ocaml
     try
       ...
       !best
     with Timeout_exception ->
       g_has_timedout := true;
       !best
     ```
     So a `Timeout_exception` anywhere inside `run_preprocessing` can **NEVER** discard `!best`!
2. **In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`):**
   - Wrap `semantic_child` AND the child recursion (`visit x`, `visit y`, `visit c`, etc.) in `try ... with Timeout_exception -> soft_stopped := true; node` so `Timeout_exception` can never escape `dag_bottom_up_simplify`!
   - Check `if not (should_stop ()) then ...` before every heavy per-node step (`dag-linear-mba`, `dag-gf2-masked-xor`, `dag-semilinear-mba`, `dag-minterm-ring-poly`, `dag-semantic-probe`, `dag-poly-mod2w`, `dag-ring-not-mod2w`, `dag-bitwise-ac`, `dag-ring-mod2w`)!
   - Add a `bitwise_ac_calls = ref 0` counter inside `dag_bottom_up_simplify`: cap `dag-bitwise-ac` at `!bitwise_ac_calls < 24` AND skip `dag-bitwise-ac` entirely when `zero_smt && expression_cost > 512`! (Eliminates the `541` / `207` redundant `dag-bitwise-ac` calls on `2dda4579` and `7a3c5b52`!)

---

## 3. Zero-Recursion Dead-Branch Annihilation in `lowk_restrict_pushdown` (`src/greysynth/norm_peepholes.ml:668-713` & `src/greysynth/norm_probes.ml:18-49`)

- In `src/greysynth/norm_peepholes.ml` (`lowk_restrict_pushdown`):
  - Track `ring_equalities = ref []` and `linear_mba_equalities = ref []` alongside `equalities = ref []`.
  - When `low` hits any annihilated branch:
    - `E.Binary { f = E.Mul; x = E.Cst value; y; _ }` or `x, E.Cst value` when `divisible value`:
      - DO NOT call `low y`!
      - Let `bridge = E.binary E.Mul (E.restrict ~lo:0 ~hi y) zero`.
      - Record `equalities := (lhs, bridge) :: !equalities` (abstracts `y` as a single opaque leaf -> `< 0.1 ms`!) AND `ring_equalities := (bridge, zero) :: !ring_equalities` (ZERO SMT!).
      - Set `annihilated := true` and return **`zero`** directly!
    - `E.Binary { f = E.And; x = E.Cst value; y; _ }` or `x, E.Cst value` when `divisible value`:
      - DO NOT call `low y`!
      - Let `bridge = E.binary E.And (E.restrict ~lo:0 ~hi y) zero`.
      - Record `equalities := (lhs, bridge) :: !equalities` AND `linear_mba_equalities := (bridge, zero) :: !linear_mba_equalities`.
      - Set `annihilated := true` and return **`zero`** directly!
    - `E.Binary { f = E.Or; x = E.Cst value; y; _ }` or `x, E.Cst value` when `full value`:
      - DO NOT call `low y`!
      - Let `bridge = E.binary E.Or (E.restrict ~lo:0 ~hi y) fill`.
      - Record `equalities := (lhs, bridge) :: !equalities` AND `linear_mba_equalities := (bridge, fill) :: !linear_mba_equalities`.
      - Set `annihilated := true` and return **`fill`** directly!
    - `E.Binary { f = E.Lsl; x; y; _ }` when `constant_value y` has `count >= width`:
      - DO NOT call `low x`!
      - Let `bridge = E.binary E.And (E.restrict ~lo:0 ~hi x) zero`.
      - Record `equalities := (lhs, bridge) :: !equalities` AND `linear_mba_equalities := (bridge, zero) :: !linear_mba_equalities`.
      - Set `annihilated := true` and return **`zero`** directly!
  - Note: on the outer `if not (E.is_equal lhs result)` line (702), skip re-recording `(lhs, result)` for these 4 annihilated cases since `(lhs, bridge)` + `(bridge, zero/fill)` ALREADY connect `lhs` to `result`!
  - Propagate `extra_linear` and `extra_ring` into `lowk_restrict_homomorphism_candidate` (`src/greysynth/norm_probes.ml`), concatenating them with `linear_mba_equalities` / `ring_equalities`.
  - Also apply the exact same 2-edge dead-branch fix to `bit0_restrict_pushdown` (`norm_peepholes.ml:540-588`) so `hi = 0` gets the same speedup!

---

## 4. Universal Two's-Complement Constant Absorption `c + c * B -> (-c) * (~B)` & 2-Variable `{x, y, x | y}` Basis (`src/greysynth/norm_linear.ml`)

- In `src/greysynth/norm_linear.ml`:
  1. Add a tiny helper `offer_with_complement_absorption offset terms` for any `(offset : Z.t)` and `(terms : (Z.t * E.t) list)`:
     - Always offer the direct `offset + sum_i (scale c_i b_i)`.
     - Whenever `not (Z.equal offset Z.zero)`, for each term index `j` where `Z.equal c_j offset`:
       - Replace `offset + (offset * B_j)` by `scale (normalize (Z.neg offset)) (demorgan_not B_j)` and offer the resulting constant-free sum! (Exact two's-complement identity: `c + c * B == (-c) * (~B)` for all `c, B mod 2^w`, including `c = 1 -> -(~B)` and `c = -1 -> ~B`!)
  2. Call `offer_with_complement_absorption` in:
     - The 2/3/4-value shifted reconstructor (`norm_linear.ml:600-645`),
     - A 5-line 2-variable (`count = 2`) `{x, y, x | y}` basis right next to it: with `v01 = shifted.(1)`, `v10 = shifted.(2)`, `v11 = shifted.(3)`, compute `c_x = normalize (Z.sub v11 v01)`, `c_y = normalize (Z.sub v11 v10)`, `c_or = normalize (Z.sub (Z.add v10 v01) v11)`, and call `offer_with_complement_absorption offset [ c_x, atoms.(0); c_y, atoms.(1); c_or, E.binary E.Or atoms.(0) atoms.(1) ]` (filtering out zero-coefficient terms!),
     - The Möbius-inversion sum (`norm_linear.ml:720-736`, whenever `not (Z.equal coefficients.(0) Z.zero)` and total non-zero terms `<= 4`)!

---

## 5. Verification Gate for Round 56

1. **Proof-Kernel Positive + Negative Soundness Tests (`test/proof_test.ml`):**
   - 10-opaque-atom masked-XOR + disjoint-OR positive test (`< 5 ms`, independent `mba_proof` replay!)
   - Unequal-mask AND overlapping-OR negative tests (both rejected by `semilinear_mba_mod2w` AND Bitwuzla `U.No`!)
2. **Full-Pipeline Regression Tests (`test/round56_test.ml`):**
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 45`, `< 1.0s`, ZERO SMT for GF(2) collapse, independent `mba_proof` replay!)
   - `200901a16ddf2503_w64` (`mba-capabilities-v1`: `13,092 -> <= 49`, `< 1.0s`, independent `mba_proof` replay!)
   - `0c7ee9bf12c23841_w64` (`mba-ladders-v1`: `100 -> <= 20`, independent `mba_proof` replay!)
   - `7a3c5b5205027e63_w64` (`mba-stress64-v1`: `3,066 ->` strict major reduction `< 1000`, no `in == out` partial-work discard!)
   - `mba_obf_nonlinear__line_0000860` (`14 + 14*(~y & x) + 9*y -> <= 10`, via `c + c*B -> (-c)*(~B)`), `mba_obf_nonlinear__line_0000892` (`6*y + 5*(~y & x) -> <= 7`, via `{x, y, x|y}`), and `tigress_lvl_5__target_1802` (`x1 - (x0 + 1) -> 4` exact)!
   - Run `make test` — warning-clean, 100% green!
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r56-*/out.jsonl`, do NOT run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r56-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.80x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r56-leeky-dev64/out.jsonl` — target: **`mba-capabilities-v1` `30 -> 60+/71` (`~1.05x`), `mba-ladders-v1` `48 -> 65+/72`, `mba-stress64-v1` & `mba-frontier64-v1` major drops, overall `dev_64 >= 575/880` exact & `<= 1.55x`!!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`170` shrunk cases -> `/tmp/r56-l5/out.jsonl` — recover all R55 cliff regressions, target `< 11.0x`!)
   - **`datasets/hard_cases/core_hard/`** (`328` refreshed cases -> `/tmp/r56-core/out.jsonl` — target `>= 35` exact & `< 5.0x`!)
4. Record concise Round-56 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
