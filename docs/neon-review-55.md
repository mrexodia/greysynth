# GreySynth Round-55 Spec: Zero-SMT Linear-Time `GF(2)` Masked-XOR Fast Path in `semilinear_mba_equal` + AC-Unified `gf2_masked_xor_candidate` + `e1_5vars` Smoke Fix (`~0.76x` Record!) + `7a3c5b` Partial-Work Preservation

**Baseline:** Round 54 (`863bccc` / `2a822ff` — Leeky `dev_64` **ALL-TIME RECORD `516/880` exact & `1.9197x`** (`mba-capabilities-v1` `3.06x -> 2.21x`, `mba-stress64-v1` `5.92x -> 5.27x`, `mba-interactions-v1` `28/33 @ 0.914x`, `mba-ladders-v1` `50/72`, `mba-composition-v1` `50/54`); refreshed `core_hard (328)` **`+22` more exact** (`c_mba_obfuscator` `+10`, `neureduce` `+5`, `pldi_nonpoly` `+3`); `0` refutations across all 1,444 cases!).

**Forensic Diagnosis of Round 54's THREE Exact Opportunities:**

1. **`regression_smoke` (`0.7995x -> 0.9735x`) was caused by ONE single missing guard (`greysynth.ml:589`):**
   - Every other row of `regression_smoke` IMPROVED in R54 (`mba_obfuscator__target_1561: 13->11`, `omvll__target_3457: 13->11`, `omvll__target_6242: 13->9`, `oses__line_0000240: 795->498`, `pldi_poly__line_0000992: 9->8`!).
   - ONLY `e1_5vars__line_0000432` (`3 -> 919`) and `e1_5vars__line_0000565` (`3 -> 757`) regressed because the new `local_budget = 1.2` prepass ran on pure `linear_mba_compatible` 5-variable expressions BEFORE `run_root_linear_group` collapsed them in 1 ms!
2. **Why `aa47d91d545f26c8_w64` (`mba-capabilities-v1`, `12,344 -> ref=35`) only reached `431` (isolated) / `2,713` (8 workers) instead of `<= 39`:**
   - Proof certificate trace showed `root-gf2-masked-xor` fired **`0` times**!
   - Why? (a) `semilinear_mba_mod2w` has `max_atoms = 6` (`2^k` truth-table!), so a 10–15-atom masked-XOR identity fell back to `Rewrite.accepts ~timeout:0.50` which timed out at 12,344 nodes; (b) `gf2_masked_xor_candidate` didn't AC-canonicalize opaque atoms (`((x1^x3)+(3+x2))` vs `(3+((x1^x3)+x2))`), leaving duplicate terms uncancelled!
3. **Why `7a3c5b5205027e63_w64` (`mba-stress64-v1`, `3,066 -> 3,066`) discarded ALL 254 proved zero-SMT steps:**
   - Proof certificate trace showed `169 dag-bitwise-ac` + `40 dag-bitwise-ac` + `30 dag-linear-mba` + `9 dag-factor-pullout` + `5 dag-semantic-probe-linear` + `1 dag-ring-mod2w` = **254 proved zero-SMT steps**, yet `t = 5.00s` (`has_timed_out = true`) threw away ALL 254 steps because `Timeout_exception` escaped `dag_bottom_up_simplify` before `best := ...` committed!

---

## 1. Zero-SMT Linear-Time `GF(2)` Masked-XOR Fast Path Inside `semilinear_mba_equal` (`src/proof/rewrite_proof.ml`) + AC-Unified `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml`)

1. **In `src/proof/rewrite_proof.ml` (inside `semilinear_mba_equal g left right`, ZERO certificate format changes!):**
   - Before running the `2^k` truth-table loop (and AFTER the `width <> width` and `width > 128` checks!), add a 35-line, **100% sound** DAG-memoized `gf2_masked_xor_equal g left right` fast path:
     - Represent each node `id` by `(const_mask : Z.t, terms : (int, Z.t) list)` (sorted by `Int.compare` on `id`, normalized mod `2^width`, strictly dropping any `(id, Z.zero)` entry, bounded by `max_atoms = 64`, `max_visited = 16_384`, `max_ops = 2_000_000`):
       - `Value v` (when `(node g id).expr = E.Cst v`) -> `(Bitvector.value_of v, [])`
       - `Unary ("bvnot", [], x)` -> `(Z.logxor cx mask, tx)`
       - `Binary ("bvxor", x, y)` -> `(Z.logxor cx cy, xor_merge tx ty)`
       - `Binary ("bvand", x, y)` where one child is `E.Cst m` -> `(Z.logand c m, mask_terms m t)`
       - `Binary ("bvor", x, y)` where one child is `E.Cst m` -> `(Z.logor (Z.logand c (Z.logxor mask m)) m, mask_terms (Z.logxor mask m) t)`
       - `Binary (("bvor" | "bvand") as op, x, y)` where `Z.equal (Z.logand (active left_form) (active right_form)) Z.zero` (where `active (c, t) = List.fold_left (fun a (_, m) -> Z.logor a m) c t`):
         - If `op = "bvand"`: `(Z.zero, [])`
         - If `op = "bvor"`: `(Z.logxor cx cy, xor_merge tx ty)`
       - Any other node `id`: opaque atom `(Z.zero, [ id, mask ])`!
     - **Soundness invariant (CRITICAL):**
       - Never skip `width` checks! Check `(node g left).width = (node g right).width` first.
       - Never treat `bvor`/`bvand` as `bvxor`/`0` unless `Z.equal (Z.logand (active left_form) (active right_form)) Z.zero` (provably disjoint bit positions!).
       - Return `Ring_equal` **ONLY** when `Z.equal c_left c_right` AND `t_left` and `t_right` have identical `(id, mask)` sorted lists!
       - If not equal (or limit exceeded), fall through cleanly to the existing `semilinear_mba_equal` truth-table verifier!
   - **MANDATORY PROOF-KERNEL TESTS (`test/proof_test.ml`):**
     - **Positive test:** 10-opaque-atom masked-XOR + disjoint-OR cancellation identity (well above `max_atoms = 6`!) proves via `semilinear_mba_mod2w` in `< 5 ms` (and independent `mba_proof` replay passes!).
     - **Negative test 1:** Unequal mask (`(a & 0x55) ^ (a & 0x54) == 0`) REJECTED by `semilinear_mba_mod2w` and Bitwuzla `U.No`!
     - **Negative test 2:** Non-disjoint OR (`((a & 0x3) | (b & 0x6)) == ((a & 0x3) ^ (b & 0x6))`, overlapping at bit 1!) REJECTED by `semilinear_mba_mod2w` and Bitwuzla `U.No`!
2. **In `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate`) & `src/greysynth/greysynth.ml`:**
   - Before interning an opaque atom `atom` in `gf2_masked_xor_candidate`, canonicalize `atom` under AC (`+`, `*`, `&`, `|`, `^`) via a small memoized helper (recording `ring_equalities` for `+`/`*` and `linear_mba_equalities` for `&`/`|`/`^` whenever `not (E.is_equal atom canonical)`, and building `rewritten_source` with a cycle-guarded substitution — just like `norm_linear.ml`!).
   - Return `Some (candidate, ring_equalities, linear_mba_equalities, rewritten_source)` so `Rewrite.accepts_compositional ~pass:"root-gf2-masked-xor" ~equalities:[] ~ring_equalities ~linear_mba_equalities ~semilinear_mba_equalities:[ rewritten_source, candidate ]` certifies the ENTIRE 12,344-node collapse in **`< 10 ms` WITH ZERO SMT**!
   - Also run `run_root_gf2_masked_xor ()` BOTH early (right after `dag_constant_cast_simplify`) AND right after `dag_bottom_up_simplify` (and inside `dag_bottom_up_simplify` during `zero_smt = true` with zero SMT!).
   - When reconstructing `candidate` in `gf2_masked_xor_candidate`, if all terms have pairwise-disjoint masks (or a subset does), combine disjoint terms with `E.Or` (same cost as `E.Xor`, matches clean bit-lane form!).

---

## 2. 1-Line `e1_5vars` Smoke Fix (`src/greysynth/greysynth.ml:589`)

- In `src/greysynth/greysynth.ml`:
  Guard the non-shared `1.2s` zero-SMT prepass with `not (Normalization.linear_mba_compatible !best)`:
  ```ocaml
  let local_budget =
    if shared then 1.5
    else if Normalization.has_bitwise_operator !best
            && not (Normalization.linear_mba_compatible !best)
    then 1.2
    else if exposed_product then 1.0
    else 0.0
  ```
- Immediately restores `e1_5vars__line_0000432` (`919 -> 3`) and `e1_5vars__line_0000565` (`757 -> 3`), while keeping ALL R54 improvements (`oses__line_0000240 -> 498`, `mba_obfuscator__target_1561 -> 11`, `omvll__target_3457 -> 11`, `omvll__target_6242 -> 9`) — targeting a **NEW ALL-TIME `regression_smoke` RECORD `<= 0.78x`, `62/62` strict, `>= 55/58` exact!!**

---

## 3. Fix `7a3c5b5205027e63_w64` (`mba-stress64-v1`) Timeout & Partial-Work Discard (`src/greysynth/normalization.ml`)

- Inspect why `7a3c5b5205027e63_w64` (`in = 3,066`, `169 dag-bitwise-ac` + `30 dag-linear-mba` steps!) hit `t = 5.00s` and discarded all 254 proved steps:
  1. In `dag_bottom_up_simplify`: check `deadline` (`if Unix.gettimeofday () >= deadline -. 0.05 then soft_stopped := true`) BEFORE EACH expensive step (`dag-linear-mba`, `dag-semilinear-mba`, `dag-minterm-ring-poly`, `dag-bitwise-ac`, `dag-ring-mod2w`, `dag-factor-pullout`)!
  2. Wrap the child recursion in `visit` with `try ... with Timeout_exception -> soft_stopped := true; node` so `Timeout_exception` can NEVER escape `dag_bottom_up_simplify` and discard memoized proved subtrees!
  3. In `dag-bitwise-ac`: skip `recursive_bitwise_ac_candidate` when `zero_smt = true && cost !result > 128` (or memoize canonicalized subtrees across `visit` calls!) so `7a3c5b5205027e63_w64` doesn't waste 169 redundant `dag-bitwise-ac` proofs before collapsing its linear-MBA factors!
  4. Verify `7a3c5b5205027e63_w64` (`in = 3,066 -> ref = 24`) strictly collapses well under `2.0s` (ideally `< 100` nodes!) in `test/round55_test.ml`!

---

## 4. Verification Gate for Round 55 (Target Wall Time: ~12 min!)

1. **Proof-Kernel Positive + Negative Soundness Tests (`test/proof_test.ml`):**
   - 10-atom masked-XOR + disjoint-OR positive test (`< 5 ms`, independent `mba_proof` replay!)
   - Unequal-mask AND overlapping-OR negative tests (both rejected by `semilinear_mba_mod2w` and Bitwuzla `U.No`!)
2. **Full-Pipeline Regression Tests (`test/round55_test.ml`):**
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 45`, `< 1.0s`, ZERO SMT for the GF(2) collapse, independent `mba_proof` replay!)
   - `200901a16ddf2503_w64` (`mba-capabilities-v1`: `13,092 -> <= 49`, `< 1.0s`, independent `mba_proof` replay!)
   - `7a3c5b5205027e63_w64` (`mba-stress64-v1`: `3,066 ->` major reduction `< 200`, `< 2.0s`, no `in == out` stall!)
   - `e1_5vars__line_0000432` (`-> 3`) and `e1_5vars__line_0000565` (`-> 3`)!
   - Run `make test` — warning-clean, 100% green!
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r55-*/out.jsonl`, do NOT run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r55-smoke/out.jsonl`): **MUST PASS `62/62` strict decreases, `>= 55/58` exact, `<= 0.79x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r55-leeky-dev64/out.jsonl` — target: **MASSIVE** jump on `mba-capabilities-v1` `30 -> ~65+/71` (`2.21x -> ~1.05x`!), `mba-stress64-v1` `5.27x -> < 3.5x`, pushing overall `dev_64` to **`>= 550/880` exact & `<= 1.65x`!!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`170` shrunk cases -> `/tmp/r55-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`328` refreshed cases -> `/tmp/r55-core/out.jsonl`)
4. Record concise Round-55 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
