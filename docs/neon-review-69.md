# GreySynth Round-69 Spec (Fast Sprint Commit 3/4): Post-CHS Zero-SMT Algebraic Cleanup (`src/greysynth/greysynth.ml` & `src/greysynth/norm_linear.ml`)

**Sprint Mode (Fast 4-Commit Cycle, Commit 3/4):** Gate ONLY with targeted regression tests (`test/round69_test.ml`) + warning-clean `make test` + **35-second `regression_smoke` gate (`/tmp/r69-smoke/out.jsonl`)**! Do NOT run `dev_64`, `L5`, `core_hard`, or `heldout_balanced64` until after Commit 4 (R70).

**Scope:** **ZERO `src/proof/rewrite_proof.ml` edits!** ONLY `src/greysynth/greysynth.ml` (and optionally a tiny helper in `src/greysynth/norm_linear.ml`).

---

## Why Post-CHS Zero-SMT Algebraic Cleanup Is a Pure Free Lunch

- Look at `src/greysynth/greysynth.ml:893-913` (`run_passes`):
  - After CHS discovers structural rewrites (for example folding shift+mask combinations into `ror` on SHA-256-like `Tigress L5–L8` targets, or simplifying subtrees down to size `<= 256`), CHS often finishes (or times out on horizon 2 at `t = 5.00s`!) leaving **trivial zero-SMT algebraic simplifications** sitting right in `!best`:
    - Example 1 (`tigress_lvl_5__target_1024`, size `45 -> 37` exact GT!):
      `((((A ^ R1) ^ (R2 ^ R3)) + ((A & (R1 ^ (R2 ^ R3))) << 1)) + Ch)`
      where `A = x0 + (x1 + x5)` and `R1, R2, R3` are `x2 ror 14/18/41`!
      Here `((A ^ R1) ^ (R2 ^ R3)) + ((A & (R1 ^ (R2 ^ R3))) << 1)` is a **4-atom linear MBA** (`A, R1, R2, R3`, with `<< 1 = * 2`!) that collapses straight to **`A + (R1 ^ (R2 ^ R3))`** (`size 37` = EXACT GT!) in `< 1 ms` with ZERO SMT (`linear_mba_mod2w`)!
    - Example 2 (`target_1251` across `c_mba_obfuscator`, `omvll`, and `Tigress L5–L8`, size `9 -> 8` exact GT!):
      `~((((~x1) & x3) ^ x2) - x0)` -> `not_pushdown_candidate` collapses it straight to **`x0 + ((x1 | (~x3)) ^ x2)`** (`size 8` = EXACT GT!) in `< 0.1 ms` with ZERO SMT (`linear_mba_mod2w`)!
    - Example 3 (`tigress_lvl_5__target_1565`, size `13 -> 11` exact GT!):
      `((x1 * x3) + x4) - ((x0 * x5) + (x1 * x2))` -> `common_factor_pullout_candidate` collapses it to **`(x1 * (x3 - x2)) + (x4 - (x0 * x5))`** (`size 11` = EXACT GT!) in `< 0.1 ms` with ZERO SMT (`ring_mod2w`)!
  - Today, NONE of those run after `chs gt best` (especially when `chs` tripped `!g_has_timedout := true` on its final horizon!).

---

## Exact Edits

0. **1-Line Revert in `src/greysynth/greysynth.ml:614` (`local_budget`):**
   - Remove the `size_of_expr !best > 1024 &&` guard added in Round 68 (which regressed `tigress_lvl_8__target_1016` from `9 -> 7,117` on `r68-smoke`!), restoring `else if Normalization.has_bitwise_operator !best && not (Normalization.linear_mba_compatible !best) then 1.2` (keeping ALL the wrapped child-root `gf2_masked_xor` and nested AC `replacements` wins from R68!).

1. **In `src/greysynth/greysynth.ml` (`run_passes`, right after line 904 — after the `try ... chs ... with Timeout_exception` block):**
   Add a bounded, **100% ZERO-SMT** `post_chs_zero_smt_polish` that runs whenever `!c_chs && size_of_expr !best >= 3 && size_of_expr !best <= 256 && dag_size_bounded ~limit:256 !best <= 256` (EVEN IF `!g_has_timedout` became true inside CHS — since this polish is **100% zero-SMT** and strictly bounded to `<= 0.08s`, temporarily saving/restoring `g_has_timedout` / `g_branch_deadline` so `check_timeout ()` inside `norm_linear` gets its tiny `0.08s` local budget and never exceeds `80 ms`!):
   - Specifically:
     ```ocaml
     if !c_chs && size_of_expr !best >= 3 && size_of_expr !best <= 256
        && dag_size_bounded ~limit:256 !best <= 256
     then (
       let saved_timeout = !g_has_timedout
       and saved_total = !g_total_timeout
       and saved_branch = !g_branch_deadline in
       let polish_deadline = Unix.gettimeofday () +. 0.08 in
       g_has_timedout := false;
       g_total_timeout := 0.;
       g_branch_deadline := Some polish_deadline;
       Fun.protect
         ~finally:(fun () ->
           g_has_timedout := saved_timeout;
           g_total_timeout := saved_total;
           g_branch_deadline := saved_branch)
         (fun () ->
           try
             let before = !best in
             let polished =
               Normalization.dag_bottom_up_simplify ~zero_smt:true
                 ~minimal:false ~deadline:polish_deadline !best
             in
             if size_of_expr polished < size_of_expr before then
               best := polished
           with Timeout_exception -> ()));
     ```
   - **Check safety & proof validity:**
     - `~zero_smt:true` executes **ZERO Bitwuzla SMT calls** — ONLY decidable zero-SMT rewrites (`dag-linear-mba`, `dag-not-pushdown`, `dag-factor-pullout`, `dag-ring-mod2w`, `dag-semilinear-mba`, `dag-gf2-masked-xor`, `dag-product-peel`, `dag-complementary-atoms`, `dag-correlated-null`).
     - Every accepted rewrite is independently recorded in `Rewrite.journal` and strictly decreases `size_of_expr`!
     - Hard-capped at `80 ms` (`0.08s`) on small `<= 256`-node ASTs (typically finishes in `< 3 ms`!).
     - Restores `g_has_timedout`, `g_total_timeout`, and `g_branch_deadline` cleanly in `Fun.protect`!

2. **Also verify `common_factor_pullout_candidate` handles `((x1 * x3) + x4) - ((x0 * x5) + (x1 * x2))` (`tigress_lvl_5__target_1565`):**
   - Check why `((x1 * x3) + x4) - ((x0 * x5) + (x1 * x2))` (size 13) didn't factor `x1 * (x3 - x2)` (size 11) — in `norm_peepholes.ml:780-835`, check whether `common_factor_pullout_candidate` allows opposite signs (`left_sign = true`, `right_sign = false` -> `x1 * (x3 - x2)`)! If it only checks `left_sign = right_sign`, generalize it by 3 lines to handle opposite signs (`(if left_sign then l else -l) + (if right_sign then r else -r)` -> `l - r` / `r - l`), certified **100% ZERO-SMT** via `ring_mod2w`!

---

## Fast-Sprint Verification Gate for Round 69

1. **Regression Tests (`test/round69_test.ml`, plus warning-clean `make test`):**
   - Post-CHS shape of `target_1024`: `(((((x0 + (x1 + x5)) ^ (x2 ror 14)) ^ ((x2 ror 18) ^ (x2 ror 41))) + (((x0 + (x1 + x5)) & ((x2 ror 14) ^ ((x2 ror 18) ^ (x2 ror 41)))) << 1)) + (((x3 ^ x4) & x2) ^ x4))` (`size 45`) -> collapses to **`size <= 37`** with **ZERO SMT** (`linear_mba_mod2w`) and independent `mba_proof` replay!
   - `~((((~x1) & x3) ^ x2) - x0)` (`target_1251`, `size 9`) -> **`size 8`**, zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `((x1 * x3) + x4) - ((x0 * x5) + (x1 * x2))` (`target_1565`, `size 13`) -> **`size 11`**, zero-SMT `ring_mod2w`, independent `mba_proof` replay!
2. **Fast Smoke Gate ONLY (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`):**
   - `datasets/hard_cases/regression_smoke` (`62` cases -> `/tmp/r69-smoke/out.jsonl`): **MUST PASS `62/62` proved & strict, `>= 57/58` exact, `<= 0.805x`, `0` refutations!**
3. Append a brief Round-69 sprint note to `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly!
