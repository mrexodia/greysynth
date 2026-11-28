# GreySynth Round-70 Spec (Fast Sprint Commit 4/4): Mixed-Width `uext`/`sext` Constant-Cast Folding & Identity-`restrict` Elimination (`norm_peepholes.ml`, `norm_semilinear.ml`, `normalization.ml`)

**Sprint Mode (Fast 4-Commit Cycle, Commit 4/4):** Gate ONLY with targeted regression tests (`test/round70_test.ml`) + warning-clean `make test` + **35-second `regression_smoke` gate (`/tmp/r70-smoke/out.jsonl`)**! Right after Commit 4 lands, we will launch our full comprehensive measurement sweep (`dev_64` + **Full Corpus Prune Sweep #5** + **Milestone-70 Strictly Held-Out Check**)!

**Scope:** **ZERO `src/proof/rewrite_proof.ml` edits!** ONLY `src/greysynth/norm_peepholes.ml`, `src/greysynth/norm_semilinear.ml`, and `src/greysynth/normalization.ml`.

---

## Forensic Root Cause on Remaining `Tigress L5–L8` `wide_96` & Cast Cases

Inspecting the smallest remaining `wide_96` / cast cases in `r66-l5` revealed **THREE** glaring gaps:
1. **Unfolded `sext(32) Cst` & `uext(32) Cst` inside shifts and sums (`target_2135`, `target_4663`, `target_6166`):**
   - `tigress_lvl_5__target_2135` (`out=13, gt=5`): `((sext(32) 0x2<64>) << (uext(32) x0<64>))`
   - `tigress_lvl_5__target_4663` (`out=14, gt=5`): `((uext(32) x0<64>) << (sext(32) 0x15<64>))` AND `uext(32) (~x1<64>)`
   - `tigress_lvl_5__target_6166` (`out=15, gt=5`): `((uext(32) x0<64>) << (uext(32) 0x1<64>))`
   - WHY were `sext(32) 0x15<64>` and `uext(32) 0x1<64>` NEVER folded to `0x15<96>` / `0x1<96>`?!
     - Because `dag_constant_cast_simplify` only runs ONCE on inputs `> 1024`, AND inside `dag_bottom_up_simplify` (`normalization.ml:175`), `dag-constant-cast` was gated behind `try_smt` (so it NEVER ran in `zero_smt = true` mode, nor during `run_small_dag` or post-CHS polish!) — AND `dag_constant_cast_simplify` only folded casts directly on `Lsl` shift amounts, not general `sext(k) Cst` / `uext(k) Cst` / `restrict(0, width-1) x`!
   - Once `sext(32) 0x15<64>` folds to `0x15<96>`, `((uext(32) x0<64>) << 0x15<96>)` immediately becomes a **constant shift (`* 2^21`)** that `linear_mba_mod2w` and `ring_mod2w` simplify natively in `< 1 ms` with ZERO SMT!
2. **Uneliminated Identity `restrict(0, width-1) x` (`target_2536`, `target_4333`):**
   - `tigress_lvl_5__target_2536` (`out=9, gt=7`): `(uext(32) (-1 + ((restrict(0,63) x0<64>) << 8) + (restrict(0,63) ...)))`
   - `restrict(0, 63) x<64>` is syntactically identical to `x<64>`! Folding `restrict(0, hi) x` -> `x` whenever `hi + 1 = E.sizeof x` in `constant_cast_fold_candidate` eliminates redundant `restrict` wrappers that block `linear_mba` / `ring_mod2w` matching!
3. **Unlifted `uext(amount)(~low)` when `low` is a variable or simple expression (`target_4663`, `target_1776`, `target_1933`):**
   - Currently `complementary_slice_candidate` (`norm_semilinear.ml:712-724`) ONLY rewrites `uext(amount)(~low) -> (2^low_w - 1) - uext(amount)(low)` when `uext(amount)(low)` ALSO appears in the expression — missing cases like `target_4663` where `uext(32)(~x1)` appears alongside `uext(32)(x1)` INSIDE a bitwise `&` or where `~x1` is inside `uext(32)(~x1)` and `x1` is already zero-extended elsewhere!
   - Even simpler: check `complementary_slice_candidate` (`norm_semilinear.ml:672-725`) — make sure `collect` records `uext(amount) low` even under `And`/`Or`/`Xor`/`Mul`/`Lsl`, AND run `dag_constant_cast_simplify` (folding `uext(k)(Cst)`, `sext(k)(Cst)`, `restrict(lo, hi)(Cst)`, and identity `restrict(0, width-1) x`!) right after `dag_bottom_up_simplify` (in `greysynth.ml` before `run_root_linear_group` / `run_root_complementary_slice` when `!best` contains casts and `size <= 2048`!)!

---

## Exact Edits

0. **1-Line Giant-Root Guard on `run_root_gf2_masked_xor` (`src/greysynth/greysynth.ml:528`):**
   - Guard the entire `run_root_gf2_masked_xor` helper with `if size_of_expr original <= 65_536 && dag_size_bounded ~limit:8192 original <= 8192 then ...`!
   - Why: On giant `> 65,536`-node Tigress-L8 roots (`tigress_lvl_8__target_1016`), checking children of `original` and calling `accepts_compositional original full` burned >1s of budget (`9 -> 9,309` on `r68/r69-smoke`). Guarding `original <= 65_536` restores `target_1016 -> 9` (`57/58` exact & `0.800x` on `regression_smoke`) while preserving 100% of wrapped child-root `gf2_masked_xor` wins on `6k..13k`-node `mba-capabilities-v1` trees!

1. **In `src/greysynth/norm_peepholes.ml` (`constant_cast_fold_candidate`):**
   - Ensure `constant_cast_fold_candidate` handles ALL four clean cast folds:
     - `E.Unary { f = E.Uext amount; x = E.Cst value; _ }` -> `E.constant (Bitvector.extend value (E.sizeof expression))` (exact zero-extension of constant!)
     - `E.Unary { f = E.Sext amount; x = E.Cst value; _ }` -> `E.constant (Bitvector.extend_signed value (E.sizeof expression))` (exact sign-extension of constant!)
     - `E.Unary { f = E.Restrict { lo; hi }; x = E.Cst value; _ }` -> `E.constant (Bitvector.extract value { lo; hi })`
     - `E.Unary { f = E.Restrict { lo = 0; hi }; x; _ }` when `hi + 1 = E.sizeof x` -> `x` (exact identity restrict!)
   - Check that `dag_constant_cast_simplify` (`normalization.ml`) applies `constant_cast_fold_candidate` everywhere in a DAG (not just on `Lsl` shift amounts!) with a small local SMT budget (`~timeout:0.10`, capped at `<= 32` distinct folded cast nodes per pass so it takes `< 20 ms` total!).

2. **In `src/greysynth/greysynth.ml` (`run_preprocessing`):**
   - Run `Normalization.dag_constant_cast_simplify !best` ALSO on smaller cast-containing roots (`size_of_expr !best <= 1024 && not !g_has_timedout`) — specifically once right before `run_small_dag ()` AND once right before `run_root_complementary_slice ()` (only if `!best` actually contains a `Uext`/`Sext`/`Restrict` node, checked in O(DAG) memoized!), so newly exposed `sext(32) Cst` / `uext(32) Cst` / `restrict(0, w-1) x` are IMMEDIATELY folded before `linear_mba` & `ring_mod2w` run!

3. **In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`):**
   - Also check why `tigress_lvl_5__target_4785` (`(0x200 * x1) + ((sext(7)(restrict(7,31) x0)) & (~(0x200 * x1)))`) didn't collapse `A + (B & (~A)) -> A | B`!
     - Because `A = 0x200 * x1` is a scaled linear term inside `& ~A`, AND `B = sext(7)(restrict(7,31) x0)` is opaque — `linear_candidates_with_rings` (`bitwise_stops = true`) ALREADY collapses `A + (B & (~A)) -> A | B`! Why didn't it fire on `target_4785`? Because `target_4785` had `uext(16)(restrict(0, 15) (...))` around it and `0x200 * x1` was only exposed *after* `dag-constant-cast` / `CHS`! With Commit 3/4's post-CHS `dag_bottom_up_simplify` + Commit 4/4's cast folding, `target_4785` (`10 -> 7`!) collapses automatically!

---

## Fast-Sprint Verification Gate for Round 70

1. **Regression Tests (`test/round70_test.ml`, plus warning-clean `make test`):**
   - `((uext(32) x0<64>) << (sext(32) 0x15<64>))` -> folds `sext(32) 0x15<64>` to `0x15<96>`, independent `mba_proof` replay!
   - `restrict(0, 63) x0<64>` -> folds to `x0<64>`, independent `mba_proof` replay!
   - `tigress_lvl_5__target_2135` (`in = 502, gt = 5`), `tigress_lvl_5__target_4663` (`in = 715, gt = 5`), `tigress_lvl_5__target_6166` (`in = 740, gt = 5`) -> verify strict improvement below previous `13 / 14 / 15` with independent `mba_proof` replay!
2. **Fast Smoke Gate ONLY (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`):**
   - `datasets/hard_cases/regression_smoke` (`62` cases -> `/tmp/r70-smoke/out.jsonl`): **MUST PASS `62/62` proved & strict, `>= 57/58` exact, `<= 0.805x`, `0` refutations!**
3. Append a brief Round-70 sprint note to `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly!
