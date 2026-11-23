# GreySynth Round-12 Review: Proof-Path Fixes Verified & 4 Smoking-Gun Fixes to Pass the Milestone 4A Corpus Gate

**Reviewed commits:** `091487b..2ccac35` (`091487b`, `8bb548d`, `9002e17`, `2ccac35`)  
**Summary:**
- **All 6 Round-11 correctness bugs are verified fixed!** Re-running our exact live reproducers at `2ccac35` (`egraph_extraction=true`, `ac_normalization=true`, `oes=false`, `chs=false`) gives **4/4 `proved_compositional`** with tiny certificates and zero `incomplete_derivation`:
  - `child_mba_inside_mul`: `31 -> 5` in `0.184s` (`proved_compositional`, 5 edges — was `3.117s`, `incomplete_derivation`)
  - `child_ac_expose_parent`: `7 -> 1` in `0.022s` (`proved_compositional`, 2 edges — was `incomplete_derivation`)
  - `child_prop_cancel`: `7 -> 1` in `0.026s` (`proved_compositional`, 1 edge — was 7 edges)
  - `nonpoly_L2_full`: `121 -> 3` in `0.254s` (`proved_compositional`, 18 edges)
- **Root-cause of the 16 C-Full process timeouts and `QSynth EA` (`1.49x`) / `PLDI Non-Poly` (`1.26x`) regressions:** Code inspection of `src/greysynth/egraph.ml:180-491` immediately exposed **4 exact scheduling/verification bugs** that explain *both* the 16 timeouts and every quality regression. Fixing these 4 surgical issues should cleanly clear the Milestone 4A corpus gate (`1,000/1,000` C-Full, `>= 984/16`, all 5×100 datasets `<=` baseline).

---

## Four Smoking-Gun Bugs in `src/greysynth/egraph.ml` (`2ccac35`)

### Smoking Gun 1 (Critical — Causes All 16 C-Full Process Timeouts): Unchecked `local_deadline` inside candidate & `semantic_merge` loops + Full-Journal SMT Re-Verification (`egraph.ml:195-208, 238-272, 433-449, 465-476`)
Three things combine to blow right past both the 2-second `local_deadline` and the 45-second C-Full process timeout:
1. **`verify_local` (`egraph.ml:195-204`) ignores `local_deadline`:** it clamps Bitwuzla's timeout only to `!g_total_timeout` (15s), NOT to `local_deadline -. now`. And there is **no** deadline check inside the inner candidate loop (`lines 433-449`) or inside `semantic_merge` (`lines 238-272`). A single e-class with 10 candidates × 2s Bitwuzla burns **20 seconds** before line 420 ever checks `local_deadline`!
2. **Full-journal SMT re-verification at `egraph.ml:465-476`:** After every single edge was *already* proved by `verify_local`, lines 469–475 call `Rewrite_proof.verify` on the **entire** `Rewrite.journal`, re-running Bitwuzla from scratch on every emitted edge! On large C-Full cases this doubles total SMT time and triggers process timeouts.
3. **`verify_local` still does not consult or populate `Rewrite.proofs` / `Rewrite.proof_budgets`**, repeating identical queries across saturation rounds and after fallback.

**Fixes:**
- Pass `local_deadline` into `verify_local`, `semantic_merge`, and the inner candidate loop:
  - Check `if Unix.gettimeofday () > local_deadline then raise Egraph_budget` at the start of every candidate iteration (`line 433`) and every `semantic_merge` pair (`line 244`).
  - Clamp `verify_local`'s SMT timeout to `min (min 0.5 (float_of_int !c_equiv_timeout)) (local_deadline -. Unix.gettimeofday ())` (note: `ring_mod2w` and pure-bitwise minterm edges take `< 2 ms`, so `0.5s` per local e-graph probe is generous while making budget overruns impossible!).
  - Consult & populate `Rewrite.proofs` / `Rewrite.proof_budgets` inside `verify_local` (skipping Bitwuzla completely on cache hits!).
- **Remove the redundant full-journal Bitwuzla re-run at `egraph.ml:465-476`!** Replace it with a **0.05 ms pure structural connectivity check** (calling `Rewrite_proof.congruent` — zero SMT calls! — or exporting a tiny `Rewrite_proof.check_connected` helper that checks graph congruence over already-verified edges in `builder.edges` without re-invoking Bitwuzla!).

### Smoking Gun 2 (Critical — Causes `PLDI Non-Poly` `1.26x` & `QSynth EA` `1.49x` Regressions): Top-Down (Largest-First) Class Ordering (`egraph.ml:410-418`)
```ocaml
Int.compare right_cost left_cost
```
Line 418 sorts e-classes **largest-first (top-down)**!
- On `PLDI Non-Poly` (where a 29-node inner MBA `E == a` is embedded 12 times inside a 500-node parent) and `QSynth EA`, largest-first spends the entire 2-second `local_deadline` running `local_candidates` + Bitwuzla on the **unsimplified 500-node, 400-node, 300-node parents**, hitting `Egraph_budget` before ever reaching the small inner child `E == a`!
- **Fix:** Sort e-classes **bottom-up (smallest-first: `Int.compare left_cost right_cost`, skipping leaves of cost `<= 1`)**! (Keep one optional fast root-only check for `bitsliced_candidate` when `cost root <= 512`, which is already O(66 evals) with 0 SMT until samples agree.) Small 5–40 node subtrees collapse in milliseconds, shrinking 500-node parents to 15 nodes *before* parents are even touched!

### Smoking Gun 3 (High): `Egraph_budget` and `Full` Discard All Already-Proved Work (`egraph.ml:485-491`)
When `Egraph_budget` or `Full` is raised during saturation (e.g., after 1.9 seconds of productive merges in iteration 2), lines 485–491 jump past `extract` and **roll back everything**, returning the raw unsimplified `expression`!
- **Fix:** Catch `Egraph_budget | Full` **around the saturation `while` loop** (same `try ... with` as `Timeout_exception` at line 458!), so whenever the 2s budget or enode limit is reached, `optimize` **still extracts the best proved expression found so far** and emits its minimal proof path! (And allow `add_expr_unbounded` when interning `result` at line 462 so final extraction can never fail with `Full`!) Only set `last_fallback := true` if `size_of_expr result >= size_of_expr expression` (no improvement achieved).

### Smoking Gun 4 (High): Candidate Loop Verifies All Candidates After Finding a Cheaper Winner (`egraph.ml:431-449`)
In `lines 433-449`, `List.iter` verifies **every** candidate returned by `Normalization.local_candidates` even after the first candidate already reduced `representative` from cost 40 to cost 1!
- **Fix:** Sort `local_candidates` cheapest-first (`cost` ascending, `allow_equal_cost = false` before `true`). Once a **strictly cheaper** candidate is verified and unioned for `representative`, stop verifying remaining strictly-cheaper candidates for that `representative` (still allowing at most **one** equal-cost AC candidate per class so non-monotonic child AC remains preserved!).

---

## Acceptance Targets for Round 12

1. Apply all **4 surgical fixes** above in `src/greysynth/egraph.ml` (plus a tiny zero-SMT `Rewrite_proof.is_connected` helper in `src/proof/rewrite_proof.ml` if needed for the fail-safe check).
2. Keep all existing 64+ solver-backed tests passing (`make test` green), plus add a focused regression verifying that hitting `Egraph_budget` or `Full` mid-saturation still extracts and replays partial proved progress.
3. Re-audit ALL **five 100-case MBA datasets** with `egraph_extraction: true`, `ac_normalization: true` — target: **500/500 proved**, **0 timeouts/errors**, and geometric quality matching or beating baseline across all 5 (`PLDI Poly <= 0.8812x`, `PLDI Non-Poly <= 0.9394x`, `MBA-Obfuscator nonlinear <= 0.8693x`, `QSynth EA <= 0.9673x`, `msimba <= 0.9966x`).
4. Re-audit **1,000-case C-Full** with `egraph_extraction: true`, `ac_normalization: true` — target: **1,000/1,000 proved**, **0 process timeouts** (down from 16!), `>= 984/16` strict reductions, and compare smaller/equal/larger against the paired baseline.
5. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` (if all gates pass, mark Milestone 4A `[x]`!) and commit atomically (do not modify `docs/neon-review*.md`).
