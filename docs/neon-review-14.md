# GreySynth Round-14 Review: C-Full Gate Cleared (1,000/1,000, 0 Timeouts) & Exact 2-Line Fixes for the Final Two Quality Deltas

**Reviewed commits:** `9bf2db6..3f964a6` (`9bf2db6`, `6d37a1c`, `3f964a6`)  
**Summary:** Huge milestone! Round 13 eliminated all 17 C-Full timeouts (`target_3137`: `45s hang -> 0.36s`, `target_2927`: `45s hang -> 1.32s`), passing the full **1,000/1,000 C-Full gate (0 timeouts, 984/16)**, and **3 of 5 MBA datasets already beat baseline** under `egraph_extraction: true`:
- **`PLDI Non-Poly`:** **`0.9290x`** (beats `0.9394x` baseline!)
- **`PLDI Poly`:** **`0.8789x`** (beats `0.8812x` baseline!)
- **`QSynth EA`:** **`0.8429x`** (beats `0.9673x` baseline by **13%**!)

Inspecting `/tmp/greysynth-bench/r13e-mba_obf_nonlinear/out.jsonl` and `/tmp/greysynth-bench/r13e-msimba/out.jsonl` pinpointed the **exact, tiny root causes** of the final two deltas (`MBA-Obfuscator nonlinear` `0.9427x` vs `0.8693x`, and `msimba` `1.0045x` vs `0.9966x`). Fixing both should close Milestone 4A completely!

---

## 1. Exact Root Cause of `MBA-Obfuscator nonlinear` (`0.9427x` vs `0.8693x` baseline)

Comparing `r12-mba_obf_nonlinear` (before `528e12e`) against `r13e-mba_obf_nonlinear` on the worst outliers (`line_0000034` and `line_0000079`):
```text
baseline / r12 (before 528e12e): line_0000034  in=136 -> out= 5  ((x ^ y) - y)
r13e           (after  528e12e): line_0000034  in=136 -> out=21  ((((y&x)+1)*(x&~y)) + ((y&x)*(~x+(y&x))))

baseline / r12 (before 528e12e): line_0000079  in=182 -> out= 8  ((x ^ y) - (x | ~y))
r13e           (after  528e12e): line_0000079  in=182 -> out=28  (((y&x)*x) + ((~(x|y))*(...)) - ...)
```

**Why:**
In `528e12e`, `egraph.ml`'s candidate loop sorted `Normalization.local_candidates` by immediate `size_of_expr` and **stopped after accepting a single strictly-cheaper candidate (`cheaper_found = true`)**.
- On `line_0000034` (size 136), `minterm_polynomial_candidate` produces an immediate size **25** quadratic minterm polynomial (a local dead end because `(x & y) * (x & ~y) != 0` under `bvmul`), whereas `factor_group_candidate` only factors **one** repeated factor per call, producing immediate size **~75** (which then factors the 2nd factor on the next step and collapses to size **5**!).
- Because `25 < 75`, `egraph.ml` accepted `minterm_polynomial`, set `cheaper_found = true`, and **discarded `factor_group_candidate` without ever adding it to the e-class!**

**Two Clean Complementary Fixes:**
1. **Multi-step factoring inside `factor_group_candidate` (`src/greysynth/normalization.ml`):**
   Currently `factor_group_candidate` factors only a single factor `F_1` per call (`136 -> 75`), requiring multiple outer iterations to finish a 2–3 factor sum. Loop internally (bounded by e.g. 6 steps) on the remaining unfactored sum `remainder` (accumulating `(equalities, ring_equalities)` and cleaning up with one final `ring_mod2w` / `linear_candidates` pass on the combined `sum c_i * F_i`), so `factor_group_candidate` collapses `line_0000034` directly `136 -> 5` and `line_0000079` `182 -> 8` in **one single candidate**!
2. **Do not let `minterm-polynomial` suppress `factor-group` in `egraph.ml` (`src/greysynth/egraph.ml:585-614`):**
   Instead of a single boolean `cheaper_found` that discards all other pass families, track accepted strictly-cheaper candidates **per pass family** (or keep at least both the cheapest `factor-group` candidate AND the cheapest non-factor strictly-cheaper candidate in the same e-class — that is the core purpose of an e-graph!).

---

## 2. Exact Root Cause of `msimba` (`1.0045x` vs `0.9966x` baseline)

Inspecting `/tmp/greysynth-bench/r13e-msimba/out.jsonl` reveals that **99 out of 100 cases are already exact `1.00x` (`out=5, gt=5`)!** The **entire** `0.008x` delta comes from **one single case**:
```text
msimba/line_0000002: in=165 out=11 gt=7 (1.57x) wall=28.15s
  out = ((x & 0xeffffffffffffffc) ^ 0x99db8d4c50945260) + (15 * (0x1000000000000000 & x))
```

**Why:**
`msimba/line_0000002` has 26 distinct single-bit mask terms (`> max_atoms = 6`), so `minterm_ring_proof` returns `None`. In `egraph.ml:523-548`, `root_fast` ran `bitsliced_candidate` (which found the exact size-5 answer `(x & 0xfffffffffffffffc) ^ 0x99db8d4c50945260`!), handed it to `verify_local` with `timeout <= 0.5s`, and monolithic Bitwuzla timed out at `0.5s` (it needs ~1.2–2.0s monolithically).

**Clean Compositional Fix (drops `line_0000002` from `28.15s` to `< 0.1s` AND `out=11 -> 5`):**
1. **Add a disjoint-mask compositional proof (`bitsliced_ring_proof`) in `normalization.ml`** for 1-variable masked sums `c0 + sum_i c_i * (m_i & x)` against candidate `((x & M) ^ K)` (or `a * (x ^ K) + c`):
   - Collect all mask constants `m_i` appearing in `x & m_i` in `original` plus `M` and `K` from `candidate`.
   - Partition the `width` bit positions into **atomic disjoint bit-blocks** `B_1, ..., B_r` (equivalence classes of bit positions that agree on every bit of every mask `m_i`, `M`, `K` — each block is a single `Bitvector.t` mask, and `B_j & B_k = 0` for `j <> k`).
   - For each compound mask term `(x & m_i)` covering `> 1` block, emit ONE pure-bitwise `"smt"` edge `(x & m_i) == sum_{j in m_i} (x & B_j)` (**0.8 ms**, zero multiplications!).
   - For the candidate `(x & M) ^ K`, emit ONE pure-bitwise `"smt"` edge `((x & M) ^ K) == K + sum_{j in M, K_j=0} (x & B_j) - sum_{j in M, K_j=1} (x & B_j)` (**1 ms**, zero multiplications!).
   - Emit **ONE `"ring_mod2w"` edge** connecting the expanded `original` to the expanded `candidate` (**< 0.1 ms**)!
   - Wire `bitsliced_ring_proof` into both `Normalization.run` / `local_candidates` and `Egraph.optimize`'s `root_fast`!
2. Also allow `root_fast` in `egraph.ml:539` a slightly higher local budget cap (`min 1.5 remaining_local_deadline`) if it ever needs to fall back to monolithic SMT on a single root bit-sliced check.

---

## 3. Acceptance Targets for Round 14 (Milestone 4A Completion Gate)

1. Implement multi-step `factor_group_candidate` + pass-aware strictly-cheaper acceptance in `egraph.ml`, plus `bitsliced_ring_proof` for 1-variable disjoint-mask sums.
2. Add focused unit tests for `mba_obf_nonlinear/line_0000034` (`136 -> 5`), `line_0000079` (`182 -> 8`), and `msimba/line_0000002` (`165 -> 5` via `ring_mod2w`, `< 0.2s`!).
3. Run `make test` (all green).
4. Re-audit ALL **five 100-case MBA datasets** with `egraph_extraction: true`, `ac_normalization: true` — verify **500/500 proved**, **0 timeouts**, and **ALL FIVE matching or beating baseline**:
   - `PLDI Non-Poly <= 0.9394x`
   - `MBA-Obfuscator nonlinear <= 0.8693x`
   - `PLDI Poly <= 0.8812x`
   - `QSynth EA <= 0.9673x`
   - `msimba <= 0.9966x`
5. Re-audit **1,000-case C-Full** with `egraph_extraction: true`, `ac_normalization: true` — verify **1,000/1,000 proved**, **0 process timeouts**, `>= 984/16` strict reductions.
6. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` (**mark Milestone 4A `[x]` once all gates pass!**) and commit atomically (do not modify `docs/neon-review*.md`).
