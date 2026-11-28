# GreySynth Round-48 Spec: Dual-Boundary Merge + `sext`/`uext` Mask Lifting + Recursive Bitwise AC-Canonicalization Before Ring/Poly + Opaque-Atom `semilinear_mba` & Disjoint-Sum Pure-Bitwise Canonicalization

**Baseline:** Round 47 (`778a355` / `4152c74` — shrunk `Tigress L5` **`+44 / 251` exact `<= GT`, `10.56x -> 6.67x`** (`Tigress L5` now **`79.3%` exact!**), refreshed `core_hard` **`+25 / 341` exact, `7.07x -> 5.47x`**, Leeky `dev_64` **`2.3475x -> 2.1585x`**, `mba-ladders-v1` `39 -> 48/72`, `mba-stress64-v1` `11.26x -> 6.66x`, `mba-frontier64-v1` `22.70x -> 16.05x`, `0` refutations across all 1,539 cases).

**Zero proof-kernel changes required in Round 48** (`src/proof/rewrite_proof.ml` stays untouched!). All four improvements below are 100% general algebraic passes proved compositionally via existing zero-SMT `linear_mba_mod2w`, `semilinear_mba_mod2w`, `ring_mod2w`, and bounded SMT edges.

---

## 1. Monotonic Dual-Boundary Merge in `src/greysynth/norm_linear.ml` (Fixes `regression_smoke` `0.9488x -> <= 0.79x` & Restores `target_3259` + `mba-frontier64-v1` Exact Hits!)

Forensic inspection of `778a355` revealed WHY `tigress_lvl_6__target_3259` regressed (`7 -> 212`) and why `mba-frontier64-v1` lost 3 exact hits (`3 -> 0`):
- In `src/greysynth/norm_linear.ml`:
  ```ocaml
  if proposals = [] && ring_bridges && Nodes.length bitwise_linear_atoms > 0 then
    linear_candidates_with_rings ~opaque_atoms ~max_atoms ~semantic_bitwise
      ~ring_bridges:false cost expression
  else proposals
  ```
- When `bitwise_linear_atoms` was non-empty, stopping at `bitwise_linear_atoms` yielded a *partial* reduction (`39055 -> 212`), so `proposals <> []`, and the standard no-stop pass (which collapses `39055 -> 7`!) was **NEVER EVEN TRIED**!
- **Fix (100% general, strictly monotonic):**
  1. Add an explicit `?(bitwise_stops = true)` parameter to `linear_candidates_with_rings` (decoupling `bitwise_stops` from `ring_bridges`!).
  2. When `bitwise_stops && Nodes.length bitwise_linear_atoms > 0`: **ALWAYS** run BOTH `bitwise_stops:true` AND `bitwise_stops:false` (with the same `~ring_bridges`), merge both proposal lists, deduplicate by candidate, and return them sorted by `cost candidate` ascending!
  3. In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify` line 232): iterate `List.find_opt accept_linear` over the sorted proposals instead of only trying the single head proposal.
  4. Also check why `multivariate64__line_0000002` timed out under 8-worker parallel load in `r47-smoke` (likely `nonlinear_poly_candidate` skipped when `cost > 512` in `zero_smt`, or parallel contention): make sure `regression_smoke` returns to **`62/62` strict decreases, `>= 54/58` exact, `<= 0.795x`**!

---

## 2. General `sext`/`uext` Constant-Mask Lifting in `src/greysynth/norm_semilinear.ml` (Unlocks `Tigress L5–L8` `other_cast_slice`!)

Forensic inspection of `R46/R47 Tigress L5` top `other_cast_slice` residuals (`tigress_lvl_5__target_4853` `in=4080 -> out=410, gt=5` and `tigress_lvl_5__target_2923` `in=4080 -> out=345, gt=5`) showed two missing general bitvector identities in `nonlinear_product_identity_candidate` (`lifted_intersection` lines 688–714 & `build_constants` lines 799–844):

1. **Zero-ext / Sign-ext Low-Mask Unification (`target_4853`):**
   - For ANY `a = sext(amount) low_a` and `b = Cst wide_mask` whose upper `amount` bits are zero (i.e. `Z.equal (Bitvector.value_of low_mask) (Bitvector.value_of wide_mask)` where `low_mask` has width `sizeof low_a`):
     $$\text{uext}(\text{amount})(\text{low\_a} \mathbin{\&} \text{low\_mask}) = (\text{sext}(\text{amount})\,\text{low\_a}) \mathbin{\&} \text{wide\_mask}$$
     Extend `lifted_intersection` so it handles **`E.Sext amount_a`** symmetrically with `E.Uext amount_a`!
2. **Zero-ext High-Bit-Don't-Care Mask Unification (`target_2923`):**
   - For ANY `a = uext(amount) low_a` (whose upper `amount` bits are ALWAYS `0`) and ANY `W`-bit `wide_mask`:
     $$\text{uext}(\text{amount})(\text{low\_a} \mathbin{\&} \text{low\_mask}) = (\text{uext}(\text{amount})\,\text{low\_a}) \mathbin{\&} \text{wide\_mask}$$
     whenever `Bitvector.value_of low_mask = Z.logand (Bitvector.value_of wide_mask) (low_mask_of (sizeof low_a))` (not just when `wide_mask == low_mask` — e.g. `wide_mask = ~0x1db42<64> = 0xfffffffffffe24bd<64>` and `low_mask = 0xfffe24bd<32>`!).
   - Apply this in BOTH `lifted_intersection` AND `build_constants.and_constant` (`try_pair`), recording the lifted equality `(actual, E.binary E.And wide_var wide_mask)` in `lifted_equalities` (already proved cleanly by `Rewrite.accepts_compositional`!).

---

## 3. Recursive Bitwise AC-Canonicalization Before Ring/Polynomial Expansion (`src/greysynth/norm_ring.ml` / `src/greysynth/norm_poly.ml` — Crushes `mba-majority-v1`!)

Forensic inspection of `mba-majority-v1` (`23bc7e4239e647a2_w64`, `in=89 -> out=73, ref=15`, representative of all 20 remaining non-exact `mba-majority-v1` cases!):
```
(M1 + ((M1 + x2) * (x1 + x2))) - (((M2 + (x1 + x2)) * x2) + (M2 * x1))
```
where `M1 = ((x5*x6) | x3) & (((x5*x6) & x3) | x4)` and `M2 = ((x5*x6) | x3) & (x4 | (x3 & (x5*x6)))`!
- `M1` and `M2` are **identical up to commutativity & associativity of `&`, `|`, `^`**, so the polynomial collapses identically to `M` (`M + M*x1 + M*x2 + x1*x2 + x2^2 - M*x2 - x1*x2 - x2^2 - M*x1 == M`)!
- Currently `ring_polynomial_candidate` interns non-ring opaque atoms by raw structural equality (`E.is_equal`), treating `M1` and `M2` as two unrelated ring variables!
- **100% General Fix:**
  - Add a recursive bitwise AC-canonicalizer (`canonical_bitwise_atom`) that recursively flattens and sorts nested `E.And`, `E.Or`, and `E.Xor` operands by `E.compare` (and commutes `E.Plus`/`E.Mul` inside opaque children if needed, OR leaves non-bitwise children canonicalized!).
  - When `ring_polynomial_candidate` (and `reduce_modular_polynomial` / `PolySim`) interns a non-ring opaque atom `a`:
    - Compute `c = canonical_bitwise_atom a`.
    - If `not (E.is_equal a c)`, record `(a, c)` as a **`linear_mba_equalities`** bridge (proved in `< 0.1 ms` with **ZERO SMT** by `linear_mba_mod2w`!) and intern `c`!
  - Pass the `linear_mba_equalities` bridges + `[rewritten_source, candidate]` in `ring_equalities` to `Rewrite.accepts_compositional ~pass:"dag-ring-mod2w"` (ZERO SMT!).

---

## 4. Opaque-Atom `semilinear_mba_candidate` + Pure-Bitwise Disjoint-Sum Tie-Breaking (`mba-extra-floor-v1`, `mba-proof-context-v1`, `mba-frontier64-v1`!)

Forensic inspection of `ad964e0b66737fef_w64` (`mba-extra-floor-v1`, `out=83, ref=11`) and `26d6be2a86f9fc4a_w64` (`mba-proof-context-v1`, `out=66, ref=15`) revealed two tiny, 100%-general algebraic gaps:

1. **Maximal-Repeated-Atom Abstraction in `semilinear_mba_candidate` (`src/greysynth/norm_semilinear.ml`):**
   - Look at `ad964e0b66737fef_w64`:
     `2 * ((B | 2) & A) + (A ^ (B | 2)) - ((B & 2) ^ B)` where `A = (x4*(x2|x3)) ^ (x0-x1)` and `B = (A & x5) ^ x6`.
   - `semilinear_mba_candidate` descended through `^` and `&` in `B` and `A`, producing 4 raw atoms instead of abstracting `(A, B)` as 2 opaque atoms where **`A + 2`** is an immediate 1-variable `simple` candidate proved in `< 1 ms` by **`semilinear_mba_mod2w` (ZERO SMT!)**!
   - **Fix:** Add `?(opaque_atoms = [])` to `semilinear_mba_candidate` (stopping `inspect` at any node in `opaque_atoms` and adding it via `add_opaque`). When `semilinear_mba_candidate cost node` returns `None` and `has_nonuniform_bitwise_constant node`:
     - Collect the top `<= 4` maximal repeated subterms (appearing `>= 2` times in `node`, `cost >= 3`, width = `E.sizeof node`, not a constant — prefer outermost repeated subterms first, or test BOTH outermost repeated AND next-level repeated when one repeated subterm `B` contains another repeated subterm `A` like `B = (A & x5) ^ x6`!), and retry `semilinear_mba_candidate ~opaque_atoms cost node`!
     - Note the `B` contains `A` nuance: in `2*((B|2)&A) + (A^(B|2)) - ((B&2)^B)`, BOTH `A` AND `B` appear as standalone operands outside each other! If `opaque_atoms = [B; A]`, checking `List.exists (E.is_equal node) opaque_atoms` BEFORE descending means `B` stops at `B` and standalone `A` stops at `A` — giving **exact 2 variables `[A, B]`**!
     - Proved compositionally by `semilinear_mba_mod2w` (**ZERO SMT**!).
2. **Equal-Cost Disjoint-Bit Sum -> Pure-Bitwise Canonicalization (`mba-proof-context-v1`, `src/greysynth/normalization.ml`):**
   - Look at `26d6be2a86f9fc4a_w64`:
     `(((M_plus + C) & K) | ((C + M_xor) & (~K))) - C` where `M_plus = ((x0 ^ x1) & x2) + (x0 & x1)` (cost 7) and `M_xor = ((x0 ^ x1) & x2) ^ (x0 & x1)` (cost 7)!
   - Because `M_plus` and `M_xor` have **equal cost 7**, `M_plus` was never rewritten to pure-bitwise `M_xor`, preventing `M_plus + C` and `C + M_xor` from unifying!
   - **Fix (100% general algebraic hierarchy: pure bitwise strictly simpler than arithmetic `+`!):**
     - In `dag_bottom_up_simplify`, when `!result` is `E.Binary { f = E.Plus; x; y; _ }` with `cost !result <= 24` and both `x` and `y` are pure-bitwise trees (only `Var`, `Cst`, `Not`, `And`, `Or`, `Xor`):
     - Test candidate `E.binary E.Xor x y` (same cost, strictly purer algebraic class — eliminates arithmetic carry!). If `Rewrite.samples_agree !result candidate` AND `Rewrite.accepts_compositional ~allow_equal_cost:true ~pass:"dag-disjoint-sum-xor" ~equalities:[] ~linear_mba_equalities:[ !result, candidate ] !result candidate` (ZERO SMT via `linear_mba_mod2w`!), accept `result := candidate`!
     - (Ensure `Rewrite.accepts_compositional` supports `?(allow_equal_cost = false)` just like `Rewrite.accepts`, ONLY passed here where top operator strictly descends `Plus -> Xor` so termination is 100% guaranteed!)

---

## 5. Verification Gate for Round 48 (Target Wall Time: ~10–12 min!)

1. **Unit & Regression Tests (`test/round48_test.ml`):**
   - `tigress_lvl_6__target_3259`-style boundary-vs-standard linear test (verifies dual-boundary merge recovers size `7`!).
   - `tigress_lvl_5__target_4853` (`sext` low-mask) AND `tigress_lvl_5__target_2923` (`uext` high-bit-don't-care mask) tests: verify compositional proof + independent `mba_proof` replay!
   - `23bc7e4239e647a2_w64`-style `mba-majority-v1` test (commuted `M1`/`M2` inside polynomial cancellation): verify zero-SMT collapse to `M` + independent `mba_proof` replay!
   - `ad964e0b66737fef_w64`-style `mba-extra-floor-v1` test (`2*((B|2)&A) + (A^(B|2)) - ((B&2)^B) -> A + 2`): verify zero-SMT collapse via `semilinear_mba_mod2w` + independent `mba_proof` replay!
   - `26d6be2a86f9fc4a_w64`-style `mba-proof-context-v1` test (`(((M_plus + C) & K) | ((C + M_xor) & ~K)) - C -> M_xor`): verify zero-SMT collapse + independent `mba_proof` replay!
   - Run `make test` — warning-clean, 100% green, **zero edits to `src/proof/rewrite_proof.ml`!**
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain JSONLs under `/tmp/r48-*/out.jsonl`):**
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases -> `/tmp/r48-smoke/out.jsonl` — **RUN THIS FIRST** so we immediately verify `62/62` strict decreases, `>= 54/58` exact, `<= 0.795x`, `0` refutations!)
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases — **keeping held-out `mba-balanced-v1` strictly untouched!** -> `/tmp/r48-leeky-dev64/out.jsonl` — target: BIG jumps on `mba-majority-v1` `34 -> ~54`, `mba-proof-context-v1` `12 -> ~36`, `mba-extra-floor-v1` `23 -> ~45+`, and recovery of `mba-frontier64-v1`!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r48-l5/out.jsonl` — target: `55+` exact `<= GT`, geomean `< 5.5x`!)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r48-core/out.jsonl`)
3. Record concise Round-48 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
