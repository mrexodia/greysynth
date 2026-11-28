# GreySynth Round-67 Spec (Fast Sprint Commit 1/4): Additive Mask-Bucket Linear-MBA Partitioning (`mask_bucket_linear_sum_candidate`)

**Sprint Mode (User-Approved Fast 4-Commit Cycle):** To iterate 3–4x faster across our 4 big general ideas (R67–R70), each sprint commit runs ONLY:
1. Targeted unit/regression tests (`test/round67_test.ml`) + warning-clean `make test`, AND
2. The **35-second `regression_smoke` gate (`62` cases -> `/tmp/r67-smoke/out.jsonl`)** — MUST pass `62/62` proved & strict, `>= 56/58` exact, `0` refutations!
*(Do NOT run `dev_64`, `L5`, `core_hard`, or `heldout_balanced64` in R67–R69; we will run one comprehensive measurement sweep + Full Prune Sweep #5 + Milestone-70 Held-Out Check right after Commit 4 / R70!)*

**Scope:** **ZERO `src/proof/rewrite_proof.ml` edits!** ONLY `src/greysynth/norm_nonlinear.ml`, `src/greysynth/normalization.ml`, and `src/greysynth/greysynth.ml`.

---

## Mathematical Principle (100% General, 100% Zero-SMT)

Suppose a large additive expression `E = t_1 + t_2 + ... + t_n` (`Plus`/`Minus`/`Unary Minus`) combines multiple masked linear-MBA sub-identities that use **distinct non-uniform bitwise constants** `M_1, M_2, ..., M_m` (for example, `9` distinct 64-bit masks `M_1 .. M_9`, each appearing in `6..8` terms of a 3-atom masked linear MBA over `(M_k & x, A_1, A_2)`).
- Together, `E` has `9 + 3 = 12+` opaque atoms — far above `max_atoms = 6`!
- Yet if we partition the additive terms `t_1 .. t_n` into buckets by their **unique non-uniform bitwise constant** `M_k` (terms mentioning exact 1 non-uniform constant `M_k` go into bucket `B(M_k)`; terms with 0 or >= 2 go into `rest`):
  1. By ring associativity/commutativity (`1` single `ring_mod2w` edge, ZERO SMT!):
     `E == (sum B(M_1)) + (sum B(M_2)) + ... + (sum B(M_m)) + (sum rest)`.
  2. Each bucket `sum B(M_k)` (`|B(M_k)| >= 2`) contains **ONLY ONE** non-uniform constant `M_k` (`<= 4..5` atoms total!).
  3. Even if `M_k`'s full zero-identity `F_{M_k} + F_0 == 0` had unmasked residual terms `F_0` in `rest`, **`sum B(M_k) = F_{M_k}` is STILL identically equal to `-F_0`** (completely independent of `M_k`!) — so `linear_candidates_with_rings ~max_atoms:6 cost (sum B(M_k))` collapses `sum B(M_k)` to `-F_0` (or `0`) in **`< 1 ms` with ZERO SMT (`ring_mod2w` + `linear_mba_mod2w`)**!
  4. Then combining the tiny unmasked residuals with `rest` collapses the entire expression in the next linear/ring step!

---

## Exact Implementation

1. **In `src/greysynth/norm_nonlinear.ml` (right after `partial_linear_sum_candidate`, around line 719):**
   Add `mask_bucket_linear_sum_candidate cost expression`:
   - Entry guard:
     - Root must be `E.Binary { f = (E.Plus | E.Minus); _ }`.
     - `cost expression >= 24 && cost expression <= 32_768 && Greysynth_utils.Utils.dag_size_bounded ~limit:2048 expression <= 2048`.
   - Flatten additive terms `(Plus / Minus / Unary Minus)` into `terms` (stop and return `None` if `List.length terms < 4 || List.length terms > 128` — do NOT distribute `Mul` here so we stay purely O(N) on additive spines!).
   - Helper `term_nonuniform_masks term`:
     - Walk `term` with a small memo (`Nodes.create 32`), tracking `under_bitwise : bool` (`true` inside `And`/`Or`/`Xor`; unchanged through `Not`; `false` across `Plus`/`Minus`/`Mul`? — actually track `under_bitwise = true` inside `And`/`Or`/`Xor` and `false` outside, stopping early if `> 2` distinct non-uniform constants are found!).
     - A constant `E.Cst value` under `under_bitwise = true` is a **non-uniform bitwise constant** iff `not (Bitvector.is_zeros value || Bitvector.is_fill value)`!
     - Collect distinct `Z.t` values (cap at 2; if `= 1` value `m`, the term belongs to bucket `Some m`; otherwise `None` -> `rest`).
   - Partition `terms` into `(mask_buckets : (Z.t * E.t list) list)` (preserving insertion order, only keeping buckets with `List.length bucket >= 2` — singletons move to `rest`!) and `rest : E.t list`.
   - If `mask_buckets = []` return `None`.
   - Helper `sum_terms = function [] -> zeros width | head :: tail -> build_balanced E.Plus (head :: tail)`.
   - For each `(m, bucket)` in `mask_buckets`:
     - Let `b_sum = sum_terms bucket`.
     - Run `linear_candidates_with_rings ~max_atoms:6 cost b_sum` (trying the cheapest candidate that passes `Rewrite.samples_agree b_sum cand` and satisfies `cost cand < cost b_sum`).
     - If found `(cand, b_rings, b_rewritten)`: record `improved := true`, accumulate `b_rings` into `ring_equalities`, `(b_rewritten, cand)` into `linear_mba_equalities`, and replace `b_sum` with `cand`!
     - Else keep `b_sum` unchanged.
   - If `not !improved` return `None`.
   - Build:
     - `partitioned = sum_terms (List.map fst pairs @ (if rest = [] then [] else [ sum_terms rest ]))` (where `pairs` are `(orig_bucket_sum, simplified_bucket)`),
     - `candidate = sum_terms (List.map snd pairs @ (if rest = [] then [] else [ sum_terms rest ]))` (filtering out zero constants if other terms exist; if we filter zeros, add a final `(unfiltered_candidate, candidate)` ring edge!).
   - Ensure `cost candidate < cost expression`.
   - Return `Some (candidate, (expression, partitioned) :: !ring_equalities, !linear_mba_equalities)`!
     - *(Note: Every bucket edge connects `orig_bucket_sum -> b_rewritten` via `b_rings` and `b_rewritten -> cand` via `linear_mba_mod2w`; `expression -> partitioned` via `ring_mod2w`; congruence in `Rewrite_proof` connects `partitioned -> unfiltered_candidate` automatically! **100% ZERO SMT!**)*

2. **Wire `mask_bucket_linear_sum_candidate` into TWO places:**
   - **In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`, right after `dag-linear-mba` — runs in BOTH `zero_smt = true` AND `zero_smt = false` modes!):**
     ```ocaml
     if not (should_stop ()) && cost !result >= 24 && cost !result <= 32_768 then
       (match mask_bucket_linear_sum_candidate cost !result with
       | Some (candidate, ring_equalities, linear_mba_equalities)
         when Rewrite.accepts_compositional ~pass:"dag-mask-bucket-linear"
                ~equalities:[] ~ring_equalities ~linear_mba_equalities
                !result candidate -> result := candidate
       | _ -> ());
     ```
   - **In `src/greysynth/greysynth.ml` (`run_root_partial_linear_sum`, right before or after `partial_linear_sum_candidate`):**
     ```ocaml
     (match Normalization.mask_bucket_linear_sum_candidate size_of_expr !best with
     | Some (candidate, ring_equalities, linear_mba_equalities)
       when Rewrite.accepts_compositional ~pass:"root-mask-bucket-linear"
              ~equalities:[] ~ring_equalities ~linear_mba_equalities
              !best candidate -> best := candidate
     | _ -> ());
     ```

---

## Fast-Sprint Verification Gate for Round 67

1. **Regression Tests (`test/round67_test.ml`, plus warning-clean `make test`):**
   - Synthetic 2-mask-bucket linear MBA (`M1` zero-identity + `M2` zero-identity + residual `x0 + x1` = 10+ total atoms) -> collapses cleanly via `mask_bucket_linear_sum_candidate` with **ZERO SMT** and independent `mba_proof` replay!
   - Actual `datasets/leeky/adapted/dev_64/2dda45799bcf74a9_w64.json` (`in = 2,025 -> gt = 9`) -> MUST collapse dramatically (`<= 50`, ideally exact `9`!) in `< 1.0s` with independent `mba_proof` replay!
   - Actual `datasets/leeky/adapted/dev_64/49daaea28fe9a442_w64.json` (`in = 3,021 -> gt = 24`) -> MUST collapse dramatically (`<= 100`, ideally `<= 30`!) in `< 1.5s` with independent `mba_proof` replay!
2. **Fast Smoke Gate ONLY (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`):**
   - `datasets/hard_cases/regression_smoke` (`62` cases -> `/tmp/r67-smoke/out.jsonl`): **MUST PASS `62/62` proved & strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
3. Record a crisp 1-paragraph Round-67 sprint note in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT run `dev_64`, `L5`, `core_hard`, or `heldout_balanced64` yet!).
