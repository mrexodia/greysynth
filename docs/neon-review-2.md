# MBA Simplification Follow-Up Review (Post-`5701b3e`)

Follow-up review of `docs/PLAN.md`, `docs/IMPLEMENTATION_RESULTS.md`, and the codebase at commit `5701b3e` ("Record compositional polynomial coverage"), with live read-only probes in the Dev Container (including independent `mba_proof` replay on every case).

All six original bugs from `docs/neon-review.md` have been resolved (`XO.ITE` 1-bit condition, `XO.Im` `ones` vs `fill`, `SMod_x86` div-by-zero, Xyntia wall-clock/`SIGALRM`, `binsec_simplify` edge cases, CHS horizon restart, pass-separated equivalence metrics, DAG memoization, and bounded `invert_kids`). The compositional proof architecture is now verified end-to-end (`zero_poly_ghost`: `31 -> 3` in `0.02s`, `bool_3var_dnf`: `29 -> 5` in `0.02s`, `linear_5var_sum` under `normalization_portfolio`: `37 -> 1` in `0.03s`, all passing fresh `mba_proof` replay).

Below are the concrete bugs/regressions spotted in the new code and the highest-ROI remaining MBA simplification priorities.

---

## 1. Bugs & Regressions to Fix in the New Code

### 1.1 `product_partition_candidate` drops commuted proofs (`src/greysynth/normalization.ml:499-550`)
Live probe results:
- `(x & y) * (x | y) + (x & ~y) * (~x & y)` -> **`x * y` in 0.02s** (`proved_compositional`).
- `3 * ((x & y) * (x | y)) + 3 * ((x & ~y) * (~x & y))` -> **stuck at `(((x & ~y) * (~x & y)) + ((x & y) * (x | y))) * 3`** (`21 -> 19`, `inconclusive: 3`).
- `(x & y) * (x | y) + ((~y) & x) * (y & (~x))` -> **stuck at `17 -> 17`** (`inconclusive: 1`).

Root causes:
1. `mba_proof`'s congruence closure does **not** assume commutativity of `+` or `*`. When `try_order y x` matches a commuted sum `second + first`, `equalities` (`normalization.ml:534-539`) connects `left2 + (m2 * m3)` to `x * y`, **not** `(m2 * m3) + left2`. The same failure occurs if `first` is `(x | y) * m1` or `second` is `m3 * m2`: the missing commutativity equalities (`(add second first, add first second)`, `(mul union_term m1, mul m1 union_term)`, `(mul m3 m2, mul m2 m3)`) cause `Rewrite_proof.verify` to return `"incomplete_derivation"` -> `inconclusive`.
2. `m2` and `m3` (`normalization.ml:514-516`) require exact operand order `x & ~y` and `~x & y`, failing to match commuted `(~y) & x` or `y & (~x)` (and missing the corresponding `And` commutativity edges).

### 1.2 Derived constant seeding (up to 32 constants) heavily dilutes Xyntia variable sampling
Look at `src/greysynth/synthesis.ml:264-303` vs. `outside_tools/xyntia/src/lib/tree/mutations.ml:464-469`:
```ocaml
let random_terminal (bitsz : int) : mutd t =
  let nvars = O.nvars () in
  let nconsts = O.nconsts () in
  let choice = Random.int (nvars + nconsts) in
  if choice < nvars then mk_terminal bitsz (mk_var (random_var ()))
  else mk_terminal bitsz (mk_const (random_const ()))
```
With `add_constants_to_synthesis: true`, `make_problem` now injects up to **32 constants** (plus Xyntia's own built-in `1` in `outside_tools/xyntia/src/lib/oracle.ml:250`). For a 2-variable subtree with 3 constants, Xyntia now picks a variable only **`2 / 34 = 5.9%`** of the time (down from 40% before commit `bff1cfd`). Even with 0 constants in the subtree, `seeds` adds 4 constants (+ Xyntia's duplicate `1`), cutting variable sampling from 67% to 29%.
- **Fix**:
  1. In `outside_tools/xyntia/src/lib/tree/mutations.ml:464-469`, coin-flip `variable` vs. `constant` (e.g., 50/50 or 70/30) before sampling uniformly within the chosen class, rather than weighting by `nvars / (nvars + nconsts)`.
  2. Tighten the cap in `src/greysynth/synthesis.ml:294` (e.g., 8–12 derived constants on first pass; deduplicate against Xyntia's built-in `1`).

### 1.3 `ac_normalization` unary-negation cost penalty & `normalization_portfolio` certificate bloat
- In `src/greysynth/normalization.ml:207-216`, `canonical_candidates` emits negative terms as `Plus (..., Unary Minus atom)` instead of binary `Minus`. Every negative term pays **+1 cost** (`a + (-b)` costs 4 vs. `a - b` costing 3), and `collect` omits constant left-shifts (`x << k = (2^k) * x`). Reconstructing positive and negative terms as `sum_pos - sum_neg` removes this penalty and should address many of the 254 C-Full regressions seen with `ac_normalization: true`.
- In `src/greysynth/greysynth.ml:53-71`, `normalization_portfolio` runs both `Normalization.run` branches against the **same** `!Rewrite.journal`, so all obligations from the *discarded* branch remain in the certificate. Because `Rewrite_proof.verify` (`src/proof/rewrite_proof.ml:397-416`) checks every obligation in the file, portfolio mode roughly doubles `mba_proof` replay cost.
  - **Fix**: Buffer branch obligations (or snapshot/commit only the winning branch's equalities into `!Rewrite.journal`), and/or prune unused obligations in `Rewrite_proof.finish` / stop early in `mba_proof` once congruence connects `input_id` and `output_id`.

### 1.4 Unmemoized `balance_associative`, `accepts_compositional` cache/timeout gaps, and grammar/cost drift
- `src/greysynth/synthesis.ml:97-129`: `balance_associative` walks the *entire* subtree below `expr` with **no DAG memoization** on every `truncate` call. Memoize with `Sexpr.BvTbl` (or stop descending past `depth`) to avoid blowup on large shared DAGs (like 35k-node `target_1562`).
- `src/greysynth/rewrite.ml:64-98`: `accepts_compositional`:
  1. Bypasses `Rewrite.proofs` when checking local micro-steps (re-proving the same 10 equalities on every occurrence during producer execution; keep `mba_proof` cache-free, but reuse `Rewrite.proofs` inside `Rewrite.accepts_compositional`).
  2. Does not call `check_timeout ()` between obligations.
  3. Ignores `!c_reject_non_equiv_simplifications = false`.
- `src/greysynth/normalization.ml:556-586`: duplicates the `cost_model` weight table from `src/utils/utils.ml:208-240`; share one helper to prevent drift.
- `src/greysynth/synth_backends.ml:253-258`: `xyntia_grammar_for_profile "auto"` drops `ITE` when `division = true` (Xyntia's `"full"` has no `ITE`) and drops shifts when `conditional = true` (`"mba_ite"` has no shifts). Worth addressing when Milestone 9 enables conditional synthesis on mixed expressions.

### 1.5 Structured basis samples only apply to `sampling_strategy: "label"`
In `src/greysynth/synthesis.ml:200-232`, the `(0,...,0)`, `(1,...,1)`, and one-hot basis rows are only generated for `LabelValues`, not in `src/greysynth/sample_evaluator.ml:58-68` for `RealValues` (the default). Under `"real"`, original variables still receive identical values on samples `0..4`, so XSmir `Affine`/`Poly2` will still hit `Assert_failure` in `LinearComb.search_inputs` until Milestone 6 moves explicit per-variable basis environments into `Sample_evaluator`.

---

## 2. Live Probe Reality Check: "Strict Reduction" vs. Ground-Truth Quality

`docs/IMPLEMENTATION_RESULTS.md:87-89` correctly notes that `399/400` strict reductions is not equivalent to matching ground truth. Live probes under `default.json` (`equiv_timeout = 1`, `total_timeout = 4`) highlight the gap:

| Case | Ground truth | `default.json` | `portfolio + frontier=4` | Why it stalled |
|---|---:|---:|---:|---|
| `linear_3var_const_offset` (16-bit) | size **7** (`67 + (a\|b\|c)`) | **24 -> 24** (`inconclusive: 2`) | **24 -> 24** (`inconclusive: 3`) | Passes at `equiv_timeout = 5` in `normalization_test.ml`, **times out at `equiv_timeout = 1`** because `65469 * ~(a&b&c) + 65470 * (a&b&c)` is proved as one monolithic `bvmul` query. |
| `poly_mba_cancel` (64-bit) | size **11** (`22*(x&y)-17*x-5*y`) | **167 -> 157** | **167 -> 157** | Only `product_partition_candidate`'s 1 hardcoded pattern exists; general polynomial MBAs do not collapse. |
| `linear_5var_sum` (64-bit) | size **1** (`b`) | **37 -> 21** (`inconclusive: 4`) | **37 -> 1** (`0.03s`, proved!) | Solved when AC/portfolio is active, still misses under `default.json`. |
| `zero_poly_commuted` (64-bit) | size **3** (`x * y`) | **17 -> 17** (`inconclusive: 1`) | **17 -> 17** (`inconclusive: 1`) | Bug 1.1 above (missing commuted `&`/`+`/`*` match and equalities). |
| `scaled_poly_partition` (64-bit) | size **5** (`3 * (x * y)`) | **21 -> 19** (`inconclusive: 3`) | **21 -> 19** (`inconclusive: 5`) | Factored out `3`, then hit Bug 1.1 on the commuted inner sum. |

---

## 3. Prioritized Next Steps for `docs/PLAN.md`

1. **Add ground-truth quality ratios to `scripts/audit_dataset.py` now**:
   - Report geometric & arithmetic mean `syn_cost / gt_cost` and `obf_cost / syn_cost` under both `legacy` and `paper_ast` (matching Paper Table 2). Without this, a `167 -> 157` reduction is indistinguishable from a `167 -> 11` ground-truth recovery in corpus summaries.
2. **Generalize compositional proofs to arbitrary 2/3-var minterm polynomials & constant-multiplied linear MBAs (Milestone 3)**:
   - Replace the single-shape `product_partition_candidate` with a general **disjoint-minterm polynomial ring normalizer** over $\mathbb{Z}/2^w\mathbb{Z}[m_1,\dots,m_{2^k-1}]$, emitting Layer-1 linear disjoint-minterm equalities + Layer-2 distributive/collect-like-terms ring micro-steps. This solves `poly_mba_cancel` (`167 -> 11`), `zero_poly_commuted`, `scaled_poly_partition`, and most of `ProMBA Poly` / `mba_obf_nonlinear`, all replayable in `mba_proof`.
   - Emit 2–3 micro-steps for `linear_candidates` whenever constant multipliers appear (e.g., `c * ~t -> -c * t - c`, combine linear coefficients per bitwise atom, then prove the multiplication-free Boolean identity). This makes `linear_3var_const_offset` prove in **< 5ms at `equiv_timeout = 1`** instead of requiring a 5s Bitwuzla timeout.
3. **Complete the remaining deterministic MBA passes (Milestone 3)**:
   - Connected-component partitioning of linear terms (eliminating the 4-atom / 256-node ceiling without relying on greedy AC).
   - Bit-partitioned semilinear mask reconstruction (for folded masks where the base variable is not already present in the tree for OES, e.g., `((x & 0x1234) + (x & 0xedcb)) + y` or `(x & 0x0f0f) + (y & 0xf0f0)`).
   - Univariate/affine permutation-polynomial inversion ($P(Q(x)) \equiv x \pmod{2^w}$) for `MBA-Obfuscator` (`non_polynomial+zero`).
   - Local-subtree subprocess oracle for `../rumba` (MIT) or `../CoBRA` (Apache-2.0) on maximal pure-MBA subtrees detected by `src/utils/mba_classifier.ml`.
4. **Reusable universal CHS rules (Milestone 5) + explicit `Sample_evaluator` environments & CEGIS (Milestone 6)**:
   - Move zero/all-one/one-hot/bit-boundary strata into `Sample_evaluator` so `RealValues` unlocks XSmir `Affine`/`Poly2` escalation (Milestone 7) and CEGIS counterexample refinement.
   - Prove and cache universal Greek-variable CHS rules across alpha-renamed/commuted templates for major speed and compression gains on Tigress levels 5–8 and OMVLL.
5. **Fix the 5 surgical items in Section 1** (`product_partition_candidate` commutativity, Xyntia `random_terminal` coin flip, `canonical_candidates` `sum_pos - sum_neg` + portfolio journal pruning, `balance_associative` memoization, and `accepts_compositional` local cache/timeout checks).
