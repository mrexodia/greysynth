# GreySynth Round-7 Review: Milestone 3B.2 Audit, Semilinear Gaps & Milestone 4A E-Graph Spec

**Reviewed commits:** `0213826..f49f1ee` (7 commits since `eae80e4`)  
**Summary:** Outstanding execution! All 6 Round-6 bugs are verified fixed and independently live-probed (**13/13 `proved_compositional`**), and **all four 100-case benchmark datasets now beat supplied ground-truth legacy cost (`< 1.00x` geometric quality)** with **400/400** freshly proved outputs and **1,000/1,000** on C-Full (984 strict reductions, 0 regressions):

| 100-Case Dataset | Pre-Ring Baseline | Current (`f49f1ee`) | Geometric Compression | Proved |
|---|---:|---:|---:|---:|
| `PLDI Poly` | 1.0602x | **0.8812x** | 3.70x | 100/100 |
| `PLDI Non-Poly` | 19.2494x | **0.9394x** | **52.25x** | 100/100 |
| `MBA-Obfuscator nonlinear` | 11.4734x | **0.8693x** | **14.41x** | 100/100 |
| `QSynth EA` | 1.0073x | **0.9673x** | 11.94x | 100/100 |

Below are **4 concrete code bugs** found in `d525c4d`, **2 high-ROI semilinear fixes** exposed by probing `CoBRA/test/datasets/msimba.txt`, and the implementation spec for **Milestone 4A (Bounded E-Graph Unification)** — the final major architectural pillar from `docs/neon-review-5.md`.

---

## 1. Live Probe Verification & New Torture Cases (`f49f1ee`, `default.json`, `total_timeout=5`)

All previously failing Round-6 probes now pass in **22–81 ms** (`proved_compositional`):
- `nonpoly_L2_inner`: `27 -> 1` (`a`, `0.024s`), `nonpoly_L2_full`: `121 -> 3` (`a * y`, `0.032s`)
- `linear_eq_a_plus_b`: `44 -> 3` (`a + b`, `0.028s`)
- `linear_big64_const_off`: `14 -> 1` (`0xedcba98765432114`, `0.025s`)
- `linear_big64_coeffs`: `19 -> 1` (`0`, `0.025s`)
- `linear_big_subterm_atom`: `25 -> 3` (`x * y`, `0.050s`)
- `poly_mba_cancel_2term`: `21 -> 1` (`0`, `0.022s`, 1 ring edge)
- `null_poly_64bit`: `11 -> 1` (`x`, `0.053s`), `null_poly_32bit_cubic`: `17 -> 1` (`x`, `0.039s`)
- `semilinear_bit_sliced`: `35 -> 3` (`y + x`, `1.058s`), `nested_mba_with_div`: `25 -> 3` (`x / y`, `0.081s`)

**New failing torture cases from `CoBRA/test/datasets/msimba.txt` & scaled masks:**
- **`msimba_L3_const_atoms`** (`msimba.txt` line 3, ground truth `1111 * (x ^ C1)`, size **5**): `242 -> 171` (`4.87s`, 3 inconclusive).
- **`masked_const_xor`** (`3*(x & 0x0f0f...) + 3*(x & 0xf0f0...) + 5*(y & 0x00ff...) + 5*(y & 0xff00...)`, ground truth `3*x + 5*y`, size **7**): `23 -> 23` (`4.69s`, 0 candidates).
- **`msimba_L2_bitsliced`** (`msimba.txt` line 2, 26 distinct bit-mask terms, ground truth `-7360133807098015136 ^ (-4 & x)`, size **5**): `165 -> 160` (`4.15s`).

---

## 2. Four Concrete Bugs in `d525c4d` (`src/greysynth/normalization.ml`)

### Bug 1: `RingMonomial.compare` uses `Stdlib.compare` on `E.t list` (`normalization.ml:847-850`)
```ocaml
module RingMonomial = struct
  type t = E.t list
  let compare = Stdlib.compare
end
```
`mul` sorts monomials with `E.compare` (line 886), while `RingMonomial` keys the map with `Stdlib.compare` (structural comparison of hash-consed ASTs — both $O(\text{AST size})$ and potentially inconsistent with `E.compare`).
- **Fix:** `let compare = List.compare E.compare`.

### Bug 2: `ring_polynomial_candidate` & `minterm_polynomial_candidate` lack DAG memoization, an op-count cap, and `!cost_model` awareness (`normalization.ml:856-949`)
1. `parse` (`lines 892-901`) recursively walks `expression` without a memo table and `mul` has no operation counter cap — a shared DAG with `Mul` nodes can trigger exponential traversal.
2. Lines 937 and 946 compare `Greysynth_utils.Utils.size_of_expr candidate < Greysynth_utils.Utils.size_of_expr expression` (unmemoized legacy size!) instead of passing the DAG-memoized `cost` function from `run`, violating the configured `cost_model` (`paper_ast`, `instruction`, `readability`).
- **Fix:** Pass `cost` into `ring_polynomial_candidate` and `minterm_polynomial_candidate`, memoize `parse` in a `Nodes` table, and add an `ops` guard (e.g., `max_ops = 50_000`) inside `add_term`.

### Bug 3: `factor_group_candidate` only tries 1 factor and emits uncleaned `* 0` / `+ 0` (`normalization.ml:988-1064`)
1. Lines 988–1002 pick only the single highest-frequency factor `selected`. If that factor's cofactor does not simplify (e.g. a non-MBA variable appears in 4 terms while an MBA factor appears in 3 terms), factoring gives up completely instead of trying the next highest-frequency factors.
2. Lines 1059–1063 build `(factor * simplified) + remainder_expression` literally, so when `remainder = []` it emits `(factor * simplified) + 0` (+2 wasted cost!) and when `simplified = 0` it emits `(factor * 0) + remainder_expression` (failing the `cost candidate >= cost expression` check!).
- **Fix:**
  - Try the top 6 candidate factors (sorted by frequency descending, tie-broken by `E.compare`).
  - Clean `simplified_factored` (`0` if `simplified = 0`, `factor` if `1`, `-factor` if `-1`) and omit `+ 0` when `remainder = []`, attaching one extra trivial `"ring_mod2w"` edge `(raw_simplified, cleaned_candidate)` so congruence closure proves `expression == cleaned_candidate` directly.

### Bug 4: Constant-complement atom doubling breaks `msimba` constant-mixed linear MBAs (`normalization.ml:383-390, 560-610`)
`msimba.txt` lines 3–1000 are 4-atom linear MBAs over `(x, C1, C2, C3)` using both `Ci` and `~Ci`. Because `peepholes` constant-folds `~Ci` into a distinct constant `Ci'`, both `linear_candidates` and `minterm_ring_expansion` see **7 atoms** (`x, C1, C1', C2, C2', C3, C3'`), exceeding `normalization_max_atoms = 6` and aborting with `Too_complex`!
- **Fix:** When collecting atoms inside bitwise contexts in `linear_candidates` and `minterm_ring_expansion`, canonicalize every constant `c` (other than `0` and `-1`) by pairing `c` and `~c` under a single canonical atom `canonical = min_bv c (Bitvector.lognot c)`, representing the complement as `Not(canonical)`!
  - Drops `msimba_L3_const_atoms` from 7 atoms to **4 atoms** (`x, C1, C2, C3`), collapsing `242 -> 5` (`1111 * (x ^ C1)`) in milliseconds!
- **Companion semilinear pass (`masked_const_xor` & `msimba_L2_bitsliced`):**
  1. Extend scalar-scaled disjoint mask merging: `c * (x & M1) + c * (x & M2) -> c * (x & (M1 | M2))` (proved via 1 `"smt"` edge `(x&M1)+(x&M2) == x&(M1|M2)` + 1 `"ring_mod2w"` edge — collapses `masked_const_xor` `23 -> 7` in `< 5 ms`!).
  2. Add a 1-variable bit-sliced semilinear probe (`c0 = f(0)`, `d_b = f(1 << b) - c0` for `b = 0..w-1`) to recognize affine masked/XOR forms `a * ((x & M) ^ K) + c` (like `msimba_L2_bitsliced` `165 -> 5`), certified via disjoint-mask `"smt"` edges + `"ring_mod2w"`.

---

## 3. Milestone 4A Spec: Bounded E-Graph Unifying Normalization, OES & Proof Extraction

This is the final major architectural shift from [docs/neon-review-5.md](neon-review-5.md) — eliminating the destructive phase-ordering regressions (`+249/-254` AC, `+217/-218` portfolio) that have kept AC normalization and multi-representative OES opt-in.

### Architecture (`src/greysynth/egraph.ml` + integration in `greysynth.ml`)
1. **Hash-consed E-Graph + Union-Find (`max_enodes = 8_192`, `max_iters = 4–6`, strict `check_timeout ()`):**
   - E-node shapes mirror `Rewrite_proof.shape` (`Variable`, `Value`, `Unary`, `Binary`, `Conditional`), with child IDs canonicalized to e-class representatives (`find id`).
   - Maintain a hash-cons table `(width, canonical_shape) -> enode_id`, per-e-class e-node lists, and a **proof forest**: every `union` between two e-classes stores the exact proved justification (`lhs_expr`, `rhs_expr`, `equalities`, `ring_equalities`, `pass`).
   - **Non-negotiable invariant:** Never union two e-classes without passing the shared proof-gated acceptance policy (`Rewrite.accepts` / `Rewrite.accepts_compositional` — including `ring_mod2w`!).
2. **Non-Destructive Saturation Passes:**
   - **Seed** the e-graph from the input AST (after fast deterministic normalization OR as the core normalization+OES driver).
   - **Algebraic & AC saturation:** For each e-class's cheapest representative (and AC-normalized variant), generate peepholes, AC reassociations, `ring_polynomial_candidate`, `factor_group_candidate`, `minterm_polynomial_candidate`, `linear_candidates`, and `product_partition_candidate`. Unlike destructive rewriting, **allow equal-cost or slightly larger useful forms** (e.g., AC canonical form) to be added & unioned into the same e-class without losing the original form!
   - **Semantic OES saturation directly on e-classes:** Evaluate each e-class representative on the contextual sample bank (`evaluator`), bucket by output hash, and when two distinct e-classes share a hash, verify equivalence (`minterm_ring_proof` / `Rewrite.accepts`) and **union** their e-classes!
   - Maintain congruence closure (`rebuild`) after each round of unions so newly merged child classes automatically expose parent simplifications.
3. **Global Bottom-Up Cost Extraction:**
   - Run fixed-point DP over e-classes to select the globally minimum-cost acyclic term for every e-class under `!cost_model` (`legacy`, `paper_ast`, `instruction`, `readability`), tie-breaking deterministically by `E.compare`.
4. **Minimal Proof-Spanning-Tree Emission:**
   - Walk only the proof-forest path(s) actually connecting the original root e-node and the extracted output e-node (plus congruent child paths), emitting ONLY those edges into `Rewrite.journal`. Discarded saturation alternatives emit **zero** proof obligations and require **zero** brittle cache checkpointing!
5. **Config & Rollout:**
   - Add `egraph_extraction` (bool, reported in `report_json`, exposed in `Config`).
   - Keep `default.json` safe until verified on C-Full: if `egraph_extraction: true` achieves **>= 984/1,000 strict reductions**, **1,000/1,000 `mba_proof` replay**, and **strictly improves over baseline with zero/near-zero AC regressions**, promote it (or document exact wall-time/quality tradeoffs in `docs/IMPLEMENTATION_RESULTS.md`).

---

## 4. Acceptance Targets for This Iteration

1. Fix all **4 bugs** in `normalization.ml` (`RingMonomial.compare`, memoized/cost-aware `ring_polynomial_candidate`, multi-factor + cleaned `factor_group_candidate`, constant-complement atom canonicalization) + add scaled-mask / 1-var bit-sliced semilinear pass.
2. Add focused unit tests for `msimba_L3_const_atoms` (`242 -> 5`), `masked_const_xor` (`23 -> 7`), `msimba_L2_bitsliced` (`165 -> 5`), and multi-factor/cost-model polynomial normalization.
3. Implement **Milestone 4A (`src/greysynth/egraph.ml`)** with unit tests demonstrating:
   - Non-monotonic / equal-cost AC rewrite exposing a strictly cheaper parent without losing the original form,
   - OES class merging inside the e-graph,
   - Global cost extraction under `legacy` and `paper_ast`,
   - Minimal spanning-tree certificate replay via `mba_proof`.
4. Run `make test` (all green), audit `msimba` (first 100 cases of `CoBRA/test/datasets/msimba.txt`), verify no regression on the 4×100 MBA smoke sets, and run the 1,000-case C-Full audit comparing baseline vs. `egraph_extraction: true` (with AC enabled!).
5. Update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md` and commit atomically (do not modify `docs/neon-review*.md`).
