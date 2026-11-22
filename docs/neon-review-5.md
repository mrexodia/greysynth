# GreySynth Round-5 Architectural Review: Breaking Out of the Local Optimum

**Reviewed commit:** `4dd6e71` ("Prioritize native compositional MBA passes", following `b69b4e2`)
**Purpose:** Verify Round-3 bug fixes and pivot [docs/PLAN.md](PLAN.md) from incremental local optimizations (50-edge Bitwuzla micro-step chains + destructive greedy peepholes + saturated C-Full/CHS tuning) to the three architectural upgrades that unlock 10x–20x quality gains across all MBA families while keeping native OCaml passes primary (building on [docs/neon-review-4.md](neon-review-4.md)).

---

## 1. Status of Round-3 Fixes (`3c5af95..4dd6e71`)

All six concrete bugs from [docs/neon-review-3.md](neon-review-3.md) were addressed cleanly:

| Item from `neon-review-3.md` | Status | Commit / Evidence |
|---|---|---|
| Bug 1: `Sample_evaluator` diagonal collapse | **Fixed** | `116a521` — `rank` and `seed` now diversify bit positions, rotating masks, and mode selection (`src/greysynth/sample_evaluator.ml:93-125`). |
| Bug 3: `Rewrite_proof.abstract_pair` small shared terms & constants | **Fixed** | `b9831ef` — tracks `occurs_left`/`occurs_right` separately; abstracts shared `cost >= 2` subterms and nontrivial constants (`src/proof/rewrite_proof.ml:223-261`). |
| Bug 4: `Rewrite.accepts_compositional` inconclusive budget cache | **Fixed** | `ef7f0ab` — caches `Unknown` with `budget` (`src/greysynth/rewrite.ml:120-162`). |
| Bug 5: `linear_candidates` 6-atom two-value recovery & visit cap | **Fixed** | `cc0b82c` — cap raised and two-value recovery extended to `min 6 !c_normalization_max_atoms` (`src/greysynth/normalization.ml:421, 551`). |
| Bug 6: `universal_rules` canonicalization, budget clamping, `report_json` | **Fixed** | `1bb6340`, `4de91a3` — alpha/commutative rule keys, clamped generalization budget, full `report_json` config reporting. |
| Bug 2: `mba_oracle` `Lsl`, timeout clamping, root-first targeting | **Mostly fixed (1 bug left)** | `fb4e239` — see Section 2 below (`visit` does not forward `~allow_oracle`, and mixed roots still recurse bottom-up into leaf subtrees). |
| Native disjoint-minterm linear MBA pass | **In progress** | Tracked in `neon-review-4.md`; `PLDI Non-Poly` currently at **19.25x**. |
| Native multiplicative factor-grouping / polynomial pass | **In progress** | Tracked in `neon-review-4.md`; `MBA-Obfuscator nonlinear` currently at **11.47x** (`poly_mba_cancel` `167 -> 157` vs. ground truth `11`). |

---

## 2. One Small Bug Left in `fb4e239` (`src/greysynth/normalization.ml:877-938`)

In `visit ?(allow_oracle = true) original`:
1. Lines 886–890 call `visit x`, `visit y`, `visit c`, `visit t`, `visit e` **without forwarding `~allow_oracle`**, so `allow_oracle` silently resets to `true` on every recursive child call. Both `visit ~allow_oracle:false candidate` (line 936) and `visit ~allow_oracle:false expression` (line 937) therefore only suppress `try_oracle` at the root node itself, not on descendants.
2. When the root is *not* pure-MBA (e.g., an `Ite` or `Uext` wrapping a large pure-MBA subtree), line 938 runs `visit expression`, which recurses bottom-up into children *before* testing `oracle_compatible` on maximal pure-MBA children — allowing leaf-side size-11 subtrees to consume `oracle_calls` before the maximal pure-MBA child is reached.

**Fix:** Run a dedicated top-down pass for maximal `oracle_compatible` subtrees (descending by cost, stopping recursion inside any compatible subtree once it is tried, or running as a post-pass on residual maximal pure-MBA subtrees after deterministic normalization), and forward `~allow_oracle` everywhere `visit` recurses.

---

## 3. Why the Previous Trajectory Was Converging to a Local Optimum

Look at the empirical pattern in [docs/IMPLEMENTATION_RESULTS.md](IMPLEMENTATION_RESULTS.md):
- **C-Full (984/1,000)** is effectively saturated, yet every new local rewrite causes phase-ordering churn:
  - AC normalization: **+249 improved / -254 regressed**.
  - `preprocessing_portfolio` (baseline vs. AC): **+217 improved / -218 regressed**.
  - Rumba oracle on `PLDI Non-Poly`: strict reductions **dropped 99 -> 98** (`19.25x -> 18.97x`).
- Meanwhile, the two dominant quality cliffs (`PLDI Non-Poly` at **19.25x** and `MBA-Obfuscator nonlinear` at **11.47x**) and unmeasured nonlinear suites (`ProMBA`, `Loki`, `OMVLL`, `Tigress 6–8`, `C-BeyondMBA`) are barely moving.

Four structural bottlenecks explain *all* of these symptoms at once:

1. **Bitwuzla-only proof kernel:** `Rewrite_proof` currently forces Bitwuzla to prove modular 64-bit ring arithmetic (`+`, `-`, `*` mod $2^{64}$). Bitwuzla solves pure bitwise identities in **0.6–1.6 ms** but times out (>2000 ms) on multi-multiplier 64-bit ring identities. Hand-emitting 50–100 binary Bitwuzla micro-steps per linear/polynomial expression works as an immediate stopgap (and keeps pure-SMT replay), but bloats certificates, multiplies replay latency, and scales poorly to higher-degree polynomials (`perm_poly_quad`, `ProMBA Poly`) and differential oracle checks.
2. **Destructive greedy single-tree rewriting (`cost candidate < cost current`):** Overwriting the AST whenever a local rewrite shrinks cost destroys downstream OES matches and blocks non-monotonic algebraic derivations (expand -> cancel -> factor -> collapse). That is why AC, portfolios, and oracles keep regressing half the corpus.
3. **Ad-hoc pattern accumulation in `normalization.ml` (938+ lines):** Adding dataset-specific patterns (`complement_product_steps`, `product_partition_candidate`, commuted/scaled variants, `merge_masked_addition`) chases individual benchmarks instead of implementing the 3 general native MBA solvers (linear + bit-sliced semilinear, multivariate polynomial/factoring + permutation-polynomial inversion, grey-box OES/CHS fallback).
4. **Over-investment in stochastic synthesis tuning (CHS/Xyntia) before fixing algebraic normalization:** MCTS/enumerative search cannot reliably discover 64-bit nonlinear factorizations or invert degree-2/3 permutation polynomials; its rightful role is strictly residual mixed-operator / conditional / non-algebraic handlers.

---

## 4. The Three Strategic Shifts (Updated in `docs/PLAN.md`)

### Shift A: Add a Small, Auditable, Decidable $\mathbb{Z}/2^w\mathbb{Z}$ Ring Checker Rule to `Rewrite_proof`

`Rewrite_proof.verify` already has a trusted ~50-line congruence-closure checker (`congruent` at `src/proof/rewrite_proof.ml:355-395`). Adding a second equally small, auditable, zero-dependency kernel rule — **formal commutative-ring equality over $\mathbb{Z}/2^w\mathbb{Z}$** — transforms proof tractability overnight without compromising soundness:

- **Certificate representation (v1-compatible):** Add an optional `"rule"` field on equality edges (`"smt"` default when omitted; `"ring_mod2w"` for ring obligations). Old v1 certificates replay identically; new certificates remain self-contained and untrusted until replayed by `mba_proof`.
- **Exact semantics of `"ring_mod2w"` (keep the trusted kernel tiny — ~80 lines):**
  - Only five operations are interpreted as ring syntax: `bvadd`, `bvsub`, `bvneg`, `bvmul`, and `const` (at a single uniform bit width `w`). Every other node (`var`, `bvand`, `bvor`, `bvxor`, `bvnot`, `bvshl`, `ite`, `extract`, etc.) is treated as an **opaque indeterminate** keyed by its interned `node id` in `Rewrite_proof.graph`.
  - Normalize `lhs - rhs` to a canonical sparse polynomial: a sorted map from sorted multiset of indeterminate IDs (monomial) to exact `Z.t` coefficient modulo $2^w$, dropping zero coefficients.
  - Accept iff the resulting polynomial map is empty (`0`).
  - **DoS / replay guard:** Enforce strict per-edge caps (e.g., `max_degree = 16`, `max_monomials = 4096`); if exceeded, reject the edge as unproved.
  - **Verification of the checker itself:** Add dedicated randomized property tests comparing `"ring_mod2w"` verdicts against Bitwuzla across 8/16/32/64-bit widths and non-ring edge cases (overflow wraparound, subtraction, negation, opaque subterms, degree/monomial limits).
- **How `"smt"` + `"ring_mod2w"` + `congruent` compose cleanly:**
  - **Any 64-bit linear MBA $E \to C$** ($k \le 6$ atoms):
    1. Emit tiny pure-bitwise `"smt"` edges expanding each distinct bitwise subterm $B_i$ (and `-1` if constant offset $\ne 0$) into the disjoint Boolean minterms $M_0, \dots, M_{2^k-1}$ (`B_i == sum_{p in S_i} M_p` — **0.6–1.6 ms each** in Bitwuzla!).
    2. Build `E_minterms` and `C_minterms` by substituting those expansions. Congruence closure links `E == E_minterms` and `C == C_minterms` automatically.
    3. Emit **one single `"ring_mod2w"` edge** `(E_minterms, C_minterms)` — **< 0.1 ms**!
    - Example: `nonpoly_L2_inner` (`29 -> 1`) drops from **>6,000 ms timeout** to **~3 ms** across just **4 edges** (instead of 40–100 binary Bitwuzla edges).
  - **Any factored / nonlinear polynomial MBA** (`MBA-Obfuscator nonlinear`, `poly_mba_cancel` `167 -> 11`):
    1. Expand bitwise atoms inside linear cofactors (or whole terms) via 1 ms `"smt"` minterm edges.
    2. Emit **one single `"ring_mod2w"` edge** proving the distributed/factored ring equality in **< 0.2 ms**.
  - **Univariate/multivariate permutation-polynomial inversion (`perm_poly_quad`, `ProMBA Poly`):**
    - Formal ring identities (`P^{-1}(P(x)) == x` in $(\mathbb{Z}/2^w\mathbb{Z})[x]$) prove in **one `"ring_mod2w"` edge (< 0.1 ms)**.
    - When `P^{-1}(P(x)) - x` is a **non-trivial null polynomial** over $\mathbb{Z}/2^w\mathbb{Z}$ (e.g., $2^{w-1} \cdot x(x-1) \equiv 0 \pmod{2^w}$), prove the small falling-factorial null lemma (`2^(w-1) * (x * (x - 1)) == 0`) with a local `"smt"` edge, and let `"ring_mod2w"` + congruence closure finish the rest! Keep `"ring_mod2w"` strictly formal-ring so the trusted kernel stays trivial to audit.
  - **Differential external oracles (`rumba`, `cobra`):**
    - Instead of rejecting Rumba's 64-bit answers with monolithic `smt_inconclusive`, run a **proof-reconstruction bridge**: try `"ring_mod2w"` directly, then minterm-expanded `"ring_mod2w"`, and only fall back to monolithic `"smt"` when non-ring operators prevent ring decomposition.

### Shift B: Replace Ad-Hoc MBA Peepholes with Three General Native OCaml Solvers

1. **General Linear + Bit-Sliced Semilinear Solver (closes `PLDI Non-Poly` `19.25x`):**
   - Back `linear_candidates` with **minterm + `"ring_mod2w"`** proof construction so every 64-bit linear MBA (any coefficients, up to 6 atoms) succeeds deterministically in milliseconds.
   - Add **connected-component atom splitting** (when a large linear MBA has disjoint variable/atom clusters, solve each component independently without hitting $2^k$ blowup).
   - Add **bit-sliced / masked semilinear reconstruction**: partition bit positions by constant masks (`x & mask`, shifts, low/high masks) and run the linear solver on each homogeneous mask slice (handling `C-MBA`/Tigress/OMVLL masked MBAs generally rather than one-off `merge_masked_addition`).
2. **General Nonlinear / Polynomial MBA Normalizer (closes `MBA-Obfuscator nonlinear` `11.47x` & `ProMBA Poly/Non-Poly`):**
   - **Subterm lifting (GAMBA/ProMBA style):** treat non-MBA subexpressions (`Udiv`, `Lsr`, `Ite`, `Extract`, `Concat`, nested nonlinear roots) as opaque variables so inner and outer MBAs simplify cleanly.
   - **Multiplicative factor grouping + cofactor reduction:** flatten additive sums of products, group terms sharing common bitwise/subterm factors $F_i$, and run the linear MBA solver on each cofactor $L_i$ — certified in milliseconds by `"ring_mod2w"`.
   - **Sparse modular polynomial normalization & permutation-polynomial inversion:** expand bounded-degree polynomials over $\mathbb{Z}/2^w\mathbb{Z}$ in the monomial basis; detect univariate invertible polynomials $P(x)$ (odd linear coefficient $a_1$, even higher coefficients $a_2, a_3, \dots$ — Rivest's theorem for permutation polynomials mod $2^w$) and invert via Hensel lifting / Newton iteration mod $2^w$ when composing $Q(P(x))$ reduces degree/cost.
3. **Differential Oracle Hygiene (Opt-In Only):**
   - Fix the `allow_oracle` recursion bug and invoke top-down on maximal pure-MBA subtrees, verifying candidates through the minterm + `"ring_mod2w"` proof bridge for differential testing while keeping native OCaml passes primary.

### Shift C: Unify Normalization + OES + Proof Recording into a Bounded E-Graph

Stop fighting phase-ordering regressions with fragile portfolios and destructive greedy rewrites:
- `Rewrite_proof` **already** implements a hash-consed term DAG (`graph`) + union-find congruence closure (`congruent`).
- Build a **bounded e-graph** (capped at e.g. `max_enodes = 8,000–16,000` with strict wall-clock checks) over the normalization + OES stage:
  - **Every proved rewrite** (peephole, AC canonicalization, distribution/factoring, linear/polynomial normalization, OES semantic equivalence) **unions** the original and candidate e-classes instead of overwriting the AST, recording the exact justification edge directly into the proof graph.
  - **Non-monotonic intermediate forms** (like expanding `x ^ y` or distributing a product) coexist safely alongside the original form — if they don't lead to cancellation, extraction simply ignores them at zero regression risk.
  - **Bottom-up DP extraction** selects the globally minimum-cost expression under the configured cost model (`legacy`, `paper_ast`, `instruction`, `readability`) across the entire e-graph, and emits ONLY the proof edges on the spanning tree connecting `input` to the extracted `output` (keeping certificates tiny and fast to replay).
- **Immediate payoff:** AC normalization, factor grouping, and OES multi-representative classes can all be enabled *together* without causing the 249-vs-254 / 217-vs-218 regressions documented in `docs/IMPLEMENTATION_RESULTS.md`.

---

## 5. Recommended Execution Order

1. **Implement `"ring_mod2w"` in `Rewrite_proof` + randomized Bitwuzla cross-tests** (unlocks everything downstream; replaces 50-edge micro-step chains with 1-edge sub-millisecond proofs).
2. **Wire disjoint-minterm + `"ring_mod2w"` certification into `linear_candidates`** (and fix `mba_oracle` `allow_oracle` propagation + maximal-subtree targeting), then re-audit `PLDI Non-Poly` (target: `19.25x -> ~1.1x`).
3. **Implement native multiplicative factor grouping + sparse polynomial normalization + Rivest/Hensel permutation-polynomial inversion**, then re-audit `MBA-Obfuscator nonlinear` (target: `11.47x -> ~1.1x`) and `poly_mba_cancel` / `perm_poly_quad`.
4. **Build the bounded e-graph unifying normalization + OES + global extraction**, and verify C-Full (1,000/1,000 proved, strict reductions >= 984 with zero AC/portfolio regressions) and all 4 smoke datasets.
5. **Expand benchmarks** to `Loki`, `Full-Loki`, `OMVLL`, `Tigress 6–8`, and `C-BeyondMBA`, then finish remaining polish items (Milestone 2 config centralization, Milestone 7 adaptive CHS scheduling, Milestone 9 select/min/max idioms).
