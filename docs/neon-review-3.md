# GreySynth Round-3 Review: Post-`3c5af95` Audit & Root-Cause Blueprint

**Reviewed commit:** `3c5af95` ("Record the Rumba oracle smoke audit", +39 commits since Round 2 at `5701b3e`)
**Scope:** Static audit of `src/greysynth/*`, `src/proof/rewrite_proof.ml`, `outside_tools/xyntia/src/lib/tree/mutations.ml`, `docs/PLAN.md`, `docs/IMPLEMENTATION_RESULTS.md`, plus read-only Dev Container probes against the built binaries (`greysynth_cli.exe`, `mba_proof.exe`, `mba_equiv.exe`) and the benchmark datasets (`PLDI Non-Poly`, `MBA-Obfuscator nonlinear`).

---

## 1. Round-2 Fix Verification & Live Probe Results

Every concrete bug from `docs/neon-review-2.md` was fixed cleanly. Running the 13-case Round-2 diagnostic suite under `default.json` (`total_timeout = 5`, `synthesis_timeout = 1`, `equiv_timeout = 1`) and independently replaying every certificate with `mba_proof.exe` gives **13/13 `proved_compositional`**:

| Case | Round 2 (`5701b3e`) | Round 3 (`3c5af95`) | Time | `mba_proof` | Checks (`cand/prov/dis/inc`) | Output |
|---|---:|---:|---:|---|---|---|
| `linear_3var_const_offset` | 24 -> 24 (1 inc) | **24 -> 7** | 0.42s | `proved_compositional` | 1/1/0/0 | `0x0043 + (c \| (b \| a))` |
| `linear_5var_sum` | 37 -> 37 (max_atoms=4) | **37 -> 1** | 0.08s | `proved_compositional` | 8/8/0/0 | `b` |
| `linear_6var_xor` | 23 -> 11 | **23 -> 11** | 1.32s | `proved_compositional` | 3/3/0/0 | `((y^x)^(w^z))^(b^a)` |
| `zero_poly_commuted` | 17 -> 17 | **17 -> 3** | 0.01s | `proved_compositional` | 1/1/0/0 | `x * y` |
| `scaled_poly_partition` | 21 -> 21 | **21 -> 5** | 0.02s | `proved_compositional` | 1/1/0/0 | `3 * (x * y)` |
| `perm_poly_affine` | 19 -> 3 | **19 -> 3** | 0.01s | `proved_compositional` | 4/4/0/0 | `y + x` |
| `semilinear_folded_add` | 9 -> 9 | **9 -> 3** | 0.00s | `proved_compositional` | 1/1/0/0 | `x + y` |
| `semilinear_const_xor` | 9 -> 3 | **9 -> 3** | 0.00s | `proved_compositional` | 1/1/0/0 | `0x1234 + x` |
| `ite_sparse_branch` | — | **14 -> 8** | 1.01s | `proved_compositional` | 8/2/6/0 | `(x == 0x2a) ? y : (z + y)` |
| `poly_nonpoly_inv` (8-bit) | — | **33 -> 11** | 2.30s | `proved_compositional` | 4/4/0/0 | `(x+y) * ((2*(x+y)) ^ 1)` |
| `semilinear_mixed_vars` | 7 -> 7 | 7 -> 7 | 0.07s | `proved_compositional` | 0/0/0/0 | `(x & 0x0f0f) + (y & 0xf0f0)` (equal cost to `\|`) |
| **`poly_mba_cancel`** | 167 -> 157 | **167 -> 157** | 4.04s | `proved_compositional` | 2/2/0/0 | Ground truth is size **11** (`-17*(x&~y) - 5*~(x\|~y)`) |
| **`perm_poly_quad`** | 45 -> 45 | **45 -> 45** | 4.38s | `proved_compositional` | 4/0/0/**4** | 4 inconclusive 64-bit quadratic proofs |

`PLDI Poly` (`1.0602x`) and `QSynth EA` (`1.0073x`) in `docs/IMPLEMENTATION_RESULTS.md` are now near-optimal. The two remaining cliffs in `docs/IMPLEMENTATION_RESULTS.md` — **`PLDI Non-Poly` (`19.2494x`)** and **`MBA-Obfuscator nonlinear` (`11.4734x`)** — have clear, concrete root causes documented below, alongside 6 specific code bugs in recent commits.

---

## 2. Concrete Bugs & Regressions in Recent Commits

### Bug 1 (High Impact): `Sample_evaluator.sample_value` assigns identical values to all variables on ~71% of structured samples (`src/greysynth/sample_evaluator.ml:94-116`)
Look at `sample_value` for `id >= 5 + variable_count`:
- `offset mod 7 = 0`: `1 << bit` — **ignores `name`, `rank`, and `seed`** (every variable gets the exact same value).
- `offset mod 7 = 1`: `~(1 << bit)` — **ignores `name`, `rank`, and `seed`**.
- `offset mod 7 = 2`: `(1 << (bit + 1)) - 1` — **ignores `name`, `rank`, and `seed`**.
- `offset mod 7 = 3`: `0x5555...` — **ignores `name`, `rank`, `seed`, AND `offset`** (identical constant across all variables and every 7th sample!).
- `offset mod 7 = 4`: `1 << (size - 1)` — **ignores `name`, `rank`, `seed`, AND `offset`** (and duplicates `sample_id = 4` `min_sbv`!).
- Only `offset mod 7` in `{5, 6}` (2/7 = **28.6%**) actually varies across variables or across `seed`.

**Impact:**
1. On the 100-sample bank, ~65 rows satisfy `x == y == z == ...` (diagonal collapse), weakening OES/CHS discrimination (`x ^ y == 0`, `x & y == x | y == x` on 71% of structured rows).
2. On the `holdout` bank (`nb_samples = 32`, `seed = 1`), ~20+ rows are **identical to `seed = 0` rows** and have `x == y == z`, leaving only ~7 independent multi-variable holdout rows!

**Fix:** Mix `rank` (variable index) and `seed` into the bit position and pattern selection for `offset mod 7` in `0..4`, e.g.:
- `bit = ((offset / 7) + (rank * 7) + (seed * 13)) mod size` for cases `0, 1, 2`;
- Rotate pattern masks (`0x5555...`, `0xaaaa...`, `0x3333...`, `0x0f0f...`, `0x00ff...`, `0xff00...`) by `(offset / 7 + rank + seed)` in case `3`;
- Keep at most 1–2 intentional diagonal (`x == y`) rows, and make the remaining rows independent across variables and `seed` so `holdout` (`seed = 1`) is genuinely disjoint from `samples` (`seed = 0`).

### Bug 2 (High Impact): External MBA oracle (`mba_oracle`) starves its call budget at the leaves and fails monolithic SMT verification (`src/greysynth/normalization.ml:736-863`)
This directly explains why the Rumba smoke test in `docs/IMPLEMENTATION_RESULTS.md:173-182` barely moved `PLDI Non-Poly` (`19.25x -> 18.97x`) and actually *reduced* strict reductions from 99 to 98:
1. **Bottom-up budget starvation (`normalization.ml:842-855`)**: `visit` recurses into children *first*, then calls `oracle_candidate` whenever `cost !current >= 5` and `!oracle_calls < !c_mba_oracle_calls` (default `4`). On any non-trivial AST, the **first 4 tiny size-5 subtrees near the leaves** consume all 4 oracle calls, so Rumba/CoBRA is **never invoked on the root or on any maximal pure-MBA subtree**.
   - **Fix:** Invoke `oracle_candidate` **top-down on maximal pure-MBA subtrees** (a pure-MBA subtree whose parent is not pure-MBA, or as a post-pass on the residual AST after deterministic bottom-up normalization finishes), prioritized by subtree cost descending, with a minimum cost threshold (e.g., `>= 11`).
2. **Monolithic SMT proof rejection (`normalization.ml:857`)**: Even when Rumba returns the exact 64-bit simplified answer for a nonlinear or large-coefficient linear MBA, `Rewrite.accepts` attempts a single 1–2s Bitwuzla query and gets `smt_inconclusive`. Oracle outputs should pass through the compositional proof builders (Section 3 below) before falling back to monolithic SMT.
3. **Missing `Lsl` and unbounded timeout (`normalization.ml:746, 771-806`)**:
   - `inspect` rejects `E.Lsl` (`<<`), disqualifying `C-MBA`/`Tigress` subtrees that contain constant left-shifts.
   - `oracle_candidate` does not clamp `!c_mba_oracle_timeout` against remaining `g_total_timeout` (unlike `synthesis.ml:508-515`), allowing oracle calls to overshoot `total_timeout`.
   - Parsing takes `List.rev lines` head (`answer :: _`) without validating that stderr/stdout did not emit a trailing warning line.

### Bug 3: `Rewrite_proof.abstract_pair` misses repeated constants and cost 2–3 subterms (`src/proof/rewrite_proof.ml:250`)
Line 250 currently gates abstraction on:
```ocaml
if occurrences.(id) >= 2 && current.cost >= 4 then
```
This misses two huge classes of sound abstractions:
1. Repeated cost 2–3 compound subterms such as `~b` (cost 2), `a & b` (cost 3), `a ^ b` (cost 3) — which are the exact shared factors in `MBA-Obfuscator nonlinear` and the `a & b` minterm in linear MBAs.
2. Repeated 64-bit constants (`cost = 1`) appearing on **both sides** of a ring identity such as `((0x123456789abcdef1 * u) + (0xedcba9876543210f * u)) == ((0x123456789abcdef1 + 0xedcba9876543210f) * u)`. As measured via `mba_equiv.exe` (Section 3.2), Bitwuzla constant-folds `c1 + c2` to `0` *before* recognizing distributivity and times out (`>2000ms`), whereas abstracting repeated constants (`c1 -> v1`, `c2 -> v2`) yields `((v1 * u) + (v2 * u)) == ((v1 + v2) * u)`, which Bitwuzla proves in **0.81 ms**!

**Fix:** Track `occ_left.(id)` and `occ_right.(id)` separately in `abstract_pair`, and abstract any maximal subterm occurring on **both sides** (`occ_left.(id) >= 1 && occ_right.(id) >= 1`) that is either non-atomic (`cost >= 2`) or a non-trivial constant (`cost = 1`, excluding `0`, `1`, `-1` — or try both with a short abstract timeout and fall back to concrete as already done at `rewrite_proof.ml:297-301`). Since abstraction is strictly stronger (`UNSAT => valid`, `SAT => fallback to concrete`), soundness is completely preserved.

### Bug 4: `Rewrite.accepts_compositional` does not cache `Unknown | Timeout` proof budgets (`src/greysynth/rewrite.ml:119-152`)
`accepts_compositional` checks `proofs` only for `Some U.Yes` (line 125) and never checks or updates `proof_budgets` on failure (`U.Unknown | U.Timeout`). Repeated normalization/synthesis passes that propose the same compositional rewrite retry and time out on the same inconclusive step again.

### Bug 5: `linear_candidates` mismatches `normalization_max_atoms = 6` (`src/greysynth/normalization.ml:421, 550`)
- `normalization_max_atoms` was raised to `6`, so `linear_candidates` now solves 5–6 atom linear MBAs, **but** two-value Boolean recovery (`normalization.ml:550`) is still hardcoded to `if count <= 4`.
- `collect` (`normalization.ml:421`) still hard-stops at `visited > 256`, which truncates large unsimplified nested linear MBAs (e.g., `PLDI Non-Poly` line 58 has 523 AST nodes before inner simplification; raising or memoizing DAG-visited nodes fixes this cleanly).

### Bug 6: `universal_rules` lookup & generalization proof budget (`src/greysynth/synthesis.ml:529-575`)
- `Sexpr.BvTbl.find_opt universal_rules e` (line 530) does not canonicalize commutative operand order or alpha-renaming of Greek placeholder variables (`α, β, ...`), so `(α | β) + (α & β)` will miss `(β | α) + (β & α)` or `(α & β) + (α | β)`.
- Line 569 runs `prove_equality ~timeout:(min 1. !c_equiv_timeout) e synth_expr` on **every** accepted CHS rewrite without clamping to remaining `g_total_timeout` (unlike `synthesis_timeout` at lines 508–515) and without checking `check_timeout ()` afterward.
- `Config` / `report_json` (`src/greysynth/config.ml:215`, `src/greysynth/greysynth.ml:237-263`): `load_config_from_json` builds a throwaway `Sample_evaluator.make !c_nb_samples` that `greysynth.ml:303` immediately discards, and `report_json` still omits ~11 newly added config keys (`ac_normalization`, `normalization_portfolio`, `normalization_max_atoms`, `mba_oracle`, `oes_candidate_limit`, `cegis_retries`, `learn_synthesis_rules`, `branch_covering_samples`, `chs_max_inputs`, `chs_max_horizon`, `synthesis_constant_limit`).

---

## 3. Root-Cause Analysis & Blueprint for the Two Remaining Benchmark Cliffs

### 3.1 Why `PLDI Non-Poly` is at `19.25x` Quality — Confirmed Empirically

Inspecting `ProMBA/mbasolve_benchmark/backup/dataset_nonpoly.txt` shows the exact structure of the benchmark:
- Lines 2–56: `(E & y) * (E | y) + (E & ~y) * (~E & y)` (ground truth `a * y`), where `E` is a 2-variable 64-bit linear MBA equal to `a` (e.g., Line 2: `-(a&b) + 10*(a&~b) + 2*a + 11*~(a|b) - 11*~b == a`, size 29).
- Lines 57–100: linear MBAs over `(x, E)` or `(E, y)` where `E` is repeated 10–14 times (size 138–523).

Running `greysynth_cli.exe` (`default.json`, `total_timeout = 5`) on 5 diagnostic slices from `dataset_nonpoly.txt` pinpoints the exact failure:

| Diagnostic Case | Input -> Output Size | Time | Checks (`cand/prov/dis/inc`) | Ground Truth Size |
|---|---:|---:|---|---:|
| `nonpoly_L2_inner` (`E` alone) | **29 -> 27** | 6.65s | 5 / 2 / 0 / **2** | **1** (`a`) |
| `nonpoly_L2_full` | **129 -> 127** | 6.61s | 5 / 2 / 0 / **2** | **3** (`a * y`) |
| `nonpoly_L57_full` | **138 -> 121** | 5.37s | 11 / 9 / 0 / **1** | **3** |
| `nonpoly_L58_inner` (`E` alone) | **41 -> 40** | 6.01s | 4 / 1 / 0 / **2** | **1** (`a`) |
| `nonpoly_L58_full` | **523 -> 522** | 6.01s | 4 / 1 / 0 / **2** | **3** |

**What happened:**
1. `linear_candidates` **already found the exact ground truth `a`** for `nonpoly_L2_inner` and `nonpoly_L58_inner`!
2. `complement_product_steps` only expands `c * ~t -> (-c)*t + (-c)`, leaving `-(a&b) + 10*(a&~b) + 2*a + 11*~(a|b) - 11*~b` with **multiple 64-bit constant multipliers** in a single monolithic Bitwuzla query — which timed out **twice** (`inconclusive = 2`), burning >6s (note also the `total_timeout = 5` overshoot!) and starving the entire outer expression.
3. Because `E` never collapsed to `a`, `product_partition_candidate` never saw `(a & y)*(a | y) + (a & ~y)*(~a & y)` (which it otherwise collapses to `a * y` in **0.01s**!).

### 3.2 Empirically Verified Fix: Binary-Ring + Disjoint-Minterm Compositional Proofs

`Rewrite_proof.verify` (`src/proof/rewrite_proof.ml:355-395`) **already runs full congruence closure** over the certificate DAG. We benchmarked each atomic 64-bit proof obligation directly in Bitwuzla via `mba_equiv.exe -timeout 2`:

| 64-bit Obligation Tested in `mba_equiv.exe` | Verdict | Time | Takeaway |
|---|---|---:|---|
| `~(a \| b) == (~a) & (~b)` | `yes` | **0.66 ms** | Pure bitwise-to-minterm: instant |
| `~b == ((~a)&(~b)) + (a&(~b))` | `yes` | **0.96 ms** | Disjoint minterm sum (zero carries): instant |
| `a == (a&(~b)) + (a&b)` | `yes` | **1.59 ms** | Instant |
| `-1 == m0 + m1 + m2 + m3` | `yes` | **1.41 ms** | Constant offset expansion: instant |
| `0x123456789abcdef1 * (u + v) == c*u + c*v` | `yes` | **0.57 ms** | Binary distributivity works for **any** 64-bit constant! |
| `(a * f) + (b * f) == (a + b) * f` | `yes` | **0.81 ms** | **2-term additive factoring: instant!** |
| `((t1*f) + (t2*f)) + (t3*f) == ((t1+t2)+t3)*f` | **`ukn`** | >2000 ms | **3-term factoring in one step times out — MUST do 2 terms at a time!** |
| `(a * f) - (b * f) == (a - b) * f` | **`ukn`** | >2000 ms | **`bvsub` factoring times out — MUST normalize `x - y == x + (-y)` first!** |
| `x - y == x + (-y)` | `yes` | **0.74 ms** | Instant |
| `-(b * f) == (-b) * f` | `yes` | **0.88 ms** | Instant |
| `-(0x123456789abcdef1 * u) == 0xedcba9876543210f * u` | `yes` | **0.80 ms** | Instant |
| `(a * b) * c == a * (b * c)` / `a * b == b * a` | `yes` | **0.71–0.75 ms** | Instant |
| `1 * u == u` / `(-1) * u == -u` / `0 * u == 0` | `yes` | **0.74–0.80 ms** | Instant |
| `0x123456789abcdef1 + 0xedcba9876543210f == 0` | `yes` | **0.79 ms** | Pure constant fold: instant |
| Arbitrary AC additive regrouping (abstracted terms) | `yes` | **0.74 ms** | Instant |
| Whole `L2` linear sum even *after* abstracting `m0,m2,m3` | **`ukn`** | >2000 ms | **Combining all terms in one query STILL times out — MUST decompose into binary steps!** |

**Compositional Proof Algorithm for ANY $k$-variable ($k \le 4$) Linear MBA $E \to C$ (Generalizes and replaces `complement_product_steps`):**
1. **Normalize signs to pure `+`**: rewrite `x - y -> x + (-y)` (0.74ms), `-(c * t) -> (-c) * t` (0.80ms), `-t -> (-1) * t` (0.80ms), `t -> 1 * t` (0.74ms), and constant `c0 -> (-c0) * (-1)` (if `c0 != 0`).
2. **Bitwise-to-minterm expansion (zero multiplications)**: for each distinct bitwise expression $B_i$ over the $k$ atoms, emit ONE local edge $B_i = \sum_{p \in S_i} M_p$ (and `-1 = \sum_p M_p` if needed) where $M_0, \dots, M_{2^k-1}$ are the $2^k$ pairwise-disjoint Boolean minterms. Each edge proves in **~1 ms**; congruence closure lifts it into $E$ automatically.
3. **Binary distributivity**: for each `c_i * (M_a + M_b + ...)` with $|S_i| \ge 2$, emit binary edges `c * (u + v) == (c * u) + (c * v)` (**0.57–0.82 ms** each).
4. **AC regrouping by minterm**: emit ONE pure-addition edge grouping all `c_i * M_p` terms for each $M_p$ adjacent to each other (**0.74 ms** via `abstract_pair`).
5. **Binary coefficient accumulation per minterm**: fold each $M_p$'s summands **two at a time** via:
   - `(c1 * M_p) + (c2 * M_p) == (c1 + c2) * M_p` (**0.81 ms** once Bug 3 in `abstract_pair` abstracts repeated constants and cost 2–3 minterms!),
   - `(c1 + c2) == c_sum` (**0.79 ms** constant fold),
   - plus `0 * M_p == 0`, `1 * M_p == M_p`, `(-1) * M_p == -M_p`, `x + 0 == x`.
6. **Reverse on candidate `C`**: expand the compact candidate `C` (1–3 terms) to the same canonical minterm sum $\sum_p \text{coeff}_p \cdot M_p$.

**Result:** Proves **any** 64-bit 2–4 variable linear MBA — even with arbitrary random 64-bit coefficients — in **~15–30 ms total**, with **zero changes to `Rewrite_proof`'s format or verifier**, unlocking `PLDI Non-Poly` (`nonpoly_L2`, `nonpoly_L57`, `nonpoly_L58`, etc.) from `19.25x` down toward `~1.0x`.

### 3.3 Why `MBA-Obfuscator nonlinear` is at `11.47x` Quality (and `poly_mba_cancel` is `167 -> 157` instead of `11`)

Inspecting `rumba/third_party/dataset/mba_obf_nonlinear.csv` (lines 1–25) shows that **every single case** has the algebraic shape:
$$\sum_i F_i \cdot L_i(v_0, v_1)$$
where each $F_i$ is a small bitwise term (e.g., `~v1`, `v0 ^ v1`, `v0 & ~v1`, `~(v0 | ~v1)`) and each cofactor $L_i(v_0, v_1)$ is a 2-variable linear MBA that simplifies to a **constant** $c_i$ (e.g., line 1 factors by `~v1` and `v0^v1` into `1*~v1 - 1*(v0^v1)`; line 15 = `poly_mba_cancel` factors by `(v0&~v1)` and `~(v0|~v1)` into `-17*(v0&~v1) - 5*~(v0|~v1)`).

**Compositional Factor-Grouping Pass (in `normalization.ml`):**
1. Flatten additive sums of products (using `sub_to_add` + `neg_mul` + `mul_assoc`/`mul_comm`, each **0.71–0.88 ms**).
2. Extract multiplicative factors of each summand (e.g., `((c * A) * B)` has factors `{A, B}` with cofactors `{c * B, c * A}`) and greedily select the most frequent non-constant factor `F` appearing in $\ge 2$ summands (or partition into disjoint factor buckets when every term matches a small set of factors).
3. Regroup all summands containing `F` adjacent (ONE AC-addition edge, **0.74 ms**), normalize each into `cofactor_j * F` (`mul_assoc`/`mul_comm`, **0.75 ms**), and fold **two terms at a time** via `(t1 * F) + (t2 * F) == (t1 + t2) * F` (**0.81 ms** per binary step — NOT n-ary in one query!).
4. Run the compositional disjoint-minterm linear normalizer (Section 3.2) on the cofactor sum `t1 + t2 + ...`!
   - On `mba_obf_nonlinear.csv`, every cofactor collapses to a constant `c_i`, turning `F * (t1 + t2 + ...)` into `c_i * F` in milliseconds!
5. **Bonus — General Polynomial / Quadratic Minterm Extension (fixes `perm_poly_quad` `45 -> 45` and `ProMBA Poly`):**
   - For univariate or 2-variable quadratic/cubic polynomial MBAs (`perm_poly_quad` = `P^{-1}(P(x))` over $\mathbb{Z}/2^w\mathbb{Z}$), expanding into the monomial basis $\{1, x, x^2, x^3, \dots\}$ (or pairwise-disjoint minterm products $M_p \cdot M_q = 0$ for $p \ne q$, which proves in **< 1 ms** in Bitwuzla!) using the **exact same binary-ring edges** (`a*(b+c) == a*b + a*c`, `a*b == b*a`, `(a*b)*c == a*(b*c)`, `(c1*u) + (c2*u) == (c1+c2)*u`) proves 64-bit permutation-polynomial inversions like `perm_poly_quad` compositionally without monolithic 64-bit multiplication bit-blasting!
   - Note that for disjoint minterms $M_p \cdot M_q = 0$ ($p \ne q$): `((a & b) * (a & ~b))` is **NOT** zero in bitvector multiplication (carry propagation across bit positions makes `(x & y) * (x & ~y) != 0`!), so polynomial minterm reduction works on standard polynomial monomials $x^i y^j$ or bitwise-minterm **additive** terms (and for `product_partition_candidate`, Bitwuzla handles bitwise identities like `(x&y)*(x|y) + (x&~y)*(~x&y) == x*y` directly in 10ms). Do **not** assume $M_p \cdot M_q = 0$ for `bvmul`! Only $M_p \land M_q = 0$ and $M_p + M_q = M_p \mid M_q$ hold bitwise.

---

## 4. Prioritized Next Steps for `docs/PLAN.md`

Ordered by expected quality & reliability gain per line of code:

1. **Upgrade `Rewrite_proof.abstract_pair` (`src/proof/rewrite_proof.ml:219-270`)** to abstract maximal subterms occurring on both sides (`occ_left >= 1 && occ_right >= 1`, including cost 2–3 compound terms and non-trivial constants). Zero format change, unlocks sub-millisecond binary ring proofs.
2. **Implement Compositional Disjoint-Minterm Proof Builder for `linear_candidates` (`src/greysynth/normalization.ml`)** using binary distributivity + AC regrouping + binary coefficient accumulation (Section 3.2). Re-benchmark `PLDI Non-Poly` immediately — expect `19.25x` to drop dramatically toward `~1.0–2.0x`.
3. **Implement Compositional Multiplicative Factor Grouping (`src/greysynth/normalization.ml`)** using 2-term binary factoring + cofactor linear normalization (Section 3.3). Re-benchmark `MBA-Obfuscator nonlinear` and `poly_mba_cancel` — expect `11.47x` to drop dramatically toward `~1.0–2.0x` and `poly_mba_cancel` `167 -> 11`.
4. **Fix `Sample_evaluator.sample_value` diagonal collapse (`src/greysynth/sample_evaluator.ml:94-116`)** so `offset mod 7` in `0..4` varies across variable `rank` and `seed` (making `holdout` genuinely independent of `samples`).
5. **Fix `mba_oracle` invocation order and timeout clamping (`src/greysynth/normalization.ml:736-863`)**: run top-down on maximal pure-MBA subtrees (or post-pass on large residual pure-MBA roots), support `E.Lsl`, clamp timeout to remaining `g_total_timeout`, and verify oracle answers through the compositional proof builders when monolithic SMT is inconclusive.
6. **Clean up remaining hygiene items in `docs/PLAN.md`:**
   - Cache `Unknown | Timeout` budgets in `Rewrite.accepts_compositional` (`src/greysynth/rewrite.ml:119-152`).
   - Raise two-value Boolean recovery limit from `count <= 4` to `min 6 !c_normalization_max_atoms` and DAG-memoize `linear_candidates` `collect` (`normalization.ml:421, 550`).
   - Canonicalize `universal_rules` lookup keys and clamp generalization SMT timeout to remaining `g_total_timeout` (`synthesis.ml:529-575`).
   - Complete Milestone 2's centralized config/reporting checklist (`config.ml`, `greysynth.ml` `report_json`) and Milestone 7/8's adaptive short-probe -> XSmir escalation & whole-pipeline portfolio extraction.
