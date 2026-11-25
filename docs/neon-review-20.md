# GreySynth Round-20 Spec: Variable-Scalable Linear/Boolean MBA Engine & Decidable `linear_mba_mod2w` Proof Rule

**Baseline commit:** `a3e8dc9` (Round 19 `poly_mod2w` complete — `Univariate64` `1,000/1,000` at `1.0000x`, `Multivariate64` `1,000/1,000` at `1.0000x`!)  
**Target:** Crush the **6,600+ weak linear/Boolean MBA cases** exposed in Wave 1 & Wave 2:
- **SiMBA `e1..e5` (3/4/5 vars):** **5,139 weak cases** (`e1_5vars` `0/1,000` at `936.18x`; `e2_4vars` `14/1,000` at `320.27x`; `e3_4vars` `7/1,000` at `70.04x`; `e4_4vars` `7/1,000` at `50.15x`; `e1_4vars` `529/1,000` at `9.53x`; `e5_4vars` `534/1,000` at `8.09x`; plus 230 weak 3-var cases).
- **Neureduce:** **1,360 weak cases** (e.g., `line_0000007` and `line_0000010`: sums of disjoint-variable linear MBA components like `{v0, v1, v2} + {v3, v4}`, currently blocked by variable-count caps and the `cost >= 300` gate on grouped Boolean reconstruction).
- **CoBRA `mba_flatten.txt`** (`95` weak cases) & residual **`permutation64.txt`** (`10` weak cases where opaque-atom linear/Boolean cleanup applies after `poly_mod2w`).

While keeping **100% fail-closed soundness** and **sub-millisecond independent replay** in `mba_proof`.

---

## 1. Decidable `linear_mba_mod2w` Proof Kernel Rule (`src/proof/rewrite_proof.ml`, `src/proof/rewrite_proof.mli`)

Currently, linear MBA rewrites are proved via `minterm_ring_proof`, which breaks them into up to $2^k$ Bitwuzla SMT edges plus a `ring_mod2w` edge. At $k = 4$ or $k = 5$ on 64-bit widths, those SMT obligations routinely time out (spending ~1,200s per 1,000-case SiMBA suite and failing to certify valid simplifications!).

**Exact mathematical theorem (Linear MBA Canonical Form over $\mathbb{Z}/2^w\mathbb{Z}$):**
Let $a_0, \dots, a_{k-1}$ be $k \le 8$ opaque interned terms of width $w \le 128$, and for each assignment $b \in \{0, \dots, 2^k - 1\}$ let $M_b = \bigwedge_{i: b_i = 1} a_i \land \bigwedge_{i: b_i = 0} \neg a_i$ be the $b$-th bitwise minterm.
Because the $2^k$ minterms are pairwise bitwise disjoint and sum to all-ones ($\sum_{b=0}^{2^k - 1} M_b = -1 \pmod{2^w}$):
1. Every linear MBA expression $E$ over $a_0, \dots, a_{k-1}$ evaluates identically to a unique linear combination $(c, t) \in (\mathbb{Z}/2^w\mathbb{Z}) \times (\mathbb{Z}/2^w\mathbb{Z})^{2^k}$ representing $E \equiv c + \sum_{b=0}^{2^k-1} t[b] \cdot M_b \pmod{2^w}$:
   - **Linear arithmetic layer** (`parse_linear`):
     - `const v` $\mapsto (v \bmod 2^w, \vec{0})$
     - `bvadd x y` $\mapsto (c_x + c_y, t_x + t_y) \pmod{2^w}$
     - `bvsub x y` $\mapsto (c_x - c_y, t_x - t_y) \pmod{2^w}$
     - `bvneg x` $\mapsto (-c_x, -t_x) \pmod{2^w}$
     - `bvnot x` $\mapsto (-1 - c_x, -t_x) \pmod{2^w}$ *(valid universally in two's complement: $\neg E \equiv -1 - E \pmod{2^w}$, and agrees identically with bitwise `bvnot`!)*
     - `bvmul (const k) y` or `bvmul x (const k)` $\mapsto (k \cdot c, k \cdot t) \pmod{2^w}$
     - `bvshl x (const s)` $\mapsto$ if $s \ge w$ then $(0, \vec{0})$ else $(2^s \cdot c_x, 2^s \cdot t_x) \pmod{2^w}$
     - `bvand`, `bvor`, `bvxor` $\mapsto (0, \text{indicator}(\text{parse\_bitwise } e))$
     - Any other node (variables, nonlinear `bvmul`, shifts by non-constant, `ite`, etc.) $\mapsto$ intern node ID as opaque atom $i$, return $(0, b \mapsto [b_i = 1])$.
   - **Pure bitwise layer** (`parse_bitwise`, returns `bool array` of length $2^k$):
     - `const 0` $\mapsto$ all `false`
     - `const (2^w - 1)` (all-ones ONLY!) $\mapsto$ all `true`
     - `bvnot x` $\mapsto$ pointwise `not (parse_bitwise x)`
     - `bvand x y` / `bvor x y` / `bvxor x y` $\mapsto$ pointwise `&&` / `||` / `<>`
     - **CRITICAL SOUNDNESS RULE:** Any other node — specifically including **any non-uniform constant** (neither `0` nor `2^w - 1`, such as `0x5` or `1`) as well as any arithmetic node (`bvadd`, `bvmul`, etc.) inside a bitwise op — MUST be interned as an **opaque atom** $i$ (`b -> (b lsr i) land 1 <> 0`)! Never assume a non-uniform constant has uniform bit slices!
2. **Exact canonicalization** using $M_0 = -1 - \sum_{b=1}^{2^k - 1} M_b \pmod{2^w}$:
   $$c' = (c - t[0]) \bmod 2^w, \qquad t'[0] = 0, \qquad t'[b] = (t[b] - t[0]) \bmod 2^w \quad (1 \le b < 2^k).$$
3. **Soundness:** If $c'(L) = c'(R)$ and $t'(L)[b] = t'(R)[b]$ for all $1 \le b < 2^k$, then $L \equiv R \pmod{2^w}$ holds identically for **all** bitvector values of the opaque atoms (even when opaque atoms are correlated expressions like $x \cdot y$ or non-uniform constants!).

**Deliverables in `src/proof/rewrite_proof.ml` & `.mli`:**
1. Add equality rule `"rule": "linear_mba_mod2w"` (keeping full backward compatibility with v1 certificates) + `Rewrite_proof.record_linear_mba` + `linear_mba_proofs` metric field in `verify` JSON output.
2. Implement `linear_mba_equal g left right` with **DAG memoization by interned node ID** (crucial for 3,000+ node `e1_5vars` expressions!):
   - Strict replay caps: `max_atoms = 8`, `width <= 128`, `max_visited_nodes = 16_384`, `max_ops = 2_000_000`. Fail closed with `Ring_limit_exceeded` (or distinct `Linear_mba_limit_exceeded` / `Linear_mba_not_equal`) on cap breach or mismatch.
   - Pass 1 (memoized): collect distinct opaque atoms appearing in `left` and `right` (aborting immediately if count $> 8$ or visited unique nodes $> 16\_384$).
   - Pass 2 (memoized): evaluate `(c, t)` for `left` and `right` (for $k$ atoms, array size $2^k \le 256$), canonicalize both, and check exact equality.
3. **Positive & Negative Soundness Cross-Tests in `test/proof_test.ml`:**
   - Positive tests: 4-var and 5-var SiMBA identities, 8-var identity, correlated opaque atom identities like `(x*y & z) + (x*y | z) == (x*y) + z`, `~(a + b) == -1 - a - b`, `(x & 5) + (x | 5) == x + 5` (wait: verify `(x & 5) + (x | 5) == x + 5` — note arithmetic `5` vs bitwise opaque atom `5` is conservative unless `5` is opaque in both or kept sound; test `~((a & 5) ^ b)` identities AND verify NO false positive on `(x & 5) == x` or `(x & 1) + (x & 1) == 2*x`!).
   - **Negative soundness tests (MANDATORY, cross-checked with Bitwuzla on 8-bit & 16-bit!):**
     - Mutating any single minterm coefficient by $\pm 1$ is rejected (`not_equal`) AND refuted by Bitwuzla.
     - Non-uniform constant trap: `(x & 5) == x`, `(x | 5) == -1`, `(x & 1) + (~x & 1) == -1` MUST be **REJECTED** by `linear_mba_mod2w` (and refuted by Bitwuzla)!
     - Arithmetic-under-bitwise trap: `((x + y) & z) == (x & z) + (y & z)` MUST be **REJECTED**!

---

## 2. Variable-Scalable Linear/Boolean MBA Solver (`src/greysynth/normalization.ml`, `rewrite.ml`, `egraph.ml`, `greysynth.ml`)

**Deliverables:**
1. **Wire `~linear_mba_equalities` through `Rewrite.accepts_compositional` and `Egraph` proof records**, recording edges via `Rewrite_proof.record_linear_mba` (instant, zero Bitwuzla SMT timeout!).
   - Update `Normalization` callers of `linear_candidates` / `component_linear_candidates` (and `Egraph.optimize`) to certify linear MBA rewrites with ONE `linear_mba_mod2w` edge whenever `linear_mba_mod2w` applies (falling back to existing `minterm_ring_proof` / SMT only if outside `linear_mba_mod2w` caps!).
2. **Root Linear-MBA Fast Path BEFORE the `> 768` OES-First Threshold (`src/greysynth/greysynth.ml:221-246`):**
   - Currently `greysynth.ml:221` restricts root linear MBA to `size_of_expr !best >= 600 && List.length vars <= 3`.
   - Lift this cleanly: whenever `size_of_expr !best >= 20` (and before the `> 768` OES-first branch!), if `Normalization.linear_mba_compatible !best` (or after disjoint-variable component splitting), run the fast linear MBA solver (supporting up to `8` atoms — e.g. `min 8 (max 6 !c_normalization_max_atoms)` or raising default `c_normalization_max_atoms` / root linear atom cap to `8`!) and certify via a single `linear_mba_mod2w` edge!
   - Also check `linear_candidates`'s `visited` limit (`normalization.ml:945`): for a 3,088-node `e1_5vars` expression, use DAG memoization (keyed by `Nodes.t`) inside `linear_candidates` so 3,000–16,000 node expressions parse in < 2 ms without hitting `Too_complex`!
   - **Important:** For `e1_5vars` (~3,088 nodes, 5 vars) and `e2..e5_4vars` (~357 nodes, 4 vars), this single pass reduces them from 3,088 -> 3 (`v0 + v1`) or 357 -> 1 (`49374`) or 357 -> 5 (`49374 + 3735936685 * x`) in **milliseconds** before OES/e-graph/CHS even start!
3. **Disjoint-Variable Connected-Component Splitting (`src/greysynth/normalization.ml`):**
   - Many `neureduce` expressions (e.g., `line_0000007`: `-3*(~v0&(v1^v2)) + 2*(v0&(v1^v2)) + (v3|v4)`) are additive sums $T_1 + T_2 + \dots + T_m$ whose terms partition into **disjoint variable-connected components** (e.g., `{v0, v1, v2}` and `{v3, v4}`).
   - Add a helper `split_disjoint_additive_components` (union-find over variables appearing in each top-level additive term, keeping constant terms separate):
     - If there are $\ge 2$ non-trivial components (especially when total atoms $> 4$ or when each component has smaller support than the whole!), simplify each component independently with `linear_candidates` and recombine the simplified components + constant term!
     - Certify the whole expression $\to$ recombined simplified expression in **one** `linear_mba_mod2w` edge (if total atoms $\le 8$) or per-component `linear_mba_mod2w` + `ring_mod2w` edges (even when total variables $> 8$, e.g. 12 variables split into 3 components of 4 variables each!).
   - Also relax `component_linear_candidates` (`normalization.ml:1188`) which currently caps variables at `<= 2` and `cost <= 256` — raise to `<= 6` variables and `cost <= 1024`, certifying component rewrites with `linear_mba_mod2w`!
4. **Upgrade `linear_candidates` Reconstruction Quality (`src/greysynth/normalization.ml:935-1185`):**
   - **Support minimization (essential variables):** Before building Boolean/affine/Möbius reconstructions, identify which atoms $i \in \{0, \dots, k-1\}$ actually affect `target` (i.e., $\exists b$ such that `target.(b) <> target.(b lxor (1 lsl i))`). Project `atoms` and `target` down to the active support $k' \le k$!
     - Example: `e1_5vars` has 5 input variables, but `v0 + v1` only depends on 2! `e2_4vars` (`49374`) has support $k' = 0$ (immediate constant!)! `e3_4vars` (`49374 + 3735936685*x`) has support $k' = 1$! `e4_4vars` (`49374 + 3735936685*(x^y)`) has support $k' = 2$!
     - Dropping irrelevant atoms shrinks the truth table from $2^5 = 32$ to $2^0, 2^1, 2^2$ immediately, making every reconstruction instant and optimal!
   - **Pure-affine multi-variable check:** After Möbius inversion on the projected support (`coefficients`), if all `coefficients.(subset) = 0` for `popcount(subset) >= 2` (and also check complemented variables `~x_i = -1 - x_i` when that eliminates a constant offset!), directly construct the exact compact linear form $c_0 + \sum c_i x_i$.
   - **Remove the `cost >= 300` gate on equal-coefficient grouped Boolean reconstruction (`normalization.ml:1105`):**
     - For `neureduce` expressions (60–150 nodes), equal-coefficient grouping (grouping distinct non-zero values of `target`, or shifted by `target.(0)` / modal value $v^*$ so the most frequent truth-table value becomes the base constant $v^* + \sum_{v \neq v^*} (v - v^*) \cdot B_v$!) is the exact optimal representation!
     - Try BOTH base `0` AND the **most frequent value** $v^*$ in `target` as the constant shift (e.g., if 14/16 entries equal `c` and 2 equal `c + d`, shifting by `c` yields `c + d * B` instead of 2 Boolean functions!).
   - **Compact Boolean reconstruction in `boolean_candidates` for $k' \le 6$:**
     - Currently `boolean_candidates` only emits full $k'$-literal minterms (unminimized DNF), full $k'$-literal clauses (unminimized CNF), and raw ANF — which is huge when $k' = 3..6$!
     - Add **exact Quine-McCluskey prime-implicant reduction + greedy cover** (or recursive Shannon/cube merging for $k' \le 6$, which runs in microseconds since $2^6 = 64$!) for BOTH `truth` (compact DNF) and `not truth` (compact dual CNF / `~(compact DNF)`), plus check single-operator / two-level factored forms like `a & (b ^ c)` / `~a & (b ^ c)` (directly hitting `neureduce` patterns like `~v0 & (v1 ^ v2)`!).
     - Quick factored check for $k' = 3$: if fixing atom $i$ to 0 (or 1) makes `truth` identically `false`, then `truth = literal(i) & sub_truth(other 2 atoms)`, where the 2-atom subfunction has a 1-op exact lookup table (`a^b`, `a|b`, `a&b`, `~(a^b)`, etc.)! Similarly if fixing atom $i$ makes `truth` identically `true`, `truth = literal(i) | sub_truth`! And if `truth(i=0) = not truth(i=1)`, `truth = atom_i ^ sub_truth`! That 10-line cofactor decomposition (Shannon/Reed-Muller factoring for $k' \le 4$) recovers `~v0 & (v1 ^ v2)`, `v0 ^ (v1 | v2)`, etc. in O(1)!
5. **Check `permutation64.txt` residual rows (10 rows):**
   - Inspect why the remaining 10 rows of `datasets/cobra/permutation64.txt` didn't collapse in Round 19; if post-`poly_mod2w` linear MBA cleanup or `linear_mba_mod2w` solves them (or if they are degree-1/degree-2 Rivest inverse pairs), note whether Round 20 improves them (don't spend excessive time if they require a specialized permutation-polynomial inverter beyond linear MBA).

---

## 3. Focused Unit Tests & Verification Gate for Round 20

1. **Unit & soundness tests (`test/proof_test.ml`, `test/normalization_test.ml`):**
   - `linear_mba_mod2w` positive tests (4-var, 5-var, 8-var, correlated opaque atoms, `bvnot` arithmetic, `bvshl` by constant) AND mandatory negative Bitwuzla cross-tests (off-by-one coefficient, non-uniform constant mask `x & 5`, arithmetic under bitwise `(x + y) & z`).
   - Direct regression tests on actual rows from:
     - `datasets/external/simba/e1_5vars.txt` (row 1: 3,088 -> `<= 3`)
     - `datasets/external/simba/e2_4vars.txt`, `e3_4vars.txt`, `e4_4vars.txt`, `e5_4vars.txt` (row 1 each -> `<= GT`)
     - `datasets/external/neureduce/dataset.txt` (`line_0000007` and `line_0000010` -> `<= GT`)
     - Every regression test independently replayed through `mba_proof` with `"linear_mba_mod2w"` edges verified!
2. **Run `make test`** — 100% green.
3. **Targeted Audit Verification (zero `--limit`, `--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, keep container RAM well under 30 GB):**
   - All 6 major 4/5-var SiMBA suites (6,000 cases total — with `linear_mba_mod2w`, these should finish in just a few minutes total!):
     - `datasets/external/simba/e1_4vars.txt` (1,000)
     - `datasets/external/simba/e1_5vars.txt` (1,000)
     - `datasets/external/simba/e2_4vars.txt` (1,000)
     - `datasets/external/simba/e3_4vars.txt` (1,000)
     - `datasets/external/simba/e4_4vars.txt` (1,000)
     - `datasets/external/simba/e5_4vars.txt` (1,000)
   - Plus 3-var SiMBA sanity check (`e5_3vars.txt`, 1,000 cases — baseline 885/1,000 solved, 62 weak).
   - `datasets/cobra/mba_flatten.txt` (full, 95 weak baseline).
   - `datasets/external/neureduce/dataset.txt`: first `--limit 1000` (or full 10,000 if it runs under ~10 min — check wall time on first 1,000 first!).
   - `datasets/cobra/permutation64.txt` (13 cases).
   - Quick 5×100 MBA smoke regression check (`PLDI Non-Poly`, `MBA-Obfuscator nonlinear`, `PLDI Poly`, `QSynth EA`, `msimba`) — confirm **500/500 established, 0 refuted, zero quality regressions**.
4. Record concise Round-20 results (including before/after table and wall-time speedup!) in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `docs/FULL_AUDIT_REPORT.md`).
