# GreySynth Round-24 Spec: Quotient-Ring DAG `poly_mod2w`, `BitTrans`-to-`poly_mod2w` Hybrid Reduction, Centered Sparse Recovery & Newton Permutation Inversion

**Baseline:** Round 23 (`BitTrans` + `PolySim` + Complementary-Atom Pairing + RUMBA Thm 20 — crushed `c_mba_obfuscator` 152 weak → 125+ solved & `mba_obf_nonlinear` 255 weak → 149+ solved!)  
**Sources (from `docs/LITERATURE_ANALYSIS.md`):**
- Barthelemy, Eyrolles, Renault, Roblin (SPRO '16, `2995306.2995310.md`) — Binary Permutation Polynomial Inversion in $\mathbb{Z}_{2^w}[x]/I$
- Gàmez-Montolio, Florit, Brain, Howe (BAR '24, `bar2024-14-paper.md`) — Truncated-Row Stirling Normalization $F[\ell, d+1]$, Sparse Kronecker Multivariate Normalization, and Centered Sparse Representative Recovery (§VI)

**Primary targets:**
- **`datasets/hard_cases/all_failing/permutation64/`** (all **10 remaining unsolved rows** → target: **`10/10` SOLVED**, bringing full `Permutation64` to **`13/13` = `1.0000x` exact GT!**)
- **`datasets/hard_cases/all_failing/pldi_poly/`** (62 weak rows)
- **`datasets/hard_cases/core_hard/`** (413 hardest cases) & **`datasets/hard_cases/regression_smoke/`** (62 already-solved guards)

---

## 1. Exact Root Cause of All 10 Remaining `Permutation64` Cases (Verified Directly!)

Inspecting all 10 remaining `datasets/hard_cases/all_failing/permutation64/*.json` rows (`line_0000003`..`014`, sizes 245 to 11,169, GT `6*x + 6*y - 8*(x & y) + 3*(x * y)`):
- Every row is a degree 2–5 multivariate polynomial over **correlated 2-var Boolean atoms** (`x^y`, `x|y`, `x&~y`, `~x&y`, `x|~y`, `~x^y`, `~(x^~y)`, `x`, `y`) plus `x*y`.
- When every maximal pure-bitwise leaf is substituted via **`BitTrans`** into the canonical AND-conjunction basis `(x, y, z = x & y)`:
  - Every row becomes a compact degree $\le 10$ polynomial in **just 3 variables `(x, y, z)`**!
  - Its difference from GT `6*x + 6*y - 8*z + 3*x*y` **vanishes identically mod $2^{64}$ over completely independent `(x, y, z)`** (i.e., belongs to the multivariate null ideal $\mathcal{Z}^{64, 3}$)!
- **Why Round 19 & Round 23 missed them:**
  1. Round 19 ran `poly_mod2w` *before* `BitTrans`, treating `x^y`, `x|y`, `x&~y`, `~x&y` as unrelated opaque atoms.
  2. Round 23 ran `BitTrans` $\to$ `ring_mod2w`, NOT `BitTrans` $\to$ **`poly_mod2w`** (falling-factorial modular null-polynomial reduction!), and large `Permutation64` trees (`line_0000006`, `010`, `014`: 7,873–11,169 AST nodes) need DAG-evaluated quotient-ring reduction without blowing up flat monomial counts!

---

## 2. Quotient-Ring DAG `poly_mod2w` & Arbitrary-Degree Truncated-Row Normalization (`src/proof/rewrite_proof.ml`)

Currently `poly_equal` in `src/proof/rewrite_proof.ml` expands `left` and `right` as flat polynomials capped at `max_var_degree = 66` and `max_total_degree = 66`. Evaluating composed permutation polynomials like $Q(P(x))$ (raw degree up to $65^2 = 4,225$ at 64 bits!) or high-degree powers hits the flat degree cap.

**Exact mathematical upgrade (BAR '24 Alg. 1 + SPRO '16 Quotient Ring $\mathbb{Z}_{2^w}[\vec{x}]/\mathcal{Z}^{w,k}$):**
1. Because the multivariate null ideal $\mathcal{Z}^{w,k} = \langle 2^{\max(0, w - \sum v_2(j_i!))} \prod_i x_i^{\underline{j_i}} \rangle$ is a **ring ideal**, reducing intermediate polynomials modulo $\mathcal{Z}^{w,k}$ after **every** `+`, `-`, `*`, and repeated-squaring power step is a **100% sound & complete ring homomorphism**!
   - For any variable $x_i$, any power $x_i^e$ with $e \ge d_w$ (where $d_w$ is the smallest integer with $v_2(d_w!) \ge w$, e.g. $d_{64} = 66$, $d_{32} = 34$, $d_{16} = 18$, $d_8 = 10$) reduces immediately modulo $x_i^{\underline{d_w}} \equiv 0 \pmod{2^w}$ back to degree $< d_w$!
   - **BAR '24 Truncated-Row Stirling Normalization:** To reduce a univariate or axis polynomial of degree $D \ge d_w$ down to $< d_w$, compute Stirling numbers $S(c, r) \bmod 2^w$ ONLY for rows $0 \le r < d_w$ (since for $r \ge d_w$, $c_r = 2^{\max(0, w - v_2(r!))} = 1$, so row $r$ vanishes identically mod $1$!), reduce each $u[r] \bmod 2^{\max(0, w - v_2(r!))}$, and transform back via signed Stirling first-kind $s(r, j) \bmod 2^w$ ($r < d_w$)!
2. **DAG-Memoized Quotient-Ring Evaluation in `poly_equal` (`src/proof/rewrite_proof.ml`):**
   - Memoize `eval_poly` by graph node ID (`Hashtbl.t` keyed by `int`) and reduce modulo $\mathcal{Z}^{w,k}$ whenever a node's polynomial exceeds `max_var_degree` or after multiplication/power so intermediate degrees NEVER exceed $2 d_w - 2$ (and after reduction stay $< d_w$)!
   - Keep strict replay caps (`width <= 128`, `max_monomials = 8192`, `max_ops = 2_000_000`, `max_visited_nodes = 32_768`) — fail closed on cap breach.
   - **Soundness cross-tests in `test/proof_test.ml`:**
     - Positive: 64-bit composed Rivest permutation polynomial $Q(P(x)) \equiv x$ with $\deg(P)\cdot\deg(Q) > 66$ (e.g., $\deg P = 15, \deg Q = 15 \implies$ raw degree $225 > 66$!), verified via `"poly_mod2w"` in `< 10 ms`!
     - Positive: high-degree multivariate polynomial in `(x, y, z)` from `permutation64`.
     - Negative (mandatory Bitwuzla cross-test on 8-bit & 16-bit): perturbing $Q(P(x))$ by $2^{w - v_2(k!) - 1} x^{\underline{k}}$ or constant $+1$ is **rejected** by `poly_mod2w` AND refuted by Bitwuzla!

---

## 3. Producer Upgrades: `BitTrans` $\to$ Quotient-Ring `poly_mod2w`, Centered Sparse Recovery & Untrusted Newton Permutation Inversion (`src/greysynth/normalization.ml`, `greysynth.ml`)

1. **`BitTrans` $\to$ Multivariate `poly_mod2w` Pipeline (`polysim_poly_mod2w`):**
   - Inside `PolySim` (and as a fast early root pass in `greysynth.ml` BEFORE the `> 768` OES-first branch, handling expressions up to `dag_size <= 8192` / `tree_size <= 32768`!):
   - Whenever an expression is a ring polynomial over maximal pure-bitwise leaves (with base atom count $\le 4$, or total distinct conjunction atoms $\le 8$):
     1. Replace each maximal pure-bitwise leaf $B_j$ by its exact `BitTrans` AND-conjunction sum $F(B_j)$ (certified by `linear_mba_mod2w` edges!).
     2. Evaluate & reduce the substituted polynomial in the **quotient ring** $\mathbb{Z}_{2^w}[\text{conjunctions}]/\mathcal{Z}^{w}$ via `reduce_modular_polynomial` (certified by **ONE `poly_mod2w` edge**!).
     3. Run **centered sparse extraction** (Section 3.2 below) + `linear_candidates` cleanup on any degree-1 part so `6*x + 6*y - 8*(x&y) + 3*(x*y)` is emitted cleanly and compactly!
   - **Directly solves ALL 10 remaining `Permutation64` rows** (`3/13 -> 13/13` exact GT!) with zero SMT calls!
2. **Centered Signed Representative Recovery (BAR '24 §VI Fix):**
   - When converting a reduced falling-factorial polynomial $u[\mathbf{j}] \in [0, c_{\mathbf{j}} - 1]$ back to power basis, reducing unsigned can bloat sparse negative terms (e.g., at $w=8$, `-x^2` has $u[2] = 127$, yielding `127*x^2 + 128*x` instead of `-x^2`!).
   - Fix: for each falling-factorial coefficient $u[\mathbf{j}]$ with modulus $c_{\mathbf{j}} < 2^w$, also consider centered shift $u'[\mathbf{j}] = u[\mathbf{j}] - c_{\mathbf{j}}$ when $u[\mathbf{j}] > c_{\mathbf{j}} / 2$ (working top-down from highest total degree to lowest so cancelling high-degree shifts simplify lower degrees too!), and pick the **strictly smaller AST cost** between unsigned canonical, centered canonical, and original polynomial!
   - Certified by the exact same `poly_mod2w` edge (identical canonical normal form mod $\mathcal{Z}^{w,k}$)!
3. **Untrusted 6-Step Newton Compositional Inversion for Rivest Permutation Polynomials (SPRO '16 §2.3):**
   - Add a clean helper `invert_permutation_poly width coeffs` (outside the TCB!):
     - Check Rivest's 3 parity conditions ($a_1$ odd, $\sum_{k\ge 1} a_{2k}$ even, $\sum_{k\ge 1} a_{2k+1}$ even).
     - Shift $r(x) = P(x) - a_0$, initialize $g_0(x) = x$, $h_0(x) = 1$, and run $\lceil \log_2 w \rceil$ Newton steps in $\mathbb{Z}_{2^w}[x]/\mathcal{Z}^w$:
       $$h_{i+1} = \mathrm{red}_{\mathcal{Z}}(h_i \cdot (2 - r'(g_i) \cdot h_i)), \qquad g_{i+1} = \mathrm{red}_{\mathcal{Z}}(g_i - h_{i+1} \cdot (r(g_i) - x))$$
       returning $P^{-1}(y) = \mathrm{red}_{\mathcal{Z}}(g_{\text{final}}(y - a_0))$.
   - Use it in two constructive ways:
     1. When `P(Q(e))` is encountered as a nested univariate polynomial composition (even at raw degree $> 66$), quotient-ring DAG evaluation collapses it directly via `poly_mod2w`!
     2. When `P(e1) == P(e2)` (or `P(e1) - P(e2)`) appears in an equality/conditional/opaque predicate where $P$ is a Rivest permutation polynomial, $P$ is **bijective** mod $2^w$ — so `P(e1) == P(e2) <-> e1 == e2` (certified via `P^{-1}(P(e1)) == e1` and `P^{-1}(P(e2)) == e2` in `poly_mod2w`!).

---

## 4. Fast, Focused Verification Gate for Round 24 (Target Wall Time: ~3–5 min!)

1. **Unit & Soundness Tests (`test/proof_test.ml`, `test/normalization_test.ml`):**
   - Quotient-ring DAG `poly_mod2w` positive (degree $> 66$ composition $Q(P(x)) \equiv x$ at 64-bit) & negative (off-by-one-bit Bitwuzla cross-test at 8/16-bit).
   - Centered sparse recovery test (`-x^2` at 8/64-bit stays `-x^2`, never bloats to `127*x^2 + 128*x`).
   - Newton inversion test: invert a degree-5 64-bit Rivest permutation polynomial $P$, verify $P^{-1}(P(x)) \equiv x \pmod{2^{64}}$ via `mba_proof` (`poly_mod2w`).
   - Regression tests on actual `permutation64` rows (`line_0000003`, `line_0000006`, `line_0000010`) verifying exact collapse to `<= 20` (GT) with `mba_proof` replay!
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/all_failing/permutation64/`** (all 10 remaining cases — target: **`10/10` solved**, plus run full `datasets/cobra/permutation64.txt` 13 cases to confirm **`13/13` solved = `1.0000x`!**)
   - **`datasets/hard_cases/all_failing/pldi_poly/`** (62 weak cases)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted, zero regressions!)
   - **`datasets/hard_cases/core_hard/`** (413 cases — track overall solved count climbing!)
4. Record concise Round-24 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
