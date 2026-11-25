# GreySynth Round-19 Spec: High-Degree Univariate & Multivariate Modular Polynomial Engine (`poly_mod2w`)

**Baseline commit:** `ed0f259` (`3f856ab` code + Wave 1 & Wave 2 audit reports committed & pushed)  
**Target:** Crush the **2,002 weak polynomial cases** exposed in Wave 1 (`datasets/cobra/univariate64.txt` — 999/1,000 weak at 84.2×; `datasets/cobra/multivariate64.txt` — 994/1,000 weak at 628.6×; `datasets/cobra/permutation64.txt` — 9/13 weak at 27.3×) while keeping 100% fail-closed soundness and fast independent replay in `mba_proof`.

---

## 1. Decidable `poly_mod2w` Proof Kernel Rule (`src/proof/rewrite_proof.ml`, `src/proof/rewrite_proof.mli`)

Currently `ring_mod2w` only checks formal commutative-ring identity mod $2^w$ (degree $\le 16$, monomials $\le 4096$), so modular null polynomials like $2^{49} x^{\underline{16}} \equiv 0 \pmod{2^{64}}$ or multivariate null polynomials $\sum c_{\vec{k}} \prod_i t_i^{\underline{k_i}} \equiv 0 \pmod{2^{64}}$ cannot be certified without bit-blasting (which times out in Bitwuzla at 64 bits).

**Exact mathematical rule (Singmaster / Kempner / Chen theorem over $\mathbb{Z}/2^w\mathbb{Z}$):**
Any polynomial $P(t_1, \dots, t_m) = \sum_{\vec{e}} a_{\vec{e}} \prod_i t_i^{e_i}$ over opaque interned subterms $t_1, \dots, t_m$ of width $w$ transforms uniquely into the multivariate falling-factorial basis via Stirling numbers of the second kind $S(e, k)$:
$$P(t_1, \dots, t_m) = \sum_{\vec{k}} c_{\vec{k}} \prod_{i=1}^m t_i^{\underline{k_i}}, \qquad t^{\underline{k}} = t(t-1)\cdots(t-k+1).$$
Because every integer product $\prod_{i=1}^m t_i^{\underline{k_i}}$ is always divisible by $\prod_{i=1}^m (k_i!)$, whose 2-adic valuation is $V(\vec{k}) = \sum_{i=1}^m v_2(k_i!)$ (where $v_2(k!) = \sum_{j \ge 1} \lfloor k / 2^j \rfloor$):
- **Soundness:** If for every $\vec{k}$, $2^{\max(0, w - V(\vec{k}))} \mid c_{\vec{k}}$, then $P(t_1, \dots, t_m) \equiv 0 \pmod{2^w}$ identically for ALL bitvector values of $t_1, \dots, t_m$ (even when $t_i$ are correlated opaque expressions!).

**Deliverables in `src/proof/rewrite_proof.ml` & `.mli`:**
1. Add equality rule `"rule": "poly_mod2w"` (alongside `"smt"` and `"ring_mod2w"`, keeping full backward compatibility with v1 certificates) and `Rewrite_proof.record_poly` + `poly_proofs` metric field in `verify` JSON output.
2. Represent sparse multivariate monomials compactly as sorted `(atom_id * exponent) list` (NOT repeated atom lists, so degree 64 takes O(1) space!).
3. Implement `poly_equal g left right`:
   - Enforce strict replay caps: `max_var_degree = 66`, `max_total_degree = 66`, `max_monomials = 8192`, `max_ops = 1_000_000`, `width <= 128`.
   - Compute sparse difference `diff = poly(left) - poly(right)` mod $2^w$ over opaque interned non-ring atoms (`bvadd`, `bvsub`, `bvneg`, `bvmul`, `const`).
   - If `diff` is empty, return `Ring_equal` immediately.
   - Otherwise apply the exact axis-by-axis falling-factorial Stirling transform (`S(e, k) mod 2^w`, computed dynamically by Pascal recurrence up to the observed max exponent `<= 66`) along each variable appearing in `diff`.
   - Check that every resulting falling-factorial coefficient $c_{\vec{k}}$ satisfies `(c_k mod 2^(max(0, w - sum v2(k_i!)))) = 0`!
   - Return `Ring_equal` iff ALL falling-factorial coefficients vanish mod their exact $2^{\max(0, w - V(\vec{k}))}$ threshold; otherwise `Ring_not_equal` (or `Ring_limit_exceeded` if caps trigger).
4. **Cross-tests in `test/proof_test.ml`:**
   - Verify `poly_mod2w` proves univariate degree-2..20 null polynomials (8/16/32/64-bit) and multivariate null polynomials like $2^{w - v_2(k_1!) - v_2(k_2!)} x^{\underline{k_1}} y^{\underline{k_2}} \equiv 0$.
   - **Negative soundness tests (critical!):** Cross-test against Bitwuzla on 8-bit and 16-bit widths that changing ANY falling-factorial coefficient by $2^{w - V(\vec{k}) - 1}$ (one bit below the exact threshold!) is **REJECTED** by `poly_mod2w` (`Ring_not_equal`) AND refuted by Bitwuzla!

---

## 2. High-Degree Univariate & Multivariate Polynomial Reducer (`src/greysynth/normalization.ml`, `src/greysynth/rewrite.ml`, `src/greysynth/egraph.ml`, `src/greysynth/greysynth.ml`)

**Deliverables:**
1. Extend `Rewrite.accepts_compositional` (and `Egraph` proof records) to carry optional `~poly_equalities` certified via `Rewrite_proof.record_poly`.
2. Implement `reduce_modular_polynomial cost expression` in `src/greysynth/normalization.ml` (handling arbitrary degree up to `66` and up to `8192` monomials over opaque ring atoms!):
   - Parse `expression` as a sparse multivariate polynomial mod $2^w$ using compact `(atom * exponent) list` monomials (checking `check_timeout ()` periodically!).
   - Perform the exact axis-by-axis Stirling transform to falling-factorial basis $c_{\vec{k}}$.
   - Reduce every coefficient $c_{\vec{k}} \leftarrow c_{\vec{k}} \bmod 2^{\max(0, w - \sum v_2(k_i!))}$ (which immediately zeroes every null term AND cancels obfuscated high-bit null multiples on surviving terms!).
   - Transform the reduced falling-factorial polynomial back to power basis via exact signed Stirling numbers of the first kind $s(k, j) \pmod{2^w}$ (axis-by-axis).
   - Rebuild the reduced polynomial into a compact AST (using balanced/Horner or power-squaring representation for any surviving powers $t^e$, omitting zero terms and unit coefficients `1 * t -> t`, `-1 * t -> -t`).
   - If `cost candidate < cost expression`, emit `(candidate, [], [ expression, candidate ])` (1 single `poly_mod2w` edge!).
3. **Large-root placement (CRITICAL for `multivariate64` & `permutation64`!):**
   - Notice `multivariate64` expressions are ~2,400 AST nodes (`> 2,048` e-graph limit) and `permutation64` expressions are up to ~11,169 AST nodes (`> 768` OES-first threshold)!
   - Therefore invoke `reduce_modular_polynomial` as a fast early root pass in `run_preprocessing` (before the `>768` OES-first branch!) whenever the root expression has `cost >= 5` and is a ring combination of opaque terms (or contains high-degree ring structure), AND also wire it into `Normalization.run`, `Normalization.local_candidates`, and `Egraph.optimize`!
   - After `reduce_modular_polynomial` shrinks a `permutation64` expression (e.g., killing the degree-2..10 null terms over opaque atoms `(x^y), (x|y), (x*y)`), the remaining compact linear/quadratic MBA automatically flows right into `Egraph.optimize` / `Normalization` to collapse all the way to ground truth!
   - Also check `permutation64` rows 1–13 to see if any remaining rows need higher-degree Rivest/Hensel inversion or opaque-atom linear cleanup after null-polynomial reduction, and handle them cleanly!

---

## 3. Focused Unit Tests & Verification Gate for Round 19

1. **Unit & soundness tests (`test/proof_test.ml`, `test/normalization_test.ml`):**
   - `poly_mod2w` positive & negative (off-by-one-bit) Bitwuzla cross-tests across 8/16-bit univariate & multivariate polynomials.
   - Direct regression tests on actual rows from `univariate64.txt` (row 1), `multivariate64.txt` (row 1), and `permutation64.txt` (rows 1–5), verifying strict collapse to `<= GT` AND independent `mba_proof` replay!
2. **Run `devcontainer exec --workspace-folder . make test`** — 100% green.
3. **Full audit of all 3 polynomial suites (zero `--limit`, `--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`):**
   - `datasets/cobra/univariate64.txt` (1,000 cases) — target: dramatic jump from `1/1,000` solved (`84.2×`) toward `~1,000/1,000` solved (`~1.00×`)!
   - `datasets/cobra/multivariate64.txt` (1,000 cases) — target: dramatic jump from `6/1,000` solved (`628.6×`) toward `~1,000/1,000` solved (`~1.00×`)!
   - `datasets/cobra/permutation64.txt` (13 cases) — target: dramatic jump from `3/13` solved (`27.3×`) toward `~13/13` solved!
4. **Quick regression check on 5×100 MBA smoke sets** (confirm zero regressions!).
5. Record concise Round-19 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `docs/FULL_AUDIT_REPORT.md`).
