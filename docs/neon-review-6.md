# GreySynth Round-6 Review: `ring_mod2w` Audit, 6 Fixes & Milestone 3B.2 Spec

**Reviewed commits:** `be594a2..eae80e4` (`be594a2`, `10a515f`, `40d431f`, `5636640`, `eae80e4`)  
**Summary:** Huge milestone! Adding the bounded `ring_mod2w` kernel rule and minterm certification moved `PLDI Non-Poly` geometric quality from **19.2494x down to 1.5868x** (100/100 strictly smaller, 100/100 proved) and dropped `nonpoly_L2_full` from **6.61s (stuck at 127)** to **0.031s (`121 -> 3`, `a * y`)** with full `mba_proof` replay!  
The `ring_equal` checker itself (`src/proof/rewrite_proof.ml:418-488`) is **mathematically sound** for all bit widths $w \ge 1$. However, live probing exposed **6 concrete bugs/gaps** in how `minterm_ring_proof` is wired (explaining why `PLDI Non-Poly` stopped at `1.5868x` instead of `~1.05x`), followed by the exact spec for Milestone 3B.2 (`MBA-Obfuscator nonlinear` `11.47x -> ~1.1x`).

---

## 1. Live Probe Evidence (at `eae80e4`, `default.json`, `total_timeout=5`, `equiv_timeout=1`)

| Case | Result | Time | Edges (`ring`) | `inconclusive` | Diagnosis |
|---|---:|---:|---:|---:|---|
| `nonpoly_L2_inner` (`== a`) | **27 -> 1** | **0.033s** | 4 (1) | 0 | Works via `early_minterm`! |
| `nonpoly_L2_full` (`== a * y`) | **121 -> 3** | **0.031s** | 16 (1) | 0 | Works! Inner `a` exposed `product_partition_candidate`. |
| **`linear_eq_a_plus_b`** (`== a + b`) | **44 -> 18** | 4.101s | 4 (1) | **5** | **Bug 1:** `accepts` never calls `minterm_ring_proof` for non-variable targets! |
| **`linear_big64_coeffs`** (`== 0`) | **19 -> 19** | 5.161s | 0 (0) | **4** | **Bug 1:** Target is constant `0`, skipped by `early_minterm` and `accepts`! |
| **`linear_big64_const_off`** (`== 5 - 0x1234...`) | **14 -> 14** | 6.111s | 0 (0) | **2** | **Bug 1 + Bug 2:** `E.Cst` not expanded to `(-c) * all_minterms`! |
| **`linear_big_subterm_atom`** (`== x * y`) | **25 -> 25** | 5.050s | 0 (0) | **4** | **Bug 3:** `minterm_ring_proof` only collects `E.Var`, not opaque compound atoms! |
| **`poly_mba_cancel_2term`** (`== 0`) | **21 -> 21** | 4.650s | 0 (0) | **4** | **Milestone 3B.2:** Even 2-term identical-monomial ring cancellation isn't wired yet! |

---

## 2. Six Concrete Bugs to Fix First

### Bug 1 (Critical): `minterm_ring_proof` is NOT wired into `accepts` for `linear_candidates` (`src/greysynth/normalization.ml:1016-1028, 1068-1074`)
Currently `minterm_ring_proof` is called **only** inside `early_minterm` (`normalization.ml:1016-1028`), which only tests single variables (`a`, `b`, `x`, `y`). Inside `accepts` (`normalization.ml:1068-1074`), candidates produced by `linear_candidates` (like `a + b`, `a ^ b`, `0`, `~a`, `a | b`, `3*a + 5`) still fall back to `complement_product_steps` -> monolithic Bitwuzla timeout!

Additionally, `early_minterm` calls `minterm_ring_proof original candidate` (allocating $2^k$ minterms and walking the whole subtree) for *every* variable on *every* node with `cost >= 11` **before** checking `Rewrite.samples_agree original candidate`.

**Fix:**
1. In `accepts candidate` (`normalization.ml:1068-1074`), try `minterm_ring_proof !current candidate` **first** (whenever `Rewrite.samples_agree !current candidate` passes, or let `accepts_compositional` check samples first — wait: check `Rewrite.samples_agree !current candidate` *before* constructing the minterm expansion so non-equivalent candidates cost zero minterm work!). Fall back to `complement_product_steps` -> `Rewrite.accepts` only when `minterm_ring_proof` returns `None`.
2. In `early_minterm` (`normalization.ml:1016-1028`), gate on `Rewrite.samples_agree original candidate` *before* calling `minterm_ring_proof original candidate`.

### Bug 2 (Critical): `minterm_ring_proof` fails on constant offsets / `~x + x == -1` (`src/greysynth/normalization.ml:437-441`)
At line 441, `expand` leaves `E.Cst c` unexpanded (`| E.Cst _ -> Some expression`), while `is_boolean` (`lines 395-405`) expands `~a` to `m0` and `a` to `m1`. Therefore:
- `expand (~a + a)` produces `m0 + m1`,
- `expand (-1)` produces `-1`.
In the formal ring $\mathbb{Z}/2^w\mathbb{Z}[m_0, m_1]$, `m0 + m1 != -1`, so `ring_equal` rejects **every** linear MBA whose constant term cancels against complements (e.g., `10*(~a) + 10*a == -10`, `linear_big64_const_off`, `linear_3var_const_offset`, and constant-offset cases in `PLDI Non-Poly`).

**Fix:**
- Let `all_minterms = sum (Array.to_list minterms)` and `fill_expr = E.constant (Bitvector.fill width)` (i.e. `-1`).
- Lazily emit **one** `"smt"` edge `(fill_expr, all_minterms)` (1.4 ms in Bitwuzla!) whenever any nonzero `E.Cst c` is expanded.
- For `E.Cst c` where `not (Bitvector.is_zeros c)`:
  - Emit a tiny `"ring_mod2w"` edge `(E.Cst c, E.binary E.Mul (E.constant (Bitvector.neg c)) fill_expr)` (trivial `c == (-c) * (-1)` mod $2^w$, 0.01 ms!), OR directly substitute `E.binary E.Mul (E.constant (Bitvector.neg c)) all_minterms` in `expand` AND record the single `"ring_mod2w"` edge `(E.Cst c, E.binary E.Mul (E.constant (Bitvector.neg c)) fill_expr)` so congruence closure connects `E.Cst c == (-c) * fill_expr == (-c) * all_minterms`!
  - (Special case: if `Bitvector.is_fill c`, no extra ring edge is needed — `fill_expr == all_minterms` directly!)

### Bug 3 (High): `minterm_ring_proof` only collects `E.Var` atoms, failing on compound subterm atoms (`src/greysynth/normalization.ml:354-366`)
`linear_candidates` supports arbitrary opaque non-linear / mixed-width subterms as atoms (e.g., `x * y` in `linear_big_subterm_atom`, `5 * x` and `6 * y` in the paper's contextual example), whereas `minterm_ring_proof` only collects `Sample_evaluator.variables_of_expr`. On `linear_big_subterm_atom` (`10*((x*y)^z) + 20*((x*y)&z) - 9*(x*y) - 10*z == x*y`), `minterm_ring_proof` returns `None` and Bitwuzla times out 4 times.

**Fix:** Collect maximal non-ring, non-boolean subterms of width `width` (the exact same atom-collection rule used by `linear_candidates`: stop descending at any node outside `{Plus, Minus, Mul, Neg, Lsl-const, And, Or, Xor, Not, Cst}`, or at any `Mul` that occurs *inside* a bitwise op `{And, Or, Xor, Not}`) as the `atoms` array in `minterm_ring_proof`. Because `Rewrite_proof.abstract_pair` already abstracts shared compound subterms, Bitwuzla proves every bitwise-to-minterm edge over compound atoms in **< 1 ms**!

### Bug 4 (Medium): `E.Lsl` `"smt"` edge in `minterm_ring_proof` mixes unexpanded LHS with expanded RHS (`src/greysynth/normalization.ml:446-459`)
Line 456 emits `(expression, replacement)` where `expression = orig_x << k` (unexpanded) and `replacement = expanded_x * 2^k` (expanded minterm sum), forcing Bitwuzla to prove minterm expansion AND multiplication together.

**Fix:** Emit `(E.binary E.Lsl orig_x y, E.binary E.Mul orig_x pow2)` (pure `t << k == t * 2^k`, proved in 0.5 ms via `abstract_pair`!) while returning `E.binary E.Mul expanded_x pow2` — congruence closure connects `orig_x == expanded_x` automatically.

### Bug 5 (Medium): Worst-case quadratic DoS guard & limit reporting in `ring_equal` (`src/proof/rewrite_proof.ml:456-488, 531-546`)
In `ring_equal`:
1. `mul` checks `Polynomial.cardinal > 4096`, which stops distinct-monomial growth, but an adversarial certificate multiplying two 4096-term polynomials that collapse onto fewer monomials can still run up to $4096^2 \approx 16\text{M}$ inner iterations. Add a simple `ops` ref incremented per `add_term` call with `if !ops > 200_000 then raise Ring_limit` to guarantee `< 20 ms` worst-case replay time.
2. Distinguish `Ring_limit` (limit exceeded -> `U.Unknown` / explicit reason `"ring_limit_exceeded"`) from genuine polynomial inequality (`U.No` / `"ring_not_equal"`), while still never accepting an exceeded edge as proved.

### Bug 6 (Low): `~allow_oracle` propagation & ring certification in `normalization.ml:989, 1059, 1076`
1. Lines 1059 and 1076 call `visit candidate` without `~allow_oracle`, silently resetting `allow_oracle` to `true` after a local rewrite. Forward `~allow_oracle` consistently.
2. In `try_oracle` (`normalization.ml:989`), try `minterm_ring_proof current candidate` / `ring_mod2w` before falling back to monolithic `Rewrite.accepts` so differential oracle runs can certify 64-bit answers.

---

## 3. Milestone 3B.2 Spec: Native Sparse Polynomial, Factor Grouping & Permutation-Polynomial Inversion

With `ring_mod2w` now live in `Rewrite_proof`, Milestone 3B.2 becomes remarkably clean and fast (zero 50-edge micro-step chains!):

### 3.1 Pure Sparse Ring Normalization (`ring_polynomial_candidate`)
Given any uniform-width expression rooted at `Plus | Minus | Mul | Neg`:
1. Parse it into a canonical sparse polynomial over $\mathbb{Z}/2^w\mathbb{Z}$ treating every non-`{+,-,neg,*}` subterm as an opaque atom (bounded by e.g. `max_degree = 8`, `max_monomials = 256`).
2. Reconstruct a compact candidate from the canonical polynomial (combining like monomials, dropping zero terms, signed `positive - negative` layout).
3. If `cost candidate < cost current`, certify in **ONE `ring_mod2w` edge (< 0.1 ms)**!
   - Immediately solves `poly_mba_cancel_2term` (`21 -> 1`, `0`), duplicate/canceling polynomial terms, and **formal** permutation-polynomial inverses (`P^{-1}(P(x)) == x` in $(\mathbb{Z}/2^w\mathbb{Z})[x]$) in `< 1 ms`!

### 3.2 Native Multiplicative Factor Grouping + Cofactor Linear Reduction (`factor_group_candidate`)
Target: `MBA-Obfuscator nonlinear` (`11.47x -> ~1.1x`) and `poly_mba_cancel` (`167 -> 11`):
1. From the canonical sparse polynomial $\sum_m c_m \cdot m$ (where each monomial $m$ is a multiset of opaque atoms):
2. Find the highest-frequency opaque atom $F$ appearing in $\ge 2$ monomials of degree $\ge 2$ (or partition all degree $\ge 2$ monomials greedily by their most-frequent shared factor $F_1, F_2, \dots$).
3. Rewrite the polynomial as:
   $$\text{factored} = \sum_i F_i \cdot C_i + R$$
   where each cofactor $C_i$ is the sum of the remaining parts of monomials containing $F_i$, and $R$ is the unfactored remainder.
4. Notice: `current == factored` is a **100% pure formal ring identity** -> certified by **ONE `ring_mod2w` edge (< 0.2 ms)**!
5. Now run `linear_candidates` + `minterm_ring_proof` on each cofactor $C_i$ (and on $R$ if non-empty):
   - On `MBA-Obfuscator nonlinear` (e.g., `poly_mba_cancel`), every $C_i$ is a 2-variable linear MBA that collapses to a single constant $c_i$ (`-17`, `-5`) via 3 tiny `"smt"` edges + 1 `"ring_mod2w"` edge!
   - Combine the factored ring edge `(current, factored)` + each cofactor's `(equalities_i, ring_equalities_i)` + a final cleanup `"ring_mod2w"` edge `(factored_with_reduced_cofactors, compact_result)` in a single `Rewrite.accepts_compositional` call!
   - If `cost compact_result < cost current`, accept! Total time for 167-node `poly_mba_cancel`: **< 10 ms**!

### 3.3 Univariate Permutation-Polynomial & Null-Polynomial Reduction
Target: `perm_poly_quad` (`45 -> 1`) and `ProMBA Poly`:
1. After expanding a univariate polynomial $Q(x) = \sum_{d=0}^D a_d x^d \pmod{2^w}$:
   - Check if any high-degree residual is a **null polynomial** mod $2^w$ using the falling-factorial basis $x^{\underline{k}} = x(x-1)\cdots(x-k+1)$: whenever $2^{w - v_2(k!)} \mid c$, the term $c \cdot x^{\underline{k}} \equiv 0 \pmod{2^w}$ (e.g., $k=2$: $2^{w-1} \cdot x(x-1) \equiv 0 \pmod{2^w}$).
   - Prove the tiny local null lemma `(c * x*(x-1)..., 0)` via `"smt"` (or via `(x * (x - 1)) & 1 == 0`) and combine with `"ring_mod2w"`!
2. For compositions $F(P(x))$ where $P$ is a permutation polynomial mod $2^w$ ($a_1$ odd, $a_2, a_3, \dots$ even — Rivest's theorem), compute $P^{-1}$ via Hensel/Newton iteration mod $2^w$ when needed and verify `Q(P(x)) == R(x)` via `ring_mod2w` (+ any null-polynomial lemma).

---

## 4. Acceptance Targets for This Iteration

1. Fix all **6 bugs** in Section 2 with focused unit regressions (`linear_eq_a_plus_b`, `linear_big64_coeffs`, `linear_big64_const_off`, `linear_big_subterm_atom`, `E.Lsl` minterm proof, `ring_equal` op-limit guard).
2. Implement **Milestone 3B.2** (`ring_polynomial_candidate` + `factor_group_candidate` + permutation/null-polynomial reduction) with focused unit tests including `poly_mba_cancel` (`167 -> 11`) and `perm_poly_quad`.
3. Run `make test` in the Dev Container (all green).
4. Re-audit the 100-case smoke sets for:
   - `PLDI Non-Poly` (verify improvement below `1.5868x`, 100/100 proved),
   - `MBA-Obfuscator nonlinear` (verify major drop from `11.4734x` toward `~1.1x`, 100/100 proved),
   - `PLDI Poly` and `QSynth EA` (no regressions),
   and update `docs/IMPLEMENTATION_RESULTS.md` and `docs/PLAN.md`.
5. Commit atomically (keep `docs/neon-review*.md` untouched).
