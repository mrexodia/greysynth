# GreySynth Round-36 Spec: Shift- & Slice-Aware Linear/Semi-Linear MBA Peeling, Opaque-Atom DAG Reduction & Abstract-Certified Bit-Slice Identities

**Baseline:** Round 35 (`dcefef4` / `a85dd15` — modularized `Norm_*` architecture, `94.12%` exact `<= GT` across 52,645 GT expressions, `3,100` remaining `all_non_exact/` rows of which **`1,894` (61%) are `Tigress L5–L8`** and `177` are `OMVLL`).

**Forensic Diagnosis of All `1,894` Remaining `Tigress L5–L8` Outputs:**
Inspecting the exact Round-34 outputs of all `1,894` remaining `Tigress L5–L8` rows revealed **four 100%-general algebraic gaps** (zero obfuscator-specific hacks!):

1. **Constant left-shifts (`<< k`) and multi-variable opaque atoms broke `dag-linear-mba` (`80.9%` of remaining Tigress rows contain `<< 1`!):**
   - `((A & B) << 1) + (A ^ B) == A + B`, `((A | B) << 1) - (A ^ B) == A + B`, `((A & ~B) << 1) - (A ^ B) == A - B`, and `(A & ~B) - (B & ~A) == A - B` failed to peel in `dag_bottom_up_simplify` for **two** general reasons:
     - **(a)** `linear_mba_mod2w` (in `src/proof/rewrite_proof.ml`) and `linear_mba_compatible` rejected constant left-shift `E << k` in arithmetic position even though $x \ll k \equiv 2^k \cdot x \pmod{2^w}$ identically!
     - **(b)** `dag_bottom_up_simplify` gated `linear_candidates` on `List.length (variables_of_expr !result) <= 8 && linear_mba_compatible !result`, which inspected **all leaf variables** inside opaque nonlinear/division/cast children instead of just the **opaque atom count** (blocking 2-atom identities like `(A ^ B) + (2*(A & B))` whenever `A, B` contained `Mul`, `Udiv`, `Sext`, or `> 8` leaf vars, e.g. `tigress_l5/3126`, `tigress_l6/1173`, `tigress_l6/1524`, `tigress_l8/1286`!).
2. **Low-bit zero-extended slices (`uext(w-k, restrict(0, k-1, E))`) and `<< k` broke `semilinear_mba_mod2w` (`35.7%` of remaining Tigress rows contain `uext(w-1)(restrict(0,0) E)`!):**
   - `((uext(63)(restrict(0,0) E)) << 1) + (1 ^ E) == E + 1` (`tigress_l5/6533`), `(uext(63)(restrict(0,0) E)) + (E | 1) == E + 1` (`tigress_l6/1739`, `1481`), and `((E & -2) << 1) - (E ^ 1) == E - 1` (`tigress_l7/1285`, `tigress_l8/1285, 5697, 1281`) are all pure **1-atom semi-linear MBA identities**, blocked solely because `semilinear_mba_mod2w` didn't treat `uext(w-k, restrict(0,k-1, E))` as `E & ((1<<k)-1)` or arithmetic `E << k` as `(1<<k) * E`, and because `dag_bottom_up_simplify` skipped `semilinear_mba_candidate` when `minimal = true`!
   - Also in multi-term sums (`tigress_l5/2558`, `tigress_l6/2536`: `((~x1 | M) + x1 + 1) + (x0 & M)`), partitioning additive sums by opaque variable exposes the 1-variable semi-linear subset `((~x1 | M) + x1 + 1) -> x1 & M`!
3. **Zero-cost abstract-certified bit-slice / shift / mask collapses on arbitrary-size subtrees:**
   - Giant `Tigress L7–L8` trees wrap million-node subexpressions in `restrict(0, hi) (X << k)` (`== 0` whenever `k > hi`!), `(uext(w-k, restrict(0, k-1, X))) & C` (`== 0` whenever low `k` bits of `C` are `0`, e.g., `(uext(63)(restrict(0,0) E)) & 2 == 0`!), and `restrict(0, hi) (X | C)` / `(X ^ C)` / `(X & C)` / `(X + C)` when the low `hi+1` bits of `C` are the identity (`tigress_l5/3500`). Because `known_bits_candidate` was guarded to `cost <= 256` to avoid raw giant-tree SMT, these vanished-to-zero wrappers never fired on giant DAGs! Certifying them via **1-variable abstract equality** takes `< 0.5 ms` regardless of subtree size!
4. **Two tiny general algebraic polish gaps:**
   - **Complemented scaled term inside bitwise ops (`tigress_l5/4671`, `tigress_l6/4191, 4192`, `tigress_l5/4785`):** `ring_polynomial_candidate` expanded `~(c * x)` into `(-1) + ((-c) * x)` inside `B + (A & (-1 + (-c)*x))`, hiding `B + (A & ~B) == A | B`! Recognizing `(-1) + ((-c) * x) == ~(c * x)` inside bitwise contexts (or folding `-1 - E -> ~E`) collapses all of them to `A | B`!
   - **Complementary constant in zero-SMT product peeling (`tigress_l8/5511`, `2789`):** Generalize `nonlinear_product_identity_candidate` so `((~a & C) * (a & ~C)) + ((a & C) * (a | C)) == a * C` also matches when `~C` was already constant-folded (e.g. `0x1e` and `0xffffffffffffffe1`), using the exact same zero-SMT `linear_mba_mod2w` + `ring_mod2w` proof!

---

## 1. Arithmetic Constant `Lsl` in `linear_mba_mod2w` & `Lsl` + `uext(restrict(0, k-1))` in `semilinear_mba_mod2w` (`src/proof/rewrite_proof.ml`)

**Strict Soundness Rules (MUST be cross-tested positively AND negatively against Bitwuzla in `test/proof_test.ml`!):**
1. **`linear_mba_mod2w` (`src/proof/rewrite_proof.ml`):**
   - In **arithmetic position ONLY** (outside any bitwise operator `~`, `&`, `|`, `^`):
     - `E.Binary { f = Lsl; x; y = E.Cst k }` (with `0 <= k < width`): evaluate as exact scalar multiplication by `Z.shift_left Z.one k` mod $2^w$ (and `0` if `k >= width`).
   - Underneath ANY bitwise operator (`~`, `&`, `|`, `^`): `Lsl` MUST remain a **strict opaque atom**!
   - **Mandatory negative test:** verify that `((x << 1) & (y << 1)) == ((2 * x) & (2 * y))` is accepted ONLY when `x << 1` is treated as opaque, and that `((x << 1) & y)` is NEVER falsely distributed as `2 * (x & y)` (reject trap `((x << 1) & y) == 2 * (x & y)` in both kernel and Bitwuzla!).
2. **`semilinear_mba_mod2w` (`src/proof/rewrite_proof.ml`):**
   - In **arithmetic position ONLY**: `E.Binary { f = Lsl; x; y = E.Cst k }` evaluates as exact scalar multiplication by $2^k \pmod{2^w}$ (strictly opaque under bitwise operators!).
   - In **bitwise OR arithmetic position**: `E.Unary { f = E.Uext amount; x = E.Unary { f = E.Restrict { lo = 0; hi }; x = inner } }` when `amount > 0 && hi + 1 + amount = E.sizeof inner`: evaluate identically as `inner & ((1 << (hi + 1)) - 1)` (exact zero-extended low-bit mask; `lo = 0` strictly enforced!).
   - **Mandatory negative tests:**
     - Reject `uext(amount) (restrict(lo, hi) x)` when `lo > 0` (e.g. `restrict(1, 7)` is a right shift, NOT a mask — MUST remain strictly opaque!).
     - Reject `sext(amount) (restrict(0, hi) x)` (sign extension is NOT a mask — MUST remain strictly opaque!).
     - Reject `Lsl` under bitwise operator (`((x << 1) & 2) == 2 * (x & 1)` is a shift-under-bitwise trap unless treated as opaque!).
   - **Mandatory positive tests:**
     - `((a & b) << 1) + (a ^ b) == a + b` (`linear_mba_mod2w`)
     - `((a | b) << 1) - (a ^ b) == a + b` (`linear_mba_mod2w`)
     - `((a & ~b) << 1) - (a ^ b) == a - b` (`linear_mba_mod2w`)
     - `((uext(63) (restrict(0, 0) x)) << 1) + (1 ^ x) == x + 1` (`semilinear_mba_mod2w`)
     - `(uext(63) (restrict(0, 0) x)) + (x | 1) == x + 1` (`semilinear_mba_mod2w`)
     - `((x & -2) << 1) - (x ^ 1) == x - 1` (`semilinear_mba_mod2w`)

---

## 2. Opaque-Atom DAG Linear & Semi-Linear Peeling (`src/greysynth/norm_linear.ml`, `src/greysynth/norm_semilinear.ml`, `src/greysynth/normalization.ml`)

**Deliverables:**
1. **Opaque-atom `dag-linear-mba` (NO leaf-variable cap, NO recursing into opaque non-linear children!):**
   - In `normalization.ml` (`dag_bottom_up_simplify`), replace the overly restrictive `List.length (variables_of_expr !result) <= 8 && linear_mba_compatible !result` gate with a fast **opaque-atom linear check**:
     - Whenever the root of `!result` is an arithmetic/bitwise operator (`+`, `-`, `*`, `<<`, `&`, `|`, `^`, `~`), call `linear_candidates ~max_atoms:4 cost !result` (or `~max_atoms:6` when `not minimal` and `cost !result <= 512`), where `linear_candidates` already treats every `Mul` (non-const), `Udiv`, `Sdiv`, `Urem`, `Srem`, `Uext`, `Sext`, `Restrict`, `Lshr`, `Ashr`, `Ite` as a **single opaque atom** without traversing inside it (`tick ()` only counts the linear spine, NOT the interior of opaque atoms!!).
     - **CRITICAL:** Make sure `linear_candidates` does **NOT** recurse into opaque atoms (`E.is_equal` hash-consing comparison is $O(1)$ on Binsec `Sexpr.Expr`!), so peeling `((A & B) << 1) + (A ^ B) -> A + B` takes `< 0.1 ms` even if `A` and `B` are 500,000-node subtrees with 11 variables!
     - Certify via `Rewrite.accepts_compositional ~pass:"dag-linear-mba" ~equalities:[] ~linear_mba_equalities:[ !result, candidate ] !result candidate` (**ZERO SMT!**).
2. **Decidable `dag-semilinear-mba` (including `minimal = true` on giant DAGs!):**
   - Update `semilinear_mba_candidate` in `norm_semilinear.ml` to:
     - Support arithmetic `E << k` (constant `1 <= k < w`) and `uext(w-k, restrict(0, k-1, E))` transparently as `2^k * E` and `E & ((1<<k)-1)`.
     - Treat complex subtrees (`Mul`, `Udiv`, `Sdiv`, `Lshr`, `Ashr`, `Sext`, non-zero-lo `Restrict`, etc.) as **opaque atoms** (up to 2 opaque atoms in `minimal = true` mode, up to 4 in normal mode) so `((uext(63)(restrict(0,0) A)) << 1) + (1 ^ A) -> A + 1` and `(uext(63)(restrict(0,0) A)) + (A | 1) -> A + 1` and `((A & -2) << 1) - (A ^ 1) -> A - 1` peel in `< 0.5 ms` with **ZERO SMT** (`semilinear_mba_mod2w`) even inside giant DAGs!
   - Add **additive sub-sum semi-linear partitioning** (in `norm_semilinear.ml`): when an additive sum `T_1 + ... + T_m` (`3 <= m <= 16`) mixes terms over different variables/atoms (e.g. `((~x1 | M) + x1 + 1) + (x0 & M)` in `tigress_l5/2558` and `tigress_l6/2536`), partition the additive terms by opaque atom, run `semilinear_mba_candidate` on each single-atom bucket (attaching the constant offset to each bucket in turn), and certify with `ring_mod2w` + `semilinear_mba_mod2w` (ZERO SMT!).

---

## 3. Abstract-Certified Bit-Slice / Shift / Mask & Complement Identities (`src/greysynth/norm_peepholes.ml`, `src/greysynth/norm_nonlinear.ml`, `src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

**Deliverables (ALL work on arbitrary-size subtrees without raw giant-tree SMT!):**
1. **Abstract-certified bit-slice & shift collapses (run in `dag_bottom_up_simplify` even when `minimal = true` and `cost !result > 512`!):**
   - `restrict(0, hi) (X << k)` where `k` is a constant `> hi` $\to$ `zeros (hi + 1)` (certified via 1-var abstract equality `restrict(0, hi) (a << k) == 0` -> `< 0.5 ms`!)
   - `(uext(w - k, restrict(0, k - 1, X))) & C` (or commuted) where `amount = w - k > 0` and `(C & ((1 << k) - 1)) == 0` $\to$ `zeros w` (1-var abstract equality!)
   - `restrict(0, hi) (X | C)` when `(C & mask) == 0`, `restrict(0, hi) (X ^ C)` when `(C & mask) == 0`, `restrict(0, hi) (X & C)` when `(C & mask) == mask`, `restrict(0, hi) (X + C)` when `(C & mask) == 0` (where `mask = (1 << (hi + 1)) - 1`) $\to$ `restrict(0, hi) X` (1-var abstract equality!)
   - `restrict(0, hi) (uext(amt) Y)` when `E.sizeof Y >= hi + 1` $\to$ `restrict(0, hi) Y` (and `Y` itself if `E.sizeof Y = hi + 1`)!
2. **Complemented scaled-term recognition inside bitwise ops (`norm_peepholes.ml` / `norm_linear.ml`):**
   - Inside bitwise operands (or as a strictly-shrinking peephole when inside `&`, `|`, `^`), recognize `(-1) + ((-c) * X)` (and commuted / `(-1) - (c * X)`) as `~(c * X)` (certified by `linear_mba_mod2w` or 1-var abstract equality `(-1) + ((-c) * a) == ~(c * a)`!), so `(c * X) + (A & (-1 + (-c) * X))` immediately becomes `B + (A & ~B) -> A | B` (`tigress_l5/4671`, `tigress_l6/4191, 4192`, `tigress_l5/4785`!)!
3. **Complementary constant in zero-SMT `nonlinear_product_identity_candidate` (`norm_nonlinear.ml`):**
   - Recognize `((~a & C1) * (a & C2)) + ((a & C1) * (a | C1)) -> a * C1` (and commuted forms) whenever `C1` and `C2` are constants with `C2 == ~C1` (mod $2^w$), certified by the exact same zero-SMT `linear_mba_mod2w` + `ring_mod2w` proof! (Fixes `tigress_l8/5511` & `tigress_l8/2789`!)
4. **Zero-SMT final ring polish & 12-round DAG peeling (`src/greysynth/greysynth.ml`):**
   - Allow up to **12** shrinking bottom-up rounds in `dag_bottom_up_simplify` on `dag_size <= 2048` (within `4.0s` local deadline for giant DAGs).
   - Right before returning `!best` from `run_preprocessing` / `run`, if `size_of_expr !best <= 256`, run ONE fast zero-SMT `ring_polynomial_candidate` cleanup (fixes trivial post-timeout residuals like `((E - 0x11) + 0x11) -> E` in `tigress_l6/6654`!).

---

## 4. Fast, Focused Verification Gate for Round 36 (Target Wall Time: ~6–8 min!)

1. **Proof Kernel Cross-Tests (`test/proof_test.ml`):**
   - Positive AND negative Bitwuzla cross-tests for `Lsl` in `linear_mba_mod2w` and `Lsl` + `uext(restrict(0, hi))` in `semilinear_mba_mod2w` (including `lo > 0`, `sext`, and shift-under-bitwise rejection traps!).
2. **Focused Tigress Regression Tests (`test/round36_test.ml`):**
   - Verify end-to-end with `mba_proof` replay on real Tigress rows:
     - `tigress_l5/target_4671` (`-> <= 7`), `tigress_l5/target_6533` (`-> <= 5`), `tigress_l5/target_2558` (`-> <= 7`), `tigress_l5/target_3500` (`-> <= 11`), `tigress_l6/target_1739` (`-> <= 9`), `tigress_l6/target_6654` (`-> <= 9`), `tigress_l5/target_3126` (`5639 -> <= 25`), `tigress_l8/target_5511` (`400k -> <= 7`), `tigress_l8/target_1286` (`1.6M -> dramatic collapse!`).
   - Keep ALL prior tests (`make test`) 100% green and warning-clean!
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r36-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` remaining Tigress L5 cases — target: big drop in remaining count & geomean!)
   - **`datasets/hard_cases/core_hard/`** (refreshed `353` cases — includes the hardest Tigress L5–L8 & OMVLL survivors!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — must stay `62/62` established, `0` refuted, `<= 0.95x`!)
4. Record concise Round-36 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
