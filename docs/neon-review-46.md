# GreySynth Round-46 Spec: Associative Scalar & AC-Factor Extraction in `norm_linear.ml` + `dag-linear-mba` Phase-Ordering + Small-Root Low-k Pushdown

**Forensic Diagnosis of Round-45 `dev_64` & `core_hard` Residuals (Three 100%-General Algebraic Unlocks, Zero Proof-Kernel Changes!):**

1. **Why `mba-frontier64-v1` (`3/96`, `22.7x`) stalled at `in == out` (`2,025–3,021` nodes):**
   - Inspecting `2dda45799bcf74a9_w64` (`in = 2,025`, `ref = (((25 & x1) ^ x2) + (18 | x0))`) revealed that every 400-node zero-identity sub-MBA over only **4 atoms** failed because scalar constants were nested *inside* products:
     - `((x0 - x1) * (18446744073709551580 * (x1 | x2)))` instead of `18446744073709551580 * ((x0 - x1) * (x1 | x2))`!
   - `norm_linear.ml` only checked top-level `Mul (Cst k, y)` / `Mul (x, Cst k)`, treating `a * (k * b)` as an unrelated opaque atom different from `a * b`!
   - And `ring_polynomial_candidate` rejected `a * (k * b) -> k * (a * b)` because both have equal cost (`5 == 5`)!
2. **Why `mba-stress64-v1` (`7a3c5b5205027e63_w64`, `in = 3,066`, `ref = 24`, `candidates = 1, inconclusive = 1, t = 5.00s`) timed out:**
   - Its AST is a sum of products of **`78–111`-node linear MBAs**!
   - Inside `dag_bottom_up_simplify` (`src/greysynth/normalization.ml`), `nonlinear_poly_candidate` (`minterm_ring_poly_candidate` / `polysim_candidate`) ran **BEFORE** `dag-linear-mba` — trying to expand a degree-6 polynomial of unsimplified `100`-node linear MBAs and burning the entire `5.0s` budget before `dag-linear-mba` ever collapsed the `80`-node factors to `3` nodes!
3. **Why `mba-ladders-v1` (`84–101` nodes, `58.3%`) skipped Round 45's `lowk_restrict_homomorphism_candidate`:**
   - `84–101 <= 128` (`dag = 60 <= 128`) bypassed BOTH `dag_bottom_up_simplify` (`size > 256 || dag > 128`) AND `Egraph` (`size > 128`), and `Normalization.run` never called `lowk_restrict_homomorphism_candidate`!
   - Plus `lowk_restrict_homomorphism_candidate` should ALSO recognize `(inner & mask)` where `mask = 2^k - 1` (`1 <= k < w`) directly (not only `uext(w-k)(restrict(0, k-1) inner)`!).
4. **Why `mba-proof-context-v1` (`33.3%`) stalled on `((M + B) & C) | ((B + M) & (~C))`:**
   - The two bitwise atoms `M + B` and `B + M` are ring-identical (`ring_mod2w`), differing only in operand order, so `norm_linear.ml` treated them as two distinct atoms instead of unifying them via a zero-SMT `ring_mod2w` edge!

---

## 1. Associative Scalar Extraction & Commutative Atom Unification in `norm_linear.ml` (`src/greysynth/norm_linear.ml`, `src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

**100% Zero-SMT, Zero Changes to `src/proof/rewrite_proof.ml`!**

1. **Extract nested scalar factors from products in `linear` (`norm_linear.ml`):**
   - Write a small helper `extract_product_scalar width expr -> (Z.t * E.t) option`:
     - Recursively collects multiplicative factors through `E.Mul` and `E.Unary E.Minus` (only walking associative `Mul` / unary `Minus`, DAG-safe):
       - Constant factors multiply into `coeff : Z.t` (mod $2^w$), unary `Minus` negates `coeff`, non-constant factors collect into `factors : E.t list`.
     - If `factors` has `>= 2` items AND (`not (Z.equal coeff Z.one)` OR `factors` are out of canonical `E.compare` order):
       - Sort `factors` canonically (`List.sort E.compare factors`) and rebuild `base = build_balanced E.Mul factors` (or `List.fold_left (E.binary E.Mul)`).
       - Construct `rewritten = scale coeff base` (e.g. `k * (a * b)`).
       - Record the zero-SMT `ring_mod2w` edge `(expr, rewritten)` in `ring_edges`!
       - Return `Scale (coeff, atom base)` in `linear`!
   - **Example:** `((x0 - x1) * (18446744073709551580 * (x1 | x2)))` $\to$ `ring_edges += (orig, 18446744073709551580 * ((x0 - x1) * (x1 | x2)))`, and `linear` sees `Scale (-36, atom ((x0 - x1) * (x1 | x2)))` — matching the exact same atom as `((x0 - x1) * (x1 | x2))`!
2. **Unify AC-equivalent additive/multiplicative bitwise atoms (`mba-proof-context-v1`!):**
   - Inside `atom expression` in `norm_linear.ml`: when `expression` is a top-level `E.Binary { f = (E.Plus | E.Mul); x; y; _ }` with `E.compare y x < 0` (e.g. `B + M` vs `M + B`, or `b * a` vs `a * b`):
     - Canonicalize to `canon = E.binary f y x`, record the zero-SMT `ring_mod2w` edge `(expression, canon)`, and intern `canon` as the atom!
   - Also canonicalize `a + (b + c)`? Even simpler: just sorting top-level `E.Plus` / `E.Mul` operands (up to 4 flat additive/multiplicative operands via `ring_mod2w`) unifies `(M + B)` with `(B + M)` and `(a + (b + c))` with `((a + b) + c)` in `< 0.01 ms` with ZERO SMT!
3. **Propagate `ring_edges` into `Rewrite.accepts_compositional`:**
   - Expose `linear_candidates_with_rings` (returning `(candidate, ring_edges, rewritten_source) list`, where `ring_edges` bridges `original -> substituted_source` via `ring_mod2w` and `[substituted_source, candidate]` is proved via `linear_mba_mod2w`!) while keeping `linear_candidates` as a thin compatibility wrapper where needed.
   - Use `linear_candidates_with_rings` in `dag_bottom_up_simplify` (`dag-linear-mba`), `run_root_linear_group` (`root-linear-group`), and `Normalization.run`!
   - **Wait — double-check congruence closure!** When `ring_edges` contains `(orig_mul_1, k1 * base)`, `Rewrite_proof` congruence closure automatically rewrites `original` into `substituted_source` (replacing every `orig_mul_i` with `k_i * base`), and `linear_mba_mod2w` proves `(substituted_source, candidate)` — **ZERO SMT, 100% independently replayed by `mba_proof`!**

---

## 2. Phase-Order Fix in `dag_bottom_up_simplify` & `run_preprocessing` (`src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

1. **Move `dag-linear-mba` (and `dag-semilinear-mba`) BEFORE `nonlinear_poly_candidate` inside `dag_bottom_up_simplify`:**
   - In `src/greysynth/normalization.ml`: run the cheap, fast zero-SMT linear/semilinear peel (`dag-product-peel`, `dag-linear-mba`, `dag-semilinear-mba`) **BEFORE** `nonlinear_poly_candidate` (`minterm_ring_poly_candidate` + `polysim_candidate`)!
   - That way, any product of linear MBAs (`mba-stress64-v1`: `80`-node linear factors inside `*`) collapses every linear factor to `~3` nodes BEFORE `nonlinear_poly_candidate` or `ring_mod2w` ever touches the outer product!
2. **In `run_preprocessing` (`src/greysynth/greysynth.ml`):**
   - Run the fast zero-SMT `dag_bottom_up_simplify ~zero_smt:true` fixpoint pass (when `size_of_expr !best > 512 && dag_size_bounded ~limit:4096 !best <= 4096`) **BEFORE** `run_root_minterm_poly ()` (currently `run_root_minterm_poly` runs at line 370 *before* `dag_bottom_up_simplify ~zero_smt:true`, causing `mba-stress64-v1` `3,066`-node expressions to burn 5.0s in a single root `minterm_ring_poly` expansion before their `80`-node linear children are simplified!!).

---

## 3. Wire `lowk_restrict_homomorphism_candidate` into `Normalization.run` + Mask `(inner & (2^k - 1))` Support (`src/greysynth/norm_peepholes.ml`, `src/greysynth/normalization.ml`)

1. **Support low-bit mask `(inner & (2^k - 1))` directly in `lowk_restrict_homomorphism_candidate` (`src/greysynth/norm_peepholes.ml`):**
   - In addition to `restrict(0, hi) inner` and `uext(w-k)(restrict(0, hi) inner)`, also match `E.Binary { f = E.And; x = inner; y = E.Cst m; _ }` (and commuted `Cst m & inner`) whenever `m = (1 << k) - 1` (`1 <= k < w`) and `cost inner >= 5`!
   - Bridge `(inner & m) == uext(w - k) (restrict(0, k - 1) inner)` via a 1ms abstract equality (or `semilinear_mba_mod2w`!), push `restrict(0, k - 1)` down through `inner` annihilating `* C` ($2^k \mid C$), `<< C` ($C \ge k$), `& M` ($M \bmod 2^k = 0$), and return the strictly cheaper `uext(w - k) simplified_k` (or `simplified_wide & m` when smaller)!
2. **Wire `lowk_restrict_homomorphism_candidate` into `Normalization.run` (`src/greysynth/normalization.ml`):**
   - Inside `Normalization.run`'s `visit` (alongside `decomposed` / before `peepholes`), invoke `lowk_restrict_homomorphism_candidate` when `cost !current >= 5 && cost !current <= 256` (with a modest `0.4s` per-run SMT cap so it can never slow down large runs!).
   - Immediately solves `mba-ladders-v1` (`84–101`-node roots `<= 128` that previously skipped both `dag_bottom_up_simplify` and `Egraph`!) AND small `restrict(0, hi)` subtrees across `Tigress L5–L8` and `OMVLL`!

---

## 4. Verification Gate for Round 46 (Target Wall Time: ~8–10 min!)

1. **Unit & Regression Tests (`test/round46_test.ml`):**
   - End-to-end tests with independent `mba_proof` replay covering:
     - Associative scalar extraction in `norm_linear.ml`: a linear MBA containing both `((x0 - x1) * (x1 | x2))` and `((x0 - x1) * (k * (x1 | x2)))` collapsing with **ZERO SMT** (`ring_mod2w` + `linear_mba_mod2w`)!
     - AC atom unification: `(((x0 + x1) & x2) | ((x1 + x0) & (~x2))) -> (x0 + x1)` with **ZERO SMT**!
     - `mba-stress64`-style sum of products of linear MBAs (`dag-linear-mba` before `nonlinear_poly_candidate`!) collapsing cleanly in `< 0.5s`!
     - Small-root (`<= 128`) `lowk_restrict_homomorphism_candidate` on `((0xffffffffffffff80 & x0) - ((((x0 ^ x2) + x1) * 0x80 + x1) & 127))` via `Normalization.run`!
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain JSONLs under `/tmp/r46-*/out.jsonl`):**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases — **still keeping `heldout_balanced64/` (`mba-balanced-v1`) strictly untouched!** -> `/tmp/r46-leeky-dev64/out.jsonl` — target: massive jumps on `mba-frontier64-v1`, `mba-stress64-v1`, `mba-ladders-v1`, and `mba-proof-context-v1`!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r46-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r46-core/out.jsonl`)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases -> `/tmp/r46-smoke/out.jsonl` — must stay `62/62`, `0` stalls, `0` refuted, `<= 0.80x`!)
3. Record concise Round-46 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `src/proof/rewrite_proof.ml`).
