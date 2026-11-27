# GreySynth Round-45 Spec: General Low-k-Bit Ring Homomorphism (`restrict(0, hi)` Pushdown) + Opaque-Atom `root-linear-group` & Raised `polysim_candidate` Cost Cap

**Baseline:**
- **Corpus-Wide (32 Suites, `54,105` audited):** `99.985%` proved (`0` refutations), **`95.76%` exact `<= GT`** (`2,234` remaining `all_non_exact/`).
- **Round 44 (`6b5ecdd` / `c23a045`):** QSynth stack overflow fixed (`362 -> 54`), exact bit-0 `GF(2)` pushdown + constant-cast shift prepass (`target_547`: `3900 -> 61`), `regression_smoke` `62/62` (`54` exact, `0.7968x`).
- **Leeky 64-bit Zero-Tuning Generalization Baseline (`8e85ff8`, `1,004` 100%-disjoint unseen expressions, `0` refutations, `0` timeouts):**
  - `1,004 / 1,004` established (`12/12` controls `1.0000x`), `963 / 992` (`97.1%`) strictly reduced, **`512 / 992` (`51.6%`)** reference-size hits (`2.34x`).
  - Strictly held-out `mba-balanced-v1` (`120` cases — **NEVER inspected during development!**): `50/112` (`44.6%`, `2.26x`), `8/8` controls untouched.
  - Forensic X-ray of Leeky `dev_64` panels (disjoint from `mba-balanced-v1`) + our shrunk `Tigress L5–L8` residuals (`other_cast_slice`: `61/251` L5, `67/335` L8) pinpointed **three 100%-general algebraic upgrades** with high cross-corpus ROI:

---

## 1. Generalize Bit-0 Pushdown to Arbitrary Low-`k`-Bit Modular Ring Homomorphism (`restrict(0, hi)` for `1 <= k < w`) (`src/greysynth/norm_peepholes.ml`, `src/greysynth/norm_probes.ml`, `src/greysynth/normalization.ml`)

Just as `restrict(0, 0)` is the exact `mod 2` ring homomorphism, **`restrict(0, k-1)` (`k = hi + 1`, `1 <= k < w`) is an EXACT ring & bitwise homomorphism modulo $2^k$**:
- `restrict(0, k-1) (Cst c)` $\to$ `Cst (c mod 2^k)<k>`
- `restrict(0, k-1) (Not x)` $\to$ `Not (lowk x)`
- `restrict(0, k-1) (Unary Minus x)` $\to$ `Unary Minus (lowk x)`
- `restrict(0, k-1) (x + y)` $\to$ `(lowk x) + (lowk y)`
- `restrict(0, k-1) (x - y)` $\to$ `(lowk x) - (lowk y)`
- `restrict(0, k-1) (x * y)`:
  - If either operand is a constant `C` divisible by $2^k$ (`C mod 2^k == 0`, e.g., `0x80` for `k=7`, `0x100` for `k=8`) $\to$ **`0<k>`**!
  - Otherwise $\to$ `(lowk x) * (lowk y)`!
- `restrict(0, k-1) (x << C)` for constant `C`:
  - If `C >= k` $\to$ **`0<k>`**!
  - If `0 <= C < k` $\to$ `(lowk x) << C<k>`!
- `restrict(0, k-1) (x & y)`:
  - If either operand is a constant `M` with `M mod 2^k == 0` (e.g., `0xffffffffffffff80` for `k=7`) $\to$ **`0<k>`**!
  - Otherwise $\to$ `(lowk x) & (lowk y)`!
- `restrict(0, k-1) (x | y)`:
  - If either operand is a constant `M` with `M mod 2^k == 2^k - 1` $\to$ **`fill<k>`**!
  - Otherwise $\to$ `(lowk x) | (lowk y)`!
- `restrict(0, k-1) (x ^ y)` $\to$ `(lowk x) ^ (lowk y)`
- `restrict(0, k-1) (Uext _ x)` or `Sext _ x` when `E.sizeof x >= k` $\to$ `lowk x`!
- `restrict(0, k-1) (Restrict { lo = 0; hi = hi2 } x)` when `hi2 >= hi` $\to$ `lowk x`!
- Any other leaf `t` $\to$ `Restrict { lo = 0; hi = k - 1 } t` (width `k`!).

**Implementation (`lowk_restrict_homomorphism_candidate`, generalizing Round 44's `bit0_restrict_homomorphism_candidate`):**
- Trigger on `E.Unary { f = E.Restrict { lo = 0; hi }; x = inner; _ }` (or `E.Unary { f = E.Uext amount; x = E.Unary { f = E.Restrict { lo = 0; hi }; x = inner; _ }; _ }`) for ANY `0 <= hi < E.sizeof inner - 1` when `cost inner >= 3` and `dag_size_bounded ~limit:1024 inner <= 1024`.
- **When `hi = 0`:** keep Round 44's exact `GF(2)` rules (`+`/`-` $\to$ `^`, `*` $\to$ `&`, `unary -` $\to$ `id`) and 1-bit `linear_mba_mod2w` minimization!
- **When `hi > 0` (`k = hi + 1`):**
  - Push `restrict(0, hi)` down DAG-memoized (`Nodes.t`), applying immediate `k`-bit annihilations (`0 + a -> a`, `a - 0 -> a`, `0 * a -> 0`, `0 & a -> 0`, `fill & a -> a`, `0 | a -> a`, `fill | a -> fill`, `0 ^ a -> a`, `a ^ a -> 0`, `a - a -> 0`).
  - Only propose a rewrite when pushing `lowk` actually eliminates dead high-bit terms (e.g. annihilates a `* C`, `<< C`, `& M`, or `| M` subtree, OR reduces `cost` strictly after optional zero-SMT `ring_polynomial_candidate` / `linear_candidates` cleanup on the `k`-bit result!).
  - **Compositional proof (identical to Round 44, `< 2 ms` per operator schema!):**
    - Emit each local 1-step equality `(restrict(0, hi) (op a b), op (restrict(0, hi) a) (restrict(0, hi) b))` — abstracted automatically by `abstract_pair`!
    - For annihilating steps (`a * C` where $2^k \mid C$, `a << C` where $C \ge k$, `a & M` where $M \bmod 2^k = 0$), use the same two-step bridge `(restrict(0, hi) (a * C), (restrict(0, hi) a) & 0<k>)` (abstracted over `a` in `1 ms`!) + `linear_mba_mod2w` `((restrict(0, hi) a) & 0<k>, 0<k>)`!
    - Emit ONE `ring_mod2w` / `linear_mba_mod2w` equality for the final `k`-bit simplification!
    - **Note:** If `cost (uext(...) simplified) < cost original`, also check whether `uext(w - k) (restrict(0, k-1) simplified)` simplifies even further to `simplified_wide & (2^k - 1)` when smaller!
- Wire into `dag_bottom_up_simplify` (in bounded-SMT mode, counting into `smt_spent`) and `local_candidates`.

---

## 2. Opaque-Atom `run_root_linear_group` + Raise `polysim_candidate` Cap (`src/greysynth/greysynth.ml`, `src/greysynth/norm_nonlinear.ml`, `src/greysynth/norm_probes.ml`)

1. **Allow opaque atoms in `run_root_linear_group` (`src/greysynth/greysynth.ml`):**
   - Currently `run_root_linear_group` checks `Normalization.linear_mba_compatible !best`, which rejects ANY expression containing nonlinear opaque atoms like `(x2 - x0) * (x0 | x1)` or masked constants `0xa972... & x1` — causing `mba-frontier64-v1` (`2k–3k` nodes, `3/96`!) to skip `root-linear-group` completely!
   - Remove the leaf-only `linear_mba_compatible` precondition (replace with `size_of_expr !best >= 15 && dag_size_bounded ~limit:2048 !best <= 2048`): `Normalization.linear_candidates ~max_atoms:8` ALREADY collects opaque atoms cleanly and returns `[]` in `< 1 ms` if the expression is not a `<= 8`-atom linear MBA, and `Rewrite.accepts_compositional ~linear_mba_equalities` certifies it with **ZERO SMT**!
   - Also in `dag_bottom_up_simplify` (`normalization.ml:230`): when `not minimal && dag_size_bounded ~limit:1024 !result <= 1024`, allow `max_atoms = 6` up to `cost !result <= 4096` (up from `512`!) — since `linear_candidates` is DAG-memoized and zero-SMT!
2. **Raise `polysim_candidate` cost cap in `nonlinear_poly_candidate` (`src/greysynth/norm_nonlinear.ml:237`):**
   - Currently `polysim_candidate` is gated at `cost expression <= 2048 && dag_size_bounded ~limit:256 expression <= 256`!
   - `mba-stress64-v1` (`0/96`!) has `2,807–14,495`-node 3-variable nonlinear polynomial MBAs that just missed the `2,048` cap despite tiny DAGs and `<= 32` atoms!
   - Raise the gate in `nonlinear_poly_candidate` to **`cost expression <= 16_384 && dag_size_bounded ~limit:1024 expression <= 1024`** (remember `polysim_candidate` is now 100% DAG-memoized with explicit `1_000_000` op cap and `64`-monomial cap, and certifies with **ZERO SMT** via `linear_mba_mod2w` + `ring_mod2w`!).
   - Also in `greysynth.ml:344` (`run_root_minterm_poly`): make sure `nonlinear_poly_candidate` runs cleanly on `257 .. 32_768` expressions with `dag_size <= 2048`.
3. **Add `attempt_maximal_repeated` fallback in `probe_opaque_atoms` (`src/greysynth/norm_probes.ml`):**
   - In `mba-extra-floor-v1` (`35.2%`), an opaque subterm `A = (x4 * (x2 | x3)) ^ (x0 - x1)` (contains bitwise ops!) is wrapped in a 2-atom semi-linear shell `(2 * ((B | 2) & A)) + ... == A + 2` where `B = (A & x5) ^ x6`.
   - When `attempt_arithmetic_atoms`, `attempt_shared_boundary`, and `attempt_operator_boundary` all return `None`, try one clean fallback `attempt_maximal_repeated`:
     - Pick the maximal (outermost, non-root, `cost >= 5`, `freq >= 2`, same width) repeated subexpressions that don't overlap; if stopping at those plus remaining non-shell leaves yields `1 <= count <= 3` atoms, run the exact same `{0,1}^k` / 1-var XSMIR / 2-var offset probe + 24 full-width sample check + `samples_agree` pre-filter!

---

## 3. Verification Gate for Round 45 (Target Wall Time: ~8–10 min!)

1. **Unit & Regression Tests (`test/round45_test.ml`):**
   - End-to-end tests with independent `mba_proof` replay covering:
     - Low-`k`-bit modular pushdown (`k = 7` and `k = 8`): `uext(57) (restrict(0, 6) (((x0 ^ x2) + x1) * 0x80 + ((0x80 * x3) + x1))) -> uext(57) (restrict(0, 6) x1)` (or `x1 & 0x7f`), proved compositionally in `< 0.1s`!
     - Opaque-atom `root-linear-group` on a `> 1,000`-node linear MBA over 4 opaque nonlinear/masked atoms (zero-SMT `linear_mba_mod2w`!).
     - `polysim_candidate` on a `> 2,500`-cost 3-variable nonlinear MBA (`mba-stress64`-style, zero-SMT `linear_mba_mod2w` + `ring_mod2w`!).
     - `attempt_maximal_repeated` opaque probe on a bitwise-containing repeated subterm `A = (x4 * (x2 | x3)) ^ (x0 - x1)` wrapped in a semi-linear `+ 2` shell!
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain JSONLs under `/tmp/r45-*/out.jsonl`):**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases, **NOT touching held-out `mba-balanced-v1`!** -> `/tmp/r45-leeky-dev64/out.jsonl` — report per-panel jumps on `mba-ladders-v1`, `mba-frontier64-v1`, `mba-stress64-v1`, `mba-extra-floor-v1`, etc.!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r45-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r45-core/out.jsonl`)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases -> `/tmp/r45-smoke/out.jsonl` — must stay `62/62`, `0` stalls, `0` refuted, `<= 0.80x`!)
3. Record concise Round-45 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `src/proof/rewrite_proof.ml`).
