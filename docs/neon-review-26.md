# GreySynth Round-26 Spec: Analytical XSMIR 10-Rule Local Interpolation, Cache-Free Exact Small-Tree Enumeration & ProMBA AC-Pairwise / Generalized Lemma Learning

**Baseline:** Round 25 (`semilinear_mba_mod2w`, $2^k$-pullout, demand-bit width narrowing, alternation-reducing proof bridge)  
**Sources (from `docs/LITERATURE_ANALYSIS.md`):**
- **XSMIR / SMIR** (Attias et al., CCS '25, `2025-ccs.md`, Tables 4, 13, 17) — 9 Analytical Local Inference Rules + `XSMIR-min` (flat 89.4%/88.9%/88.9% across Tigress L1–L3; `min` combinator +8.9 ppt & 2.1× faster with 0% FP behind our proof gate!)
- **GPU-SIMBA: Beyond Caching** (Bathie et al., `2605.08243v1.md`, §3.1–3.2) — Cache-free locally consistent RPN/small-tree enumeration hoisting left-subtree sample vectors
- **ProMBA** (Lee & Lee, CCS '23, `ccs23.md`, §3.4–3.6) — AC-flattened pairwise synthesis & on-the-fly verified rule generalization (`GeneralizeRule`: jumped success 58% → 84%, 3× smaller!)

**Primary targets:**
- **`datasets/hard_cases/all_failing/tigress_l5..l8/`** (depth-invariant analytical constant/affine/shift/mask recovery!)
- **`datasets/hard_cases/all_failing/qsynth_ea/`** (60 weak cases) & **`datasets/hard_cases/all_failing/loki/`** (144 weak) & **`floki/`** (19 weak)
- **`datasets/hard_cases/core_hard/`** (413 cases) & **`datasets/hard_cases/regression_smoke/`** (62 guards)

---

## 1. Pure-OCaml Analytical XSMIR 10-Rule Interpolator (`src/greysynth/smir_interp.ml`, `.mli`)

Instead of calling external random-search Xyntia (which wastes 1s per attempt and collapses when arbitrary 64-bit constants or masks appear), build a **zero-process, microsecond pure-OCaml analytical interpolator** (`Smir_interp`):

Given a target bitvector output array `ys : Z.t array` (length $n \ge 8$, width $w \le 64$, mask $M = 2^w - 1$) and any candidate expression `e` with sample evaluation array `es : Z.t array`:
1. **Exact match:** `forall i, es.(i) = ys.(i)` $\implies e$.
2. **Additive constant $\mathcal{R}^+$:** `c = (ys.(0) - es.(0)) & M`; if `forall i, ((es.(i) + c) & M) = ys.(i)` $\implies e + c$.
3. **XOR constant $\mathcal{R}^\oplus$:** `c = ys.(0) ^ es.(0)`; if `forall i, (es.(i) ^ c) = ys.(i)` $\implies e \oplus c$.
4. **Multiplicative constant $\mathcal{R}^\times$:** find any `i` with `es.(i)` odd, compute `c = (ys.(i) * inv(es.(i), 2^w)) & M`; if `forall j, ((c * es.(j)) & M) = ys.(j)` $\implies c \cdot e$.
5. **AND-OR bitmask $\mathcal{R}^{\wedge\vee}$ (CCS '25 Table 4):**
   - `z_y = OR_i ys.(i)`, `o_y = AND_i ys.(i)`, `z_e = OR_i es.(i)`, `o_e = AND_i es.(i)`
   - `c_and = z_y | (M ^ z_e)`, `c_or = o_y & (M ^ o_e)`
   - If `forall i, ((es.(i) & c_and) | c_or) = ys.(i)` $\implies$ emit compact form (omitting `& M` or `| 0`!).
6. **Affine $\mathcal{R}^{\text{Affine}}$:** find pair `(i, j)` with `(es.(i) - es.(j))` odd; compute:
   $$a = (y_i - y_j) \cdot (e_i - e_j)^{-1} \bmod 2^w, \qquad b = (y_i - a \cdot e_i) \bmod 2^w$$
   If `forall k, ((a * es.(k) + b) & M) = ys.(k)` $\implies a \cdot e + b$.
7. **Quadratic univariate polynomial $\mathcal{R}^{\text{Poly2}}$:** find 3 samples `(i, j, k)` whose pairwise differences `e_i - e_j`, `e_j - e_k`, `e_i - e_k` are odd (or solve 2-adic Vandermonde system via exact modular elimination!) to recover $c_2 e^2 + c_1 e + c_0 \pmod{2^w}$ and check `forall m`!
8. **Rotate right $\mathcal{R}^{\text{ror}}$:** for $k = 1 \dots w - 1$, check `forall i, ror(es.(i), k) = ys.(i)` $\implies e \text{ ror } k$.
9. **Logical left shift $\mathcal{R}^{\ll}$:** for $k = 1 \dots w - 1$, check `forall i, lsl(es.(i), k) = ys.(i)` $\implies e \ll k$.
10. **Logical & arithmetic right shifts $\mathcal{R}^{\gg}, \mathcal{R}^{\gg_s}$:** for $k = 1 \dots w - 1$, check `lsr` and `asr` $\implies e \gg k$ / $e \gg_s k$.
- **Bonus fast constant-free check:** Before checking candidate expressions, check if `ys` is constant (`ys.(0)` for all `i`) $\implies$ constant `ys.(0)`.
- **Strict safety:** `Smir_interp` is a **100% untrusted candidate generator** — EVERY proposed candidate MUST pass full `Rewrite.accepts` (all concrete samples + `mba_proof` / decidable kernel or SMT proof!) and strict size reduction `size_of_expr cand < size_of_expr original`!

---

## 2. Deterministic Cache-Free Locally Consistent Small-Tree Enumerator + OES Elevation (`src/greysynth/smir_interp.ml`, `src/greysynth/synthesis.ml`, `src/greysynth/oes.ml`)

1. **Cache-Free Locally Consistent Exact Small-Tree Enumerator (`Smir_interp.synthesize_exact`):**
   - Hook into `Synthesis.synthesize` **BEFORE** calling external Xyntia (`run_backend`)!
   - Uses the problem's fast sample array (first 16 samples as a pre-filter, then verifies on ALL problem samples before returning!).
   - **Operator-stratified subset** (QSynth/Xyntia RQ6):
     - Unary ops: `~`, `-`
     - Binary ops: `+`, `-`, `*`, `&`, `|`, `^` (adding `<<`, `>>`, `>>s` ONLY if `problem.operators.shifts` is true; `/` / `%` ONLY if `problem.operators.division` is true!).
   - **Locally consistent enumeration of core ASTs up to size 5** (hoisting left subtree `e_L`'s 16-sample vector in a local variable while sweeping `e_R` in the inner loop, with strict canonical symmetry breaking: commutative ops only for `id_L <= id_R`, pruning `~(~e)`, `-(-e)`, `e^e`, `e-e`, `e&e`, `e|e`!):
     - Size 1: each input variable `v_0 .. v_{k-1}` (immediately tested with ALL 10 XSMIR rules -> instantly solves ANY 1-var affine/mask/shift/rotate/quadratic expression like `c1*x + c2`, `(x & M) | C`, `x ror k`, `c2*x^2 + c1*x + c0` in **< 0.1 ms**!).
     - Size 2: `~v_i`, `-v_i` (with all 10 XSMIR rules!).
     - Size 3: `v_i op v_j` (with all 10 XSMIR rules -> instantly solves `c1*(x ^ y) + c2`, `((x + y) & M) | C`, `(x * y) ror k`, `(x - y) << k` in **< 0.5 ms**!).
     - Size 4–5 (for `k <= 3` vars, capped at e.g. 1,500 candidates / 25 ms per CHS call!): `(v_i op v_j) op2 v_m` and `op1(v_i op v_j)` with direct match + fast XSMIR rules (`+`, `^`, `and-or`, `affine`, `ror`/`<<`/`>>`)!
   - **Result:** For the vast majority of CHS local horizons on `Tigress L5–L8`, `QSynth EA`, and `Loki`, `Smir_interp.synthesize_exact` finds the **exact minimum-size solution in < 5 ms** without EVER spawning Xyntia or burning a 1-second random search timeout!
2. **OES + XSMIR Single-Node Elevation (Optional Fast Hook in `Oes` / `Normalization`):**
   - When OES scans unique DAG nodes (`size >= 5`), for any small repeated descendant `rep` (size `<= 3`) inside a larger node `n`, test the 10 XSMIR rules linking `rep` $\to$ `n` (cost: microseconds, zero search!) — instantly collapsing obfuscated wrappers like `n = c1 * rep + c2` or `n = (rep & M) | C` or `n = rep ror k` in one shot!

---

## 3. ProMBA AC-Flattened Pairwise Synthesis & On-the-Fly Verified Rule Generalization (`src/greysynth/synthesis.ml`)

1. **ProMBA `GeneralizeRule` (CCS '23 §3.4):**
   - Currently `Synthesis.synthesize` caches `canonical_rule_pair e (Some result)` only when `e` matches the exact syntactic shape of a previous truncated window.
   - Upgrade: whenever `synthesize` proves a local rewrite `lhs -> rhs` with `size rhs < size lhs`, also extract a **generalized template** by finding non-variable maximal subexpressions that occur in **both** `lhs` and `rhs` (replacing each identical shared subexpression across both `lhs` and `rhs` with the same fresh rule variable `$r_i`), verify the generalized identity `gen_lhs == gen_rhs` ONCE with fast SMT (`timeout = 0.2s` — takes `< 2 ms` on tiny windows!), and if proved `Yes`, store `(gen_lhs, gen_rhs)` in `universal_rules`!
   - **Soundness:** Rejects unsound generalizations (like ProMBA's `(a & b) & (b & a) -> (a & b) & b` generalizing to `x & (b & a) -> x & b`) because the generalized rule MUST pass independent SMT proof!
2. **ProMBA AC-Flattened Pairwise Cancellation (CCS '23 §3.6):**
   - In `simplify_with_horizon`, when a node `n` is an associative-commutative chain `t_1 op t_2 op ... op t_m` (`op` in `{+, *, &, |, ^}`, `3 <= m <= 10`) and whole-node synthesis did not shrink `n`:
   - Flatten the chain into `[t_1; ...; t_m]`, prioritize pairs `(t_i, t_j)` that share at least one variable (capped at e.g. 12 pairs per node!), and run our ultra-fast `Smir_interp.synthesize_exact` + `Normalization.local_candidates` on `t_i op t_j`!
   - If a pair `(t_i op t_j)` simplifies strictly to `s` (certified via `Rewrite.accepts`!), replace the pair in the chain with `s` and emit the congruence/AC `ring_mod2w`/`smt` proof edge!
   - Directly targets non-adjacent cross-term cancellations in **`Loki`**, **`QSynth EA`**, and **`Tigress L5–L8`**!

---

## 4. Fast, Focused Verification Gate for Round 26 (Target Wall Time: ~4–6 min!)

1. **Unit & Soundness Tests (`test/round26_test.ml`, `test/pipeline_test.ml`):**
   - Test ALL 10 analytical XSMIR rules (`+`, `^`, `*`, `and-or`, `affine`, `poly2`, `ror`, `lsl`, `lsr`, `asr`) on 32-bit and 64-bit arbitrary constants/masks/rotates, verifying deterministic sub-millisecond recovery AND strict `mba_proof` replay!
   - Test cache-free exact small-tree enumerator on compound Beyond-MBA patterns (`((x ^ y) * 0xdeadbeef12345679) + 0xc0de`, `((x + y) & 0x00ff00ff) | 0x01000000`, `(x ^ y) ror 13`).
   - Test ProMBA `GeneralizeRule` rejects unsound generalizations AND caches sound generalized templates across distinct subtrees without re-running synthesis.
   - Test AC-flattened pairwise cancellation on non-adjacent sum terms (e.g., `-5*y + 9*(~x) + 5*(x & y) + x*y`).
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/all_failing/qsynth_ea/`** (60 weak cases)
   - **`datasets/hard_cases/all_failing/loki/`** (144 weak cases) & **`floki/`** (19 weak cases)
   - **`datasets/hard_cases/all_failing/tigress_l5/`** (23 weak) & **`datasets/hard_cases/core_hard/`** (413 hardest cases across all suites — excluding or noting the 6 pre-existing >80 MB OMVLL files!)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted!)
4. Record concise Round-26 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
