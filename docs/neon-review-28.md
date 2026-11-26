# GreySynth Round-28 Spec: Black-Box Semantic Interpolation (`{0,1}^k` Linear & `{0..d}^k` Newton–Mahler Probing) & Cross-Branch Semantic DAG CSE (`Loki` / `gMBA`)

**Baseline:** Round 27 (GAMBA shared-factor grouping, complete SiMBA/GAMBA linear reconstruction, cast canonicalization & branchless-ITE lifting)  
**Sources (from `docs/LITERATURE_ANALYSIS.md`):**
- **gMBA** (Noh et al., Findings of ACL '25, `2025.findings-acl.1127.md`) — Extended $\{0, 1\}^n \to \mathbb{Z}/2^w\mathbb{Z}$ semantic truth-table probing recovers exact arithmetic coefficients independent of syntactic nesting!
- **BAR '24** (`bar2024-14-paper.md`) — Finite-difference / Newton–Mahler interpolation on $\{0, \dots, d\}^k$ recovers exact low-degree modular polynomials directly from semantics!
- **Loki** (Schloegel et al., USENIX Security '22, `sec22-schloegel.md`) — Cross-branch concrete-fingerprint DAG CSE (defeating independent per-copy MBA rewriting of duplicated SSA superoperators) & semantic `0/1`/constant dead-branch pruning through nonlinear masks!

**Primary targets:**
- **`datasets/hard_cases/all_failing/tigress_l5..l8/`** (deeply layered `Tigress L5–L8` where syntactic passes stall on depth!)
- **`datasets/hard_cases/all_failing/loki/`** & **`loki_tiny/`** (duplicated SSA superoperators & dead branches!)
- **`datasets/hard_cases/all_failing/omvll/`** (non-GB) & **`pldi_poly/`** & **`core_hard/`** (406 non-GB) & **`regression_smoke/`** (62 guards)

---

## 1. Black-Box `{0, 1}^k` Semantic Linear-MBA Probing on Arbitrary Nested Sub-DAGs (`src/greysynth/smir_interp.ml`, `src/greysynth/normalization.ml`)

Today `linear_candidates` only runs on expressions that are *syntactically* flat linear MBAs. When an obfuscator wraps a linear MBA inside `f^{-1}(f(e))`, nonlinear zero identities, deep `Tigress L6–L8`, or `Loki` superoperators, syntactic linearity fails immediately.

**Exact algorithm (`probe_semantic_linear_mba`):**
1. Given an arbitrary sub-DAG `e` (`size_of_expr e >= 5`, `dag_size_of_expr e <= 2048`, `1 <= k <= 4` free variables all of width `w <= 64`, not containing memory loads):
2. Evaluate `e` directly (DAG-memoized!) on all $2^k \le 16$ Boolean corner inputs $\{0, 1\}^k \subseteq (\mathbb{Z}/2^w\mathbb{Z})^k$ (taking `< 0.2 ms`).
3. Pass the resulting length-$2^k$ signature vector `target` directly into our **Round 27 SiMBA/GAMBA structured linear-MBA reconstructor** to generate the smallest candidate `cand` with `size_of_expr cand < size_of_expr e`!
4. **Fast full-width pre-filter (microseconds):** Test `cand` against 8 random full-width $w$-bit inputs (plus corner inputs `0, 1, -1, 0x5555...`). If ANY sample disagrees, discard immediately (zero solver cost!).
5. **Strict proof gate (`0%` FP):** If all full-width samples agree, certify `e == cand` via `Rewrite.accepts` (which automatically leverages our Round 25 alternation-reducing proof bridge, decidable kernels, or bounded SMT — **never accepting unproved candidates!**).
- Hook into:
  - Early root fast path in `greysynth.ml` (for roots with `1 <= k <= 4` and `dag_size <= 2048` — instantly catches obfuscation-depth-invariant linear MBAs across `Tigress L5–L8` & `Loki`!)
  - Bottom-up `dag_bottom_up_simplify` on unique sub-DAGs of `dag_size` in `[5 .. 512]` (bounded budget per expression, e.g. at most 32 semantic probes per expression!)
  - Inside `Smir_interp.synthesize_exact` on CHS truncated windows (where `k <= 4` Greek stubs act as variables!).

---

## 2. Black-Box `{0..d}^k` Newton–Mahler Polynomial Probing (`src/greysynth/smir_interp.ml`, `src/greysynth/normalization.ml`)

Extend black-box semantic probing from linear MBAs (`{0, 1}^k`) to **low-degree univariate & bivariate polynomials mod $2^w$** (`{0, ..., d}^k`):

**Exact algorithm (`probe_semantic_poly`):**
1. **Univariate degree $d \le 3$ ($k = 1$, 4 evaluations $f(0), f(1), f(2), f(3) \bmod 2^w$):**
   - Compute forward differences:
     - $d_0 = f(0)$
     - $d_1 = f(1) - f(0)$
     - $d_2 = f(2) - 2 f(1) + f(0)$
     - $d_3 = f(3) - 3 f(2) + 3 f(1) - f(0)$
   - Since $f(x) = c_0 + c_1 x + c_2 \binom{x}{2} + c_3 \binom{x}{3} \pmod{2^w}$ has $d_k = k! \cdot c_k \pmod{2^w}$:
     - Check $d_2$ even and $d_3$ even; divide by exact 2-adic factors (`inv(3, 2^w)` for the odd factor `3`, and right-shift by 1 for the factor `2`), noting the **1-bit MSB ambiguity** ($c_k$ vs $c_k + 2^{w-1}$) for $c_2, c_3$ (at most $2 \times 2 = 4$ candidate combinations!).
     - Check all $\le 4$ candidates against 8 full-width random $w$-bit inputs — at most ONE matches!
     - Convert the matching falling-factorial polynomial back to compact centered power basis `a_0 + a_1*x + a_2*x^2 + a_3*x^3`!
2. **Bivariate degree $d \le 2$ ($k = 2$, 6 evaluations at $(0,0),(1,0),(2,0),(0,1),(1,1),(0,2)$):**
   - $c_{00} = f(0,0)$
   - $c_{10} = f(1,0) - f(0,0)$, $c_{01} = f(0,1) - f(0,0)$
   - $c_{11} = f(1,1) - f(1,0) - f(0,1) + f(0,0)$ (exact — no division by 2!)
   - $d_{20} = f(2,0) - 2 f(1,0) + f(0,0)$ (even $\implies 2$ MSB choices for $c_{20}$), $d_{02} = f(0,2) - 2 f(0,1) + f(0,0)$ (even $\implies 2$ MSB choices for $c_{02}$).
   - Check the $\le 4$ candidates against 8 full-width random $w$-bit inputs; convert to compact power basis `a_0 + a_1*x + a_2*y + a_3*x*y + a_4*x^2 + a_5*y^2`!
3. **Strict proof gate:** If `size cand < size e`, certify `e == cand` via `Rewrite.accepts` (`poly_mod2w` / proof bridge / bounded SMT).
- Hook into early root fast path, `Smir_interp.synthesize_exact` (on CHS windows!), and bounded `dag_bottom_up_simplify`!

---

## 3. Cross-Branch Concrete-Fingerprint DAG CSE & Semantic Constant/Dead-Branch Pruning (`src/greysynth/oes.ml`, `src/greysynth/greysynth.ml`)

Loki's SSA superoperators duplicate intermediate expressions and apply *different* MBA rewrites to each copy (destroying syntactic CSE), and mask dead handler branches `e_i(k) * g_i` behind nonlinear multiplications.

**Deliverables (`semantic_dag_cse_pass`):**
1. Traverse the expression DAG bottom-up (each unique `Sexpr.BvTbl` node visited **at most once**, capped at `dag_size <= 4096`):
   - **Semantic constant / dead-branch pruning:** If `!evaluator.is_node_constant n = Some cst` and `size_of_expr n >= 3`, immediately try `Rewrite.accepts ~pass:"dag-const-prune" n (Cst cst)` (with fast decidable kernels + short SMT `<= 0.15s`). Replacing a dead sub-DAG with `0` or `-1` collapses its parent `*`/`&`/`|` immediately on the way up!
   - **Cross-branch semantic CSE:** Maintain a table `(width, outhash) -> smallest_proved_representative` across all unique DAG nodes seen so far (plus fast bottom-up rebuild so already-simplified children propagate!). Whenever a node `n` collides in `(width, outhash)` with a strictly smaller syntactically distinct node `rep` (`size_of_expr rep < size_of_expr n`), try `Rewrite.accepts ~pass:"dag-semantic-cse" n rep` (bounded at e.g. 64 non-trivial SMT proof attempts / 0.5s total budget per expression so it NEVER causes timeouts!).
2. **Important safety check (GreySynth Table 4 lesson!):** NEVER blindly trust `(width, outhash)` collisions without `Rewrite.accepts` proof verification! Every single merge MUST be independently proved and recorded in `Rewrite.journal`.

---

## 4. Fast, Focused Verification Gate for Round 28 (Target Wall Time: ~4–6 min!)

1. **Unit & Soundness Tests (`test/round28_test.ml`):**
   - Black-box `{0,1}^k` probing recovers a linear MBA wrapped inside nonlinear zero noise / nested arithmetic-in-bitwise layers, with independent `mba_proof` replay!
   - Black-box `{0..d}^k` Newton–Mahler probing recovers:
     - 64-bit univariate cubic `c_3*x^3 + c_2*x^2 + c_1*x + c_0` (including MSB disambiguation!)
     - 64-bit bivariate quadratic `3*x*y + 5*x^2 - 7*y + 42`
     - Verify negative soundness: non-polynomial function (`x & y`) is cleanly rejected by the 8-sample full-width filter without false proofs!
   - Cross-branch semantic DAG CSE collapses `((x ^ y) + 2*(x & y)) * (2*(x | y) - (x ^ y))` (two differently-obfuscated copies of `x + y`) into `(x + y) * (x + y)` with independent certificate replay, AND dead-branch pruning collapses `((x ^ x) * big_expr) + y` cleanly to `y`!
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/all_failing/tigress_l5/`** (23), **`tigress_l6/`** (84), **`loki/`** (144)
   - **`datasets/hard_cases/all_failing/loki_tiny/`** (first `--limit 100` of the 403 weak!)
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases — track exact GT & geomean!)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted!)
4. Record concise Round-28 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
