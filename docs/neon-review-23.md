# GreySynth Round-23 Spec: Arbitrary-Arity Multilinear `BitTrans` (`PolySim`), Complementary-Atom Pairing & RUMBA Theorem-20 / Null-Vector Propagation

**Baseline commit:** `4f66d43` (Rounds 19–22 complete; literature roadmap in `docs/LITERATURE_ANALYSIS.md`)  
**Benchmark harness:** Uses our newly isolated `datasets/hard_cases/` corpus (`regression_smoke/` ~60 already-solved guards across all suites + `all_failing/` + `core_hard/` ~400 hardest failing/weak cases) for fast, zero-waste feedback loops!  
**Primary targets:**
- **`datasets/hard_cases/all_failing/c_mba_obfuscator/`** (all 152 remaining weak cases, including `target_366` at `3.4M -> 28k`, GT `11`!)
- **`datasets/hard_cases/all_failing/mba_obf_nonlinear/`** (remaining nonlinear weak cases)
- **`datasets/hard_cases/core_hard/{tigress_l5..l8, omvll}/`** (deeply nested alternating MBA layers & timeouts)

---

## 1. Upgrade `linear_mba_mod2w` to Support Arbitrary-Arity Sparse Multilinear Checking (`src/proof/rewrite_proof.ml`, `.mli`)

Currently `linear_mba_mod2w` evaluates a $2^k$ truth table capped at `max_atoms = 8`. Any linear MBA or `BitTrans` identity over $9+$ opaque atoms (which occur frequently in `C-MBA-Obfuscator` Mode 1–4, `Neureduce`, and `OMVLL`) hits `linear_mba_limit_exceeded`.

**Exact mathematical theorem (MBA-Flatten Theorem 1 / Möbius Isomorphism):**
In the sparse multilinear polynomial ring $\mathcal{R}_w = \mathbb{Z}_{2^w}[x_1, \dots, x_t] / (x_i^2 - x_i)$ over opaque atoms $x_1, \dots, x_t$ (still treating non-uniform constants and arithmetic-under-bitwise subtrees strictly as opaque atoms!):
1. Map any pure bitwise subexpression $e$ to its exact multilinear polynomial $T(e) \in \mathcal{R}_w$ (where $\deg_i \le 1$ by $x_i^2 = x_i$):
   - `const 0` $\mapsto 0$; `const (2^w - 1)` (all-ones ONLY!) $\mapsto 1$
   - opaque atom $x_i$ $\mapsto x_i$
   - `bvnot a` $\mapsto 1 - T(a)$
   - `bvand a b` $\mapsto T(a) \cdot T(b) \pmod{(x_i^2 - x_i)}$
   - `bvor a b` $\mapsto T(a) + T(b) - T(a)\cdot T(b)$
   - `bvxor a b` $\mapsto T(a) + T(b) - 2 \cdot T(a)\cdot T(b)$
2. **Crucial bitvector sign map (constant term $a_\emptyset$):**
   Because the all-ones bitvector is $-1 \pmod{2^w}$ (NOT $+1$!), a pure bitwise expression $e$ with $T(e) = a_\emptyset + \sum_{S \neq \emptyset} a_S \prod_{i \in S} x_i$ represents the bitvector identity:
   $$e \equiv -a_\emptyset + \sum_{S \neq \emptyset} a_S \left(\bigwedge_{i \in S} x_i\right) \pmod{2^w}!$$
   *(Double-check: `~x` has $T(\sim x) = 1 - x$, which maps to $-1 - x \pmod{2^w}$ — EXACT! `~(x & ~x)` has $T = 1$, which maps to $-1$ — EXACT!)*
3. Linear arithmetic combines $(c, P)$ linearly mod $2^w$:
   - `const v` $\mapsto (v \bmod 2^w, 0)$
   - `bvadd`/`bvsub`/`bvneg`/`bvmul(const, _)`/`bvshl(_, const)` combine $(c, P)$ linearly mod $2^w$
   - `bvnot e` in arithmetic context $\mapsto (-1 - c_e, -P_e)$
   - Pure bitwise $b$ $\mapsto (-a_\emptyset(T(b)),\; \sum_{S \neq \emptyset} a_S(T(b)) \prod_{i \in S} x_i)$
4. **Soundness & Completeness:** Because the $2^t - 1$ non-empty conjunctions $\bigwedge_{i \in S} x_i$ plus the constant $-1$ form a free basis of $\mathcal{L}(t)$ over $\mathbb{Z}/2^w\mathbb{Z}$, $L \equiv R \pmod{2^w}$ iff $c(L) = c(R)$ and $P(L) = P(R)$ in $\mathcal{R}_w$!

**Deliverables in `src/proof/rewrite_proof.ml`:**
- Keep the ultra-fast $2^k$ path for $k \le 8$, AND when $k > 8$ (up to e.g. `max_atoms = 32`, `max_monomials = 4096`, `max_ops = 2_000_000`, DAG-memoized!), automatically fall through to the **sparse multilinear $\mathcal{R}_w$ checker** inside `linear_mba_equal`!
- **Positive + Negative Bitwuzla cross-tests in `test/proof_test.ml`:**
  - Verify a 10-atom and 12-atom linear MBA identity replays in `< 2 ms` via `"linear_mba_mod2w"`.
  - Verify negative traps (non-uniform constant `x & 5`, arithmetic-under-bitwise `(x + y) & z`, off-by-one coefficient at 10 atoms) are **rejected** by `linear_mba_equal` AND refuted by Bitwuzla!

---

## 2. Arbitrary-Arity `BitTrans` + Bottom-Up `PolySim` + Complementary-Atom Pairing (`src/greysynth/normalization.ml`, `greysynth.ml`)

**Deliverables:**
1. **Factor-Before-Expand & Arbitrary-Arity `PolySim` (`polysim_candidate`):**
   - Replace/generalize our 2/3-atom-only minterm-ring nonlinear pass with **MBA-Flatten / RUMBA conjunction-basis `PolySim`**:
     - Given a ring expression $E$ containing at least one product of bitwise subexpressions (with `dag_size <= 2048`):
     - **Factor-before-expand:** First simplify multiplicative factors individually (so `E_k == 1` and `Z == 0` factors in MBA-Obfuscator Mode 1 collapse before multiplying!).
     - Collect all maximal pure-bitwise leaves $B_1, \dots, B_m$ in $E$. For each $B_j$, compute its sparse AND-conjunction expansion $F(B_j) = -a_\emptyset + \sum_{S \neq \emptyset} a_S (\bigwedge_{i \in S} x_i)$ via `BitTrans` (capped at e.g. `max_monomials_per_leaf = 64`, `max_total_monomials = 2048`).
       - Each leaf identity $B_j \equiv F(B_j)$ is certified by **ONE `linear_mba_mod2w` edge**!
     - Substitute $B_j \mapsto F(B_j)$ into $E$ to get $E_{\text{sub}}$, and expand/reduce $E_{\text{sub}}$ in the commutative ring $\mathbb{Z}_{2^w}[\text{conjunctions}]$ (or `poly_mod2w` if higher powers remain!), certified by **ONE `ring_mod2w` (or `poly_mod2w`) edge**!
     - **Bitwise Re-Synthesis before returning (`FinalOptimize`):** If the reduced polynomial is degree $\le 1$ (a linear combination of conjunctions!), run `linear_candidates` to fold it back into compact bitwise/arithmetic syntax (e.g., `x + y - 2*(x & y) -> x ^ y`), certified by **ONE `linear_mba_mod2w` edge**!
   - **Zero new TCB axioms needed!** Works for **ANY number of variables** ($t = 2, 3, 4, 5, \dots$), annihilating `C-MBA-Obfuscator` Modes 1, 3, 4 (including `target_366` and $\theta$-equalities $Z = \bar{A}\bar{B}$)!
2. **Complementary-Atom Pairing (`pair_complementary_atoms`) — Fixes MBA-Obfuscator Mode 2, Liu '22 §6 Eq. 40, GAMBA §5.5 & SaMBA:**
   - Whenever a linear/polynomial MBA layer contains arithmetic opaque atoms $\{A_1, \dots, A_m\}$ inside bitwise ops (or alongside bitwise ops):
   - Normalize each arithmetic atom $A_i$ via `ring_mod2w` (remembering `~u = -u - 1` so `-~x -> x + 1`, `~(-~x) -> -x - 2`!).
   - Check if any pair satisfies **$A_i + A_j \equiv -1 \pmod{2^w}$** (checked cleanly in `ring_mod2w`: hash each atom by canonical `min(ring(A_i), ring(-A_i - 1))`!).
   - Whenever $A_i + A_j \equiv -1 \pmod{2^w}$, rewrite $A_j \to \sim A_i$ (certified constructively via `ring_mod2w`: $A_j = -A_i - 1$ + `linear_mba_mod2w`: $-A_i - 1 = \sim A_i$!), immediately unifying $A_i$ and $A_j$ into the **same single atom** so outer bitwise/MBA cancellation triggers!
   - Example: `~(-~x)` and `(-~x)` simplify to `-x - 2` and `x + 1`; pairing detects `(-x - 2) + (x + 1) == -1`, rewrites `-x - 2 -> ~(x + 1)`, and collapses the enclosing layer to exact GT!
3. **Iterative Bottom-Up DAG Peeling with CSE Unification:**
   - Run `dag_bottom_up_simplify` iteratively (up to 4 passes while strictly shrinking `dag_size` or `size_of_expr`!) with `PolySim`, `linear_mba_mod2w`, complementary-atom pairing, and eager 0-variable constant folding (`eval_const`) + trivial identity peeling (`x*1`, `x+0`, `x^x -> 0`, `~(~x) -> x`) so multi-layer `C-MBA-Obfuscator` (`target_366`) and `Tigress L6–L8` peel layer-by-layer from leaves to root!

---

## 3. RUMBA Theorem 20 Semantic Bitwise Detection & §7.2 Correlated Null-Vector Injection (`src/greysynth/normalization.ml`)

1. **Theorem 20 Exact Semantic Bitwise Test (`is_semantically_bitwise`):**
   - Inside `linear_mba` / `dag_bottom_up_simplify`, when a bitwise operator (`&`, `|`, `^`, `~`) has an arithmetic child $L$ that is a linear MBA over $k \le 6$ atoms:
   - Evaluate $L$'s canonical signature on $\{0, 1\}^k$. By **RUMBA Theorem 20**:
     $$L \text{ is semantically bitwise} \iff \big(L(0)=0 \land \forall b,\, L(b) \in \{0, 1\}\big) \;\lor\; \big(L(0)=-1 \land \forall b,\, L(b) \in \{-2, -1\}\big).$$
   - If true, directly synthesize the compact pure-bitwise expression $B$ for $\bar{L}(b) = L(b) + 2\bar{L}(0) \in \{0, 1\}$, certify $L \equiv B$ with ONE `linear_mba_mod2w` edge, and continue simplifying the enclosing bitwise layer as a single flat linear MBA!
2. **RUMBA §7.2 Correlated Null-Vector Injection (1-atom & 2-atom bounded solver):**
   - Suppose a non-bitwise child $e'$ inside a bitwise op contains an abstracted arithmetic subterm $z := L(\vec{x})$ (where $L$ is a linear MBA over $\vec{x}$, $k \le 5$).
   - We know $v_0 := z - L(\vec{x}) \equiv 0 \pmod{2^w}$ identically!
   - Look for a scalar $\lambda \in \mathbb{Z}/2^w\mathbb{Z}$ (directly inferred from any single non-zero entry of $S_{v_0}$ where $S_{e'}(b) + \lambda S_{v_0}(b) \in \{0, 1\}$ or $\{-2, -1\}$!) such that $S_{e'} + \lambda S_{v_0}$ satisfies **Theorem 20** (or vanishes to $0$!).
   - If found, emit ONE `ring_mod2w` edge $e' \to e' + \lambda (z - L(\vec{x}))$ (valid because $z = L(\vec{x})$!) + ONE `linear_mba_mod2w` edge collapsing $e' + \lambda v_0 \to B(\vec{x}, z)$, unlocking the enclosing bitwise op!

---

## 4. Fast, Focused Verification Gate for Round 23 (Target Wall Time: ~5–10 min!)

Use our newly isolated `datasets/hard_cases/` harness (NO more wasting 40 minutes re-auditing already-solved expressions!):

1. **Unit & Soundness Tests (`test/proof_test.ml`, `test/normalization_test.ml`, `test/pipeline_test.ml`):**
   - 10-atom & 12-atom multilinear `linear_mba_mod2w` positive + negative Bitwuzla cross-tests.
   - Direct regression tests (with independent `mba_proof` replay!):
     - `datasets/hard_cases/all_failing/c_mba_obfuscator/*target_366*` (massive 3.4M-node 3-var layered target!)
     - Liu '22 §6 Eq. 40 complementary-atom test: `(~(x-1) & y)*(~(x-1) | y) + (~(x-1) & ~y)*(~~(x-1) & y) -> -x * y`
     - RUMBA §7.2 null-vector test: `~x & ~y & (-(x | y | ((x & y) - x - y))) -> 0`
     - MBA-Obfuscator Mode 2 recursive test (`(-~x)` + `~(-~x)`).
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **Regression smoke:** `datasets/hard_cases/regression_smoke/` (~60 complex already-solved cases across ALL 32 suites — runs in **< 20s**! Must stay **100% established, 0 refuted, 0 quality regressions**!).
   - **Primary target (full remaining):** `datasets/hard_cases/all_failing/c_mba_obfuscator/` (all **152** remaining weak cases — target: dramatic collapse toward solved!).
   - **Secondary target:** `datasets/hard_cases/all_failing/mba_obf_nonlinear/` (all remaining weak cases) + `datasets/hard_cases/core_hard/` (~400 stratified hardest cases across all suites — runs in ~3–5 min!).
4. Record concise Round-23 results (including before/after on `c_mba_obfuscator`, `mba_obf_nonlinear`, `core_hard`, and `regression_smoke`) in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
