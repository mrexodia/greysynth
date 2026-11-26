# GreySynth Round-27 Spec: GAMBA Shared-Factor Grouping, Complete Multi-Term / Negated / Disjoint-Component Linear Reconstruction, Cast Canonicalization & Branchless-ITE Lifting

**Baseline:** Round 26 (Analytical XSMIR 10-rule local interpolation, cache-free exact small-tree enumeration, ProMBA `GeneralizeRule` & AC-pairwise synthesis)  
**Sources (from `docs/LITERATURE_ANALYSIS.md`):**
- **GAMBA** (Reichenwallner & Meerwald-Stadler, WoRMA '23, `2305.06763v2.md`, §4.2–§4.4, §5.4) — Negated-term signature splits (`c1*B1 + c2*~B2`, `c1*~B1 + c2*~B2`), disjoint-variable component partitioning for $t > 3$, Quine–McCluskey + XOR/distributive synthesis, and expand-then-factor shared-factor grouping
- **SiMBA** (`2209.06335v1.md`, §3.2.4 Cases 3, 5, 6, 7, 8) — Complete 8-case structured linear signature reconstruction (including additive overlap split $a \equiv b + c \pmod{2^w}$)
- **QSynthesis** (`US-21-David-Greybox-Program-Synthesis-wp.md`, §V) — Cast/widening `extract`/`concat`/`zext`/`sext`/`mul` canonicalization (halved binary-lifted runtimes)
- **Xyntia** (`3460120.3485250.md`, §8.3) — Branchless-selector lifting into explicit `ITE(cond, h1, h2)` so branches simplify independently

**Primary targets:**
- **`datasets/hard_cases/all_failing/neureduce/`** (all 53 remaining weak rows — 4–10 vars & compact multi-term/negated/disjoint GTs!)
- **`datasets/hard_cases/all_failing/mba_flatten/`** (all 96 remaining weak rows)
- **`datasets/hard_cases/all_failing/obfuscatorx/`** (all 7 shared-factor rows!)
- **`datasets/hard_cases/all_failing/simba_e1_4vars/`** (12 remaining weak) & **`simba_e1..e4_3vars/`** (168 remaining weak!)
- **`datasets/hard_cases/core_hard/`** (406 non-GB cases) & **`datasets/hard_cases/regression_smoke/`** (62 guards)

---

## 1. Complete SiMBA/GAMBA Structured Linear Signature Reconstruction (`src/greysynth/normalization.ml`)

Today `linear_candidates` covers single-term affine forms and raw Möbius/grouped sums, missing exact multi-term and negated-term linear MBA forms that dominate `Neureduce`, `MBA-Flatten`, and residual 3/4-var `SiMBA`:

**Deliverables:**
1. **Complete 10-Case Signature Reconstructor for Projected Support $k' \le 4$ (SiMBA §3.2.4 + GAMBA §4.2):**
   Given the projected active-support signature array `target` (length $2^{k'}$) with $a = \text{target}.(0)$ and distinct values $U$:
   - **Case 3 (Single negated term, SiMBA §3.2.4):** $a \neq 0$, $U = \{a, 2a \bmod 2^w\}$ $\implies -a \cdot (\sim B)$ where $B$ is `true` on $\{2a\}$!
   - **Case 5 (2 disjoint terms, SiMBA §3.2.4):** $a = 0$, $U = \{0, u, v\}$ $\implies u \cdot B_u + v \cdot B_v$.
   - **Case 6 (2 overlapping additive-split terms, SiMBA §3.2.4):** $a = 0$, $U = \{0, u, v, s\}$ where $s \equiv u + v \pmod{2^w}$ (check all 3 orderings!) $\implies u \cdot B_{\{u, s\}} + v \cdot B_{\{v, s\}}$! *(Recovers `c1*(x ^ y) + c2*x` cleanly in 2 terms!)*
   - **Case 7 (3 disjoint terms, SiMBA §3.2.4):** $a = 0$, $U = \{0, u, v, z\}$ $\implies u B_u + v B_v + z B_z$.
   - **Case 8 (Constant shift + Cases 5–7):** subtract $a$ from `target`, run Cases 5–7, add $a$ back!
   - **GAMBA §4.2a (Unnegated + Negated `c1*B1 + c2*~B2`):** $a \neq 0$, at most 2 values in $U \setminus \{a, 2a\}$:
     - If $U \setminus \{a, 2a\} = \{b\}$: try BOTH $(b - a) B_{\{b\}} - a \cdot (\sim B_{\{2a\}})$ AND $(b - 2a) B_{\{b\}} - a \cdot (\sim B_{\{2a, b\}})$!
     - If $U \setminus \{a, 2a\} = \{b, c\}$ with $c - b \equiv a \pmod{2^w}$ (or $b - c \equiv a$): emit $(b - a) B_{\{b, c\}} - a \cdot (\sim B_{\{2a, c\}})$!
   - **GAMBA §4.2b (Two negated terms `c1*~B1 + c2*~B2`):** $a \neq 0$, $U \setminus \{a, 2a\} = \{b, c\}$ with $b + c \equiv 3a \pmod{2^w}$: emit $(a - b) \cdot (\sim B_{\{2a, b\}}) + (a - c) \cdot (\sim B_{\{2a, c\}})$!
   - All candidates are scored by `cost` and certified by **ONE `linear_mba_mod2w` edge** (zero SMT!).
2. **GAMBA §4.3 Disjoint Variable-Component Partitioning (for $t > 3$ up to $t \le 12$!):**
   - After computing the sparse multilinear / Möbius AND-conjunction representation $c_0 + \sum_{S \neq \emptyset} c_S \bigwedge_{i \in S} x_i$ (using our Round 23 sparse multilinear evaluator up to 12 variables — instant even for 10-var `Neureduce` expressions!):
   - Build the variable co-occurrence graph across all non-zero monomials $S$ (`|S| >= 2` connects variables in $S$), and compute connected components $C_1, \dots, C_r$ via union-find!
   - If $r \ge 2$, reconstruct **each component $C_j$ independently** (any component with $|C_j| \le 4$ hits our exact 10-case SiMBA/GAMBA reconstructor above!), try attaching $c_0$ to whichever component minimizes total cost (or keep $c_0$ standalone), sum the reconstructed components, and certify the entire rewrite with **ONE `linear_mba_mod2w` edge**!
   - Directly solves `Neureduce` 4–10 variable sums of disjoint components (`line_0000007`: `-3*(~v0&(v1^v2)) + 2*(v0&(v1^v2)) + (v3|v4)` -> exact GT!)!
3. **GAMBA §4.4 Compact Boolean Synthesis (`boolean_candidates`) Upgrade:**
   - Add iterative **XOR & distributive factoring** on top of Quine–McCluskey prime implicants:
     - `(X & ~Y) | (~X & Y) -> X ^ Y`, `(X | Y) & (~X | ~Y) -> X ^ Y`, `~X ^ ~Y -> X ^ Y`
     - `(X & Y) | (X & Z) -> X & (Y | Z)` and dual `(X | Y) & (X | Z) -> X | (Y & Z)`
     - Exact lookup / cofactor synthesis for $k' \le 3$ so 3-var Boolean expressions like `~v0 & (v1 ^ v2)` and `v0 | v1 | v2` are ALWAYS minimal!

---

## 2. GAMBA §5.4 Expand-then-Factor Shared-Factor Grouping (`src/greysynth/normalization.ml`)

Look at `datasets/hard_cases/all_failing/obfuscatorx/` (all 7 rows!) and expanded nonlinear sums in `Tigress` / `C-MBA-Obfuscator`:
`((... & i) * (c * (d | (a + l)))) + (((f * (d | (a + l))) * (...)) + ((~((j & k) & i)) * (c * (d | (a + l)))))`
- Repeated multiplicative factor `(d | (a + l))` appears inside every additive term, nested asymmetrically inside `c * (d | (a + l))` vs `f * (d | (a + l))`!

**Deliverables (`shared_factor_group_candidate`):**
- Flatten top-level additive sum $T_1 + \dots + T_m$ ($2 \le m \le 64$); for each additive term $T_i$, flatten its multiplicative factors `[f_{i,1}; ...; f_{i,r}]` (keeping signs/constants cleanly).
- Find the **highest-frequency non-constant factor $F$** appearing in $\ge 2$ terms (breaking ties by largest `size_of_expr F` so giant shared subexpressions like `(d | (a + l))` factor out first!).
- Group the matching terms as `F * (cofactor_1 + ... + cofactor_p) + remainder`, recursively simplify the exposed cofactor sum (with `linear_candidates` / `shared_factor_group_candidate` / `ring_polynomial_candidate`), and keep the result if strictly cheaper!
- **Certification:** 100% constructive! Emit **ONE `ring_mod2w` edge** `original == F * cofactor_sum + remainder`, followed by whatever decidable edge (`linear_mba_mod2w` / `ring_mod2w`) simplifies `cofactor_sum`! Zero Bitwuzla SMT needed!

---

## 3. QSynthesis Cast/Widening Canonicalization & Xyntia §8.3 Branchless-ITE Lifting (`src/greysynth/normalization.ml`)

1. **Cast & Widening Canonicalization (QSynthesis §V):**
   Add sound, fast local rewrite rules in `Normalization.local_candidates` / `dag_bottom_up_simplify`:
   - `restrict(0, k-1, uext(n, x))` / `restrict(0, k-1, sext(n, x))` when `k = sizeof x` $\to$ `x` (and for `k < sizeof x` $\to$ `restrict(0, k-1, x)`)
   - `restrict(0, k-1, op(ext(x), ext(y)))` for `op in {+, -, *, &, |, ^}` when `sizeof x = sizeof y = k` $\to$ `op(x, y)` (widening mul/add truncation — halved QSynthesis runtimes on `VR-EA`/`EA-ED`!)
   - `restrict(lo, hi, concat(hi_part, lo_part))` when `[lo, hi]` lies completely inside `lo_part` or `hi_part` $\to$ direct sub-extract!
   - `concat(Cst a, Cst b)` $\to$ folded `Cst`!
   - `uext(0, x) -> x`, `sext(0, x) -> x`, `uext(a, uext(b, x)) -> uext(a+b, x)`, `sext(a, sext(b, x)) -> sext(a+b, x)`.
2. **Branchless-ITE Lifting (Xyntia §8.3):**
   Detect branchless zero/sign-mask selector idioms (at width $w$):
   - `m = ((d ^ (d >>s (w-1))) - (d >>s (w-1))) >> (w-1)` or `((d | -d) >> (w-1))` (which is `0` iff `d = 0`, `1` iff `d != 0`)
   - `m * A + (1 - m) * B` or `(A & mask) | (B & ~mask)` where `mask = 0` or `-1` (e.g., `d == 0 ? 0 : -1`, `-(c)` for 1-bit `c`, or `(x >>s (w-1))`) $\to$ lift into `ITE(cond, A, B)` so `A` and `B` simplify independently!
   - Certify via tiny local SMT check (`< 2 ms` on abstracted atoms `d, A, B`).

---

## 4. Fast, Focused Verification Gate for Round 27 (Target Wall Time: ~4–6 min!)

1. **Unit & Soundness Tests (`test/round27_test.ml`, `test/normalization_test.ml`):**
   - SiMBA/GAMBA Cases 3, 5, 6, 7, 8 + GAMBA §4.2a/b negated-term splits + 5-var/8-var disjoint-component splitting (including actual `neureduce` `line_0000007` and `line_0000010` collapsing to `<= GT`!).
   - GAMBA §5.4 shared-factor grouping on `obfuscatorx` row 1 (verifying shared `(d | (a + l))` factoring via `ring_mod2w` + zero SMT!).
   - QSynthesis cast/widening canonicalization (`restrict(0, 31, mul(uext(32, x), uext(32, y))) -> mul(x, y)`) & branchless-ITE lifting tests.
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/all_failing/neureduce/`** (all 53 remaining weak!)
   - **`datasets/hard_cases/all_failing/mba_flatten/`** (all 96 remaining weak!)
   - **`datasets/hard_cases/all_failing/obfuscatorx/`** (all 7 rows!)
   - **`datasets/hard_cases/all_failing/simba_e1_4vars/`** (all 12 remaining weak!)
   - **`datasets/hard_cases/core_hard/`** (406 non-GB cases) & **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted!)
4. Record concise Round-27 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
