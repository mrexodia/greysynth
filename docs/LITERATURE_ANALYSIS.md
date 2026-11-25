# Literature Analysis: 26 MBA Deobfuscation Papers Mapped to GreySynth

**Date:** 2026-11-25  
**Baseline commit:** `4f66d43` (Rounds 19–22 complete: `ring_mod2w`, `poly_mod2w` up to deg 66, `linear_mba_mod2w` up to 8 opaque atoms, DAG-native e-graph + bottom-up pass, 2/3-atom minterm-ring cancellation, dialect adapters, opt-in `pipeline_portfolio`)  
**Source corpus:** All 26 markdown papers/theses in `C:\CodeBlocks\ocr-server\mba-markdown`  
**Architectural principle:** Prioritize **semantically correct, constructively proof-certifiable transformations** (`mba_proof`) and **structured algebraic interpolation / deterministic local synthesis** over blind random-input black-box search. Never weaken the proof gate or count finite-sample agreement as proof.

---

## 1. Corpus Read (26 Papers / Theses)

1. **NeuReduce** (`2020.findings-emnlp.56.md`, Feng et al., EMNLP '20) — Seq2Seq linear MBA; 20% of corpus has 4–10 variables with compact sparse Boolean GTs.
2. **XSMIR / SMIR** (`2025-ccs.md`, Attias et al., CCS '25) — Search Modulo 9 Analytical Local Inference Rules (`+`, `^`, `*`, AND-OR mask, Affine, Univariate Poly, `ror`, `<<`, `>>`); `XSMIR-min`.
3. **gMBA** (`2025.findings-acl.1127.md`, Noh et al., ACL '25) — Extended $\{0,1\}^n \to \mathbb{Z}/m\mathbb{Z}$ truth tables jump exact match 40.8% → 92.8%.
4. **GreySynth** (`2026-ccs.md`, Attias et al., CCS '26) — Contextual horizon synthesis; documents cache-amplified FPs, horizon arity explosion, and global constant-injection interference.
5. **SiMBA** (`2209.06335v1.md`, Reichenwallner & Meerwald-Stadler, CheckMATE '22) — Direct $\{0,1\}^t$ evaluation in $B^n$, $O(t 2^t)$ Möbius inversion, 8-case structured linear signature reconstruction.
6. **GAMBA** (`2305.06763v2.md`, Reichenwallner & Meerwald-Stadler, WoRMA '23) — Negated-term decompositions, disjoint-variable partitioning for $t>3$, Quine–McCluskey + XOR/distributive synthesis, power-of-2 bitwise factoring, expand-then-factor shared-factor grouping, implicit `-X-1 == ~X` substitution.
7. **MSiMBA / Semi-Linear MBA** (`2406.10016v2.md`, Skees, arXiv '24) — Decidable $O(w \cdot 2^t)$ $\{0,2^i\}^t$ signature matrix for arbitrary non-uniform constants inside `& | ^ ~` + closed-form modular don't-care merging.
8. **SCRAMBLER** (`2603.03624v2.md`, Lee et al., arXiv '26) — E-graph equality expansion produces 35k-node ASTs with tiny $\le 3k$ DAGs and neutral identity padding.
9. **GPU-SIMBA: Beyond Caching** (`2605.08243v1.md`, Bathie et al., '26) — Proves observational cache breakdown; cache-free locally consistent RPN unranking (`T[s][op]`).
10. **Binary Permutation Polynomial Inversion** (`2995306.2995310.md`, Barthelemy/Eyrolles/Renault/Roblin, SPRO '16) — Rivest characterization, zero ideal $I$, quadratic 6-step Newton compositional inversion in $\mathbb{Z}_{2^w}[x]/I$.
11. **MBA-Solver** (`3453483.3454068.md`, Xu et al., PLDI '21) — Alternation-minimizing AND-conjunction basis, bit-blasting-free polynomial MBA expansion, bottom-up CSE abstraction.
12. **Xyntia** (`3460120.3485250.md`, Menguy et al., CCS '21) — ILS with log-arith distance, dead-input perturbation filtering, branchless-ITE merged handler defense (§8.3).
13. **SaMBA** (`3779208.3785382.md`, König et al., ASIA CCS '26) — E-graph obfuscator using `~u -> -u-1` cascades and recursively nested nonlinear multiplication splitting.
14. **Eyrolles PhD Thesis** (`75068_EYROLLES_2017_archivage.md`, Paris-Saclay '17) — Disjoint bitmask partitioning for arbitrary-constant linear MBAs, $2^k$ factor extraction from bitwise ops, backward `& (2^k-1)` bitwidth narrowing, outer-to-inner anti-sharing.
15. **MBA-Flatten / In-Place Simplification** (`Security and Communication Networks - 2022 - Liu...md`, Liu et al., '22) — Arbitrary-arity multilinear `BitTrans` $\mathbb{Z}_{2^w}[\vec{x}]/(x_i^2-x_i)$, bottom-up layered `PolySim`, §6 Eq. 40 complementary-atom failure mode.
16. **Greybox Program Synthesis / QSynthesis** (`US-21-David-Greybox-Program-Synthesis-wp.md`, David, BH '21) — Dual-sweep top-down/bottom-up traversal, `extract`/`concat`/`ext`/`mul` cast canonicalization (halved runtime).
17. **RUMBA: Mathematical Framework for MBA Simplification** (`arxive.md`, Royer/Tronel/Vinçont, HAL Apr '26) — Theorem 20 exact semantic bitwise detection, §7.2 correlated null-vector injection, §6 symmetrized conjunction-basis PCT, §7.1 dynamic masking `&(2^m-1)` & `<< k` width narrowing.
18. **QSynth** (`bar2020-preprint9.md`, David et al., BAR '20) — Placeholder-variable arity compression, operator-stratified sub-grammars, corner-case input seeding.
19. **Normalized Reduction of Multivariate Binary Polynomials** (`bar2024-14-paper.md`, Gàmez-Montolio et al., BAR '24) — Truncated-row Stirling normalization $F[\ell, d+1]$ for arbitrary degree $> d_w$, sparse Kronecker multivariate normalization, §VI centered signed representative recovery.
20. **BSc Thesis** (`bsc.md`, Gàmez i Montolio, UB '20) — Eyrolles DAG complexity metrics (`alt_MBA`), backward demand-bit width propagation (Def. 2.21), CEGIS distinguishing inputs.
21. **ProMBA** (`ccs23.md`, Lee & Lee, CCS '23) — Hash-consed height-widening `ChooseSubExpr`, AC-flattened pairwise synthesis, on-the-fly verified rule generalization (58% → 84% success, 3× smaller).
22. **Non-Linear MBA / MBA-Obfuscator** (`document.md`, Liu et al., ICICS '21) — Exact 4 generator modes (`F.polynomial` with $\theta$-equalities $Z=\bar{A}\bar{B}$, `F.recursively`, `F.replace`, `F.combination`).
23. **MSc Thesis** (`msc.md`, Gàmez i Montolio, UOC ~'21) — Exact bit-plane restriction for bitwise constants, staged alternation-reducing proof bridge (`E_orig -> E_bridge` algebraically, SMT only on `E_bridge == E_cand`).
24. **Syntia** (`sec17-blazytko.md`, Blazytko et al., USENIX '17) — Stratified reuse of verified sub-DAGs, distinguishing-input filtering.
25. **MBA-Blast** (`sec21-liu-binbin.md`, Liu et al., USENIX '21) — Two-way $1 \leftrightarrow n$-bit equivalence, bottom-up opaque subexpression substitution.
26. **Loki** (`sec22-schloegel.md`, Schloegel et al., USENIX '22) — Independent per-copy MBA rewriting of duplicated SSA superoperators, dead key branches behind nonlinear masks, shift/cast MBA rules.

---

## 2. Eight High-Leverage Techniques Missing from Our Fork

### Part A — Pure Constructive Algebraic Transformations (Zero Synthesis, 100% `mba_proof`-Certifiable)

#### 1. Arbitrary-Arity Multilinear `BitTrans` + Bottom-Up `PolySim` + Complementary-Atom Pairing
- **Sources:** MBA-Flatten ('22), MBA-Obfuscator ('21), MBA-Solver ('21), RUMBA ('26 §6 PCT), GAMBA (§5.5).
- **Delta:** Replace our 2/3-atom minterm-ring ceiling and 8-atom truth-table cap with the **sparse multilinear AND-conjunction ring** $\mathbb{Z}_{2^w}[x_1,\dots,x_t]/(x_i^2 - x_i)$:
  - `~x -> 1-x`, `x&y -> xy`, `x|y -> x+y-xy`, `x^y -> x+y-2xy` (mapping constant $+a_e \to -a_e$ and monomials back to $\bigwedge x_i$).
  - **Factor-Before-Expand:** Reduce each multiplicative factor individually before expanding products so $E_k \equiv 1$ and $\theta$-equality factors $\bar{B} \equiv 0$ vanish in linear time.
  - **Complementary-Atom Pairing:** When arithmetic subterms at a bitwise boundary satisfy $A_i + A_j \equiv -1 \pmod{2^w}$ (e.g., `-x` and `x - 1`, or `x + 1` and `-x - 2`), rewrite $A_j \to \sim t_i$ sharing atom $t_i = A_i$ (fixes Liu '22 §6 Eq. 40, MBA-Obfuscator Mode 2, and SaMBA `~u -> -u-1`).
  - **Bitwise Re-Synthesis before moving up:** When `PolySim` produces a linear AND-form that is semantically a single bitwise op (e.g., `x + y - 2*(x & y) -> x ^ y`), fold it back to pure bitwise syntax so enclosing bitwise ops see it directly.
- **`mba_proof` integration:** Upgrade `linear_mba_mod2w` (or add sparse multilinear mode) to remove the 8-atom cap; certify each bitwise leaf via `linear_mba_mod2w` and polynomial collapse via existing `ring_mod2w`/`poly_mod2w`. Zero new TCB axioms for nonlinear cancellation.
- **Unlocks:** **`C-MBA-Obfuscator` (~295/500 remaining, including `target_366`)**, **deep `Tigress L6–L8`**, **`OMVLL`**.

#### 2. Semantic Bitwise Detection (Theorem 20) + Correlated Null-Vector Injection
- **Source:** RUMBA (`arxive.md`, HAL Apr '26 — Thm 19–20, Alg 2, §7.2).
- **Delta:**
  - **Theorem 20:** A linear MBA $L$ inside `& | ^ ~` is **semantically bitwise** iff $(L(0)=0 \land L(\{0,1\}^t)\subseteq\{0,1\})$ or $(L(0)=-1 \land L(\{0,1\}^t)\subseteq\{-2,-1\})$. Rewrite $L$ directly to its bitwise form $B$ and continue collapsing the outer layer in one pass.
  - **§7.2 Correlated Null-Vector Injection:** When an abstracted subexpression $z := L(\vec{x})$ appears inside a bitwise context, use the exact zero identity $v_0 := z - L(\vec{x}) \equiv 0$ and solve for $\lambda \in \mathbb{Z}/2^w\mathbb{Z}$ so $e'(\vec{x}, z) + \lambda v_0$ satisfies Theorem 20 (or vanishes identically).
- **`mba_proof` integration:** 100% constructive: `ring_mod2w` adds $\lambda(z - L) = 0$, followed by `linear_mba_mod2w` collapsing to bitwise $B$.
- **Unlocks:** Deeply nested arithmetic-in-bitwise layers in **`C-MBA-Obfuscator`**, **`Tigress L6–L8`**, **`OMVLL`**.

#### 3. Quotient-Ring DAG `poly_mod2w` + Truncated-Row Normalization + Centered Sparse Recovery + Newton Permutation Inversion
- **Sources:** Barthelemy/Eyrolles (SPRO '16) + Gàmez-Montolio et al. (BAR '24).
- **Delta:**
  - **Quotient-ring DAG evaluation:** Evaluate polynomial DAGs bottom-up directly inside $\mathbb{Z}_{2^w}[\vec{x}]/\mathcal{Z}^{w,k}$ (reducing mod the falling-factorial null ideal after every `+`, `-`, `*`, `pow` via BAR '24's truncated-row Stirling transform $F[\ell, d+1]$). Eliminates the flat degree-66 cap and collapses composed 64-bit permutation polynomials $Q(P(x))$ (raw degree up to $65^2 = 4,225$) in milliseconds.
  - **Centered signed extraction (BAR '24 §VI):** Pick signed null-ideal shifts $s_j \in \{0, -1\}$ so `-x^2` isn't bloated into `127*x^2 + 128*x`.
  - **Untrusted 6-step Newton compositional inversion:** For Rivest permutation polynomials ($P'(x)$ is always odd), run 6 Newton iterations mod $\mathcal{Z}^w$ in $O(d_w^2 \log w)$ to invert/simplify $P(Q(x))$ and $P(E + Q(K))$, certified constructively by quotient-ring `poly_mod2w`.
- **Unlocks:** **`Permutation64` (`3/13 → ~13/13`)**, high-degree polynomial opaque constants in `Tigress`/`ObfuscatorX`.

#### 4. Decidable `semilinear_mba_mod2w` (Non-Uniform Constants) + $2^k$ Pullout + Demand-Bit Width Narrowing
- **Sources:** MSiMBA ('24 Thm 1.1 & §5), Eyrolles PhD (§3.1, §3.4.3, §4.1.3), RUMBA (§7.1), GAMBA (§5.2), BSc/MSc Theses.
- **Delta:**
  - **Decidable `semilinear_mba_mod2w`:** Sound & complete mod $2^w$ for arbitrary non-uniform constants inside `& | ^ ~` and constant left shifts, verified via MSiMBA's $O(w \cdot 2^t)$ $\{0, 2^i\}^t$ signature matrix or Eyrolles's $O(r \cdot 2^t)$ disjoint bitmask partition ($r \le \min(w, 2^m)$), plus closed-form modular don't-care merging (`v_2(m1-m2) + ctz(mask) >= w`).
  - **Power-of-2 pullout:** $(2^k A) \diamond (2^k B) = 2^k(A \diamond B)$ and $\sim(2^k A) = 2^k(\sim A) + (2^k - 1)$.
  - **Backward demand-bit width narrowing:** Under `& (2^k - 1)` or `<< s`, simplify inner T-function subtrees mod $2^k$ (or $2^{w-s}$), collapsing high-bit constants and triggering low-bit null polynomials like `(x*(x-1)) & 1 == 0`.
- **`mba_proof` integration:** Small decidable `semilinear_mba_mod2w` rule + 3-line shift/mask congruence lemmas.
- **Unlocks:** Bit-sliced/masked/constant-shift MBAs, **`OMVLL`**, **`Tigress L6–L8`**, **`ObfuscatorX`**.

#### 5. Shared-Factor Grouping + Multi-Term / Negated / Disjoint Linear Reconstruction
- **Sources:** GAMBA (§4.2–4.4, §5.4), SiMBA (§3.2.4), NeuReduce ('20).
- **Delta:**
  - **Expand-then-Factor shared-factor grouping (GAMBA §5.4):** Factor high-frequency common factors out of expanded nonlinear sums (`ring_mod2w`), merge identical cofactors, then collapse exposed linear MBAs (`linear_mba_mod2w`).
  - **Complete multi-term + negated signature reconstruction:** Recover `c1*B1 + c2*~B2`, `c1*~B1 + c2*~B2`, additive splits $a \equiv b+c \pmod{2^w}$, and split $t>3$ conjunction-basis terms into connected variable components with Quine–McCluskey + XOR/distributive factoring.
- **Unlocks:** **`ObfuscatorX`**, **`Neureduce`** remaining ~26% non-GT rows (4–10 vars & compact multi-term GTs).

#### 6. White-Box Beyond-MBA Normalizers + Alternation-Reducing Proof Bridge
- **Sources:** QSynthesis ('21 §V), Xyntia (§8.3), MSc Thesis (Ch. 3), Loki ('22).
- **Delta:**
  - **Cast/widening canonicalization:** `extract(mul(ext(a), ext(b))) -> mul(a, b)`, constant `concat` folding.
  - **Branchless-ITE lifting:** Lift sign/zero bit-tricks (`(x | -x) >> (w-1)`, etc.) into explicit `ITE(cond, h1, h2)` so branches simplify independently.
  - **Alternation-reducing proof bridge:** Before querying Bitwuzla on high-alternation `E_orig == E_cand` (root cause of persistent `OMVLL` timeouts), constructively normalize `E_orig -> E_bridge` via fast decidable algebraic rules to drive MBA alternation toward 0, querying SMT only on `E_bridge == E_cand`.
  - **Cross-branch concrete-fingerprint DAG CSE:** Merge semantically identical but differently-obfuscated SSA sub-DAGs bottom-up (breaking Loki's independent per-copy rewriting).

---

### Part B — Smart Algebraic Interpolation & Exact Local Synthesis (Proof-Gated)

#### 7. XSMIR's 9 Analytical Local Inference Rules + Greybox `XSMIR-min`
- **Source:** XSMIR / SMIR (CCS '25, Tables 4, 13, 17).
- **Delta:** For any small candidate $e$ and sample bank $\mathcal{S}$, analytically infer outer wrappers in $O(|\mathcal{S}|)$:
  1. $e + c$, 2. $e \oplus c$, 3. $c \cdot e$, 4. **Affine** $c_1 e + c_2$ (2-adic inverse on opposite-parity samples), 5. **AND-OR bitmask** $(e \land c_\land) \lor c_\lor$ (exact bit-envelope formula), 6. **Univariate polynomial** $\sum c_j e^j \pmod{2^w}$ (modular Vandermonde/Newton interpolation), plus 64-step `ror k`, `<< k`, `>> k`, `>>s k`.
- **Why it fits our fork:** CCS '25 achieved flat 89.4%/88.9%/88.9% across Tigress L1–L3; their **`XSMIR-min` combinator gained +8.9 ppt and 2.1× speed** and was only rejected for black-box FP (which our `mba_proof` gate eliminates completely!). Running it on OES candidates and bottom-up greybox subtrees peels arbitrary 64-bit constants, masks, shifts, rotates, and nested wrappers deterministically.

#### 8. Cache-Free Locally Consistent Exact Enumeration + ProMBA Hash-Consed Windows & On-the-Fly Verified Rule Learning
- **Sources:** GPU-SIMBA ('26 §3.1–3.2), ProMBA ('23 Alg. 1–2, §3.4–3.6), GreySynth ('26 §6), Xyntia (§8.1).
- **Delta:**
  - **Deterministic small-tree enumerator + XSMIR fitting:** Cache-free locally consistent RPN unranking (`T[s][op]`, hoisting left-subtree sample vectors in registers + restricting operators to the subtree's ops) paired with XSMIR analytical constant fitting replaces brittle random Xyntia rollouts for small CHS horizons ($s \le 7$).
  - **Arity-budgeted / hash-consed truncation + dead-stub elimination:** Unify identical boundary subtrees into the same stub variable (ProMBA `ChooseSubExpr`), drop dead stubs via 1-var perturbation (Xyntia §8.1), and cap stub arity instead of uniform syntactic depth.
  - **AC-flattened pairwise synthesis + on-the-fly verified lemma learning (ProMBA §3.4–3.6):** Generalize every proved local rewrite $r \to r'$ into a verified lemma and test pairwise cancellations on flattened AC chains.

---

## 3. Staged Implementation Roadmap (Driven Against Curated Hard-Cases + Regression Smoke)

| Round | Work Package | Primary Target Suites |
|---|---|---|
| **R23** | **Multilinear `BitTrans` + Bottom-Up `PolySim` + Complementary-Atom Pairing + RUMBA Thm 20 / §7.2 Null-Vector Injection** | `C-MBA-Obfuscator` (~295 remaining, `target_366`), `Tigress L6–L8`, `OMVLL` |
| **R24** | **Quotient-Ring DAG `poly_mod2w` + Truncated-Row Normalization + Centered Sparse Recovery + Newton Permutation Inversion** | `Permutation64` (`3/13 → ~13/13`), high-degree opaque constants |
| **R25** | **Decidable `semilinear_mba_mod2w` + $2^k$-Pullout + Backward Demand-Bit Width Narrowing + Alternation-Reducing Proof Bridge** | Non-uniform constant/masked/shift MBAs, **7 persistent `OMVLL` timeouts**, `ObfuscatorX` |
| **R26** | **OES + 9-Rule XSMIR Analytical Elevation (`XSMIR-min`) + Exact Small-Tree Enumerator + ProMBA Hash-Consed Windows / AC-Pairwise / Verified Rule Learning** | `Tigress L5–L8`, `Loki`, `QSynth` beyond-MBA |
| **R27** | **GAMBA Shared-Factor Grouping + Multi-Term/Negated/Disjoint Linear Reconstruction + Cast/Branchless-ITE Lifting + Final Full-Suite Verification** | `Neureduce` remaining 26%, `ObfuscatorX`, binary-lifted casts/ITEs, full regression check |
