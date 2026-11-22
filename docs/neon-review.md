# MBA Simplification Review & Recommendations

This review supplements `docs/PLAN.md` based on the CCS '26 GreySynth paper (`grey-synth.md`), a full review of `src/greysynth/`, `src/proof/rewrite_proof.ml`, `src/utils/utils.ml`, and vendored Xyntia sources, plus live read-only probes of the built `greysynth` binary on representative MBA benchmarks.

The non-negotiable invariant from `docs/PLAN.md` remains intact throughout: every generated candidate is untrusted and must pass the shared width, cost, independent-sample, and SMT acceptance policy, with independent certificate replay (`mba_proof`) as the final gate.

---

## 1. Immediate Bugs to Fix (Current Code & In-Progress Milestone 1)

### 1.1 Active WIP (`src/greysynth/synth_backends.ml` & vendored Xyntia)
1. **`XO.ITE` produces an ill-typed condition width (`src/greysynth/synth_backends.ml:228`)**:
   - Currently translates `XO.ITE` as `ite first second third`, passing a `w`-bit `first` directly as the condition.
   - `Sexpr.Expr.ite` expects a **1-bit** condition: `Rewrite_proof.intern` (`src/proof/rewrite_proof.ml:111`) rejects `condition.width <> 1` (`"ill-typed conditional"`), and `Utils.are_equivalent_seconds` (`src/utils/utils.ml:325`) calls `Solver.Bv.to_bl`.
   - `test/synth_backends_test.ml` did not catch this because `Sample_evaluator.eval` only checks `Bitvector.is_zeros` without asserting `sizeof c = 1`.
   - **Fix**: Translate as `ite (same_width_binary Diff first (constant (Bitvector.zeros (sizeof first)))) second third` (matching Xyntia's `operators.ml:483` `(ite (distinct c 0) t e)`), and assert `Rewrite_proof.of_expr` / `Utils.are_equivalent` in `test/synth_backends_test.ml`.
2. **`XO.Im` checks `-1` instead of `1` (`src/greysynth/synth_backends.ml:229-231`)**:
   - Currently compares `first` against `Bitvector.fill (sizeof first)` (all-1-bits / `-1`).
   - Xyntia's `outside_tools/xyntia/src/lib/operators.ml:484,522` checks `Bitvector.is_ones` (`= 1`, i.e., `Bitvector.ones (sizeof first)`).
   - **Fix**: Replace `Bitvector.fill` with `Bitvector.ones` and test both `first = 1`, `first = 0`, and `first = -1` in `test/synth_backends_test.ml`.
3. **Vendored Xyntia `SMod_x86` div-by-zero mismatch (`outside_tools/xyntia/src/lib/operators.ml:432-433`)**:
   - Returns `y` (`0`) when dividing by zero, whereas `synth_backends.ml:217` maps `SMod_x86` to `Smod` (SMT-LIB `bvsrem x 0 = x`).
   - **Fix**: Return `x` on `Bitvector.is_zeros divisor` (or test div-by-zero parity across all `Div`/`Mod` operators in `synth_backends_test.ml`).
4. **Vendored Xyntia `SIGALRM` clobbering & CPU-vs-wall timeout (`outside_tools/xyntia/src/lib/heuristic.ml:122,158`)**:
   - `MkSearch.search` unconditionally resets `Sys.sigalrm` to a no-op handler on every synthesis call, clobbering any caller alarm.
   - Timeout checks use `Sys.time ()` (CPU time) instead of wall time (`Unix.gettimeofday ()`) and do not respect remaining `Config.g_total_timeout`.

### 1.2 Existing Pipeline Bugs
5. **Unsound / buggy rules in `binsec_simplify` (`src/utils/utils.ml:481,499,547,550`)**:
   - Line 547: passes `sx + sizeof b` instead of `sx` as the width argument during AC reassociation (`binary f (binary f a b sx) c (sx + sizeof b)`), which can synthesize wrong-width constants if a nested rule uses `sx`.
   - Line 550: rewrites `a - 1 -> ~a` (mathematically wrong; `-a - 1 = ~a`).
   - Line 481 (`0 / x -> 0`, `0 % x -> 0`) and line 499 (`x / x -> 1`) are unsound at `x = 0` under total SMT-LIB bitvector semantics.
   - `Rewrite.accepts` catches these in `prepare_candidates`, so they do not compromise soundness, but they waste proof/sample checks and discard otherwise valid algebraic post-simplifications.
6. **CHS horizon-skip bug (`src/greysynth/greysynth.ml:65-72`, `src/greysynth/synthesis.ml:339-367`)**:
   - At horizon `h`, `aux` attempts `process node` top-down *before* recursing into children. If child simplifications collapse `node`'s depth down to `h` (e.g., an obfuscated `(A_obf | B_obf) + (A_obf & B_obf)` of depth 4 collapses to `(x | y) + (x & y)` of depth 2 during `h = 2`), the outer loop increments `horizon` to `3`, and `if depth_of_expr node < horizon then node` skips `node` forever (and exits the loop if the root depth is now `< 3`).
   - **Fix**: When a horizon strictly shrinks `!best`, reset `horizon := 2` (or iterate small horizons `h = 2, 3` bottom-up to a local fixed point before escalating to larger, exponentially harder horizons).
7. **OES constant-slot clobbering (`src/greysynth/oes.ml:183-189`)**:
   - When a non-constant node evaluates identically on all 100 samples (e.g., sparse `target_6828`), `first_pass` overwrites its `cache[outhash]` bucket with the literal constant. If `Rewrite.accepts` rejects that constant, the bucket has lost the smallest *real* AST representative in that equivalence class.
   - **Fix**: Covered by Milestone 4's Pareto frontier—explicitly retain both the speculative constant *and* the smallest real AST nodes per semantic class.
8. **Misc state/cache/logging bugs**:
   - `src/greysynth/greysynth.ml:85-95`: `normalization`, `OES`, and `fast_simplify` all overwrite `log_linear_is_equiv`.
   - `src/greysynth/synthesis.ml:370`: uses `Hashtbl.add` instead of `Hashtbl.replace` on `chs_cache_per_horizon`, and caches `simplified_node` even after a partial timeout or when larger than an existing entry.
   - `src/greysynth/oes.ml:344-351`: `invert_kids` in `relational_pass` walks the entire subtree unbounded by `c_local_extend_depth` ($O(N^2)$ on large ASTs).

---

## 2. Live Probe Evidence: Where Current MBA Simplification Stalls

Probing the built binary (`default.json`, `total_timeout = 3`, `synthesis_timeout = 1`) on representative MBA families revealed the exact failure modes:

| Case | Width | Expected | Result (`obf -> syn`) | Diagnosis |
|---|---:|---|---|---|
| `((a^b)\|(a^c)) + 65469 * ~(a&b&c) + 65470 * (a&b&c)` | 16 | `67 + (a \| b \| c)` (size 7) | **24 -> 24** (`0` checks, 10 CHS fails) | `normalization.ml:268-282` only searches 1- and 2-var affine templates; Möbius AND-monomial output has size 25 > 24; CHS lacks constant `67` (`0xffbd + 0xffbe`) and has `xsmir_ops = ""`. |
| `((x^y)+2*(x&y)) + ((z^w)+2*(z&w)) + ((a\|b)+(a&b)) - x - y - z - w - a` | 64 | `b` (size 1) | **37 -> 21** (`inconclusive: 2`) | Hits the 4-atom cap (`normalization.ml:178`); no AC linear collector; single-shot 64-bit SMT proof on the 10-term sum timed out. |
| 14-term quadratic MBA (`poly_mba_cancel`) | 64 | `22*(x&y) - 17*x - 5*y` (size 11) | **167 -> 166** (4 CHS fails) | Non-constant `Mul` is opaque (`normalization.ml:195-199`); CHS local horizons see only small slices with no local cancellation. |
| `((x^y)+2*(x&y)) + (x*y - ((x&y)*(x\|y) + (x&~y)*(~x&y)))` | 64 | `x + y` (size 3) | **31 -> 25** (`inconclusive: 2`, CHS skipped) | **OES already found `0` and `x+y`**, but Bitwuzla timed out at 1s proving the 64-bit `bvmul` identity and burned the remaining budget retrying it. |
| `(a&~b&~c) \| (~a&b&~c) \| (~a&~b&c) \| (a&b&c)` | 64 | `a ^ b ^ c` (size 5) | **29 -> 7** (`c ^ (~b ^ ~a)`) | Möbius expansion of `a^b^c` has size 31 > 29; no post-CHS normalization or `(~x)^(~y) -> x^y` cleanup. |

---

## 3. Architectural Bottleneck Missing from `docs/PLAN.md`: Proof-Tractable Decomposed Certificates

**Key finding**: Simply adding Milestone 3's polynomial/semilinear normalizers or external candidate generators (`CoBRA`, `Rumba`, `GAMBA`) and handing their final `(original, candidate)` pair to `Rewrite.accepts` **will fail closed on 64-bit nonlinear and wide-sum MBAs**. As `zero_poly_ghost` and `linear_5var_sum` demonstrated, Bitwuzla bit-blasting routinely times out at 1–5s on single-shot 64-bit `bvmul` identities (`x*y = (x&y)*(x|y) + (x&~y)*(~x&y)`, invertible polynomials $P(Q(x))=x$, multi-term polynomial MBAs).

### Recommended Proof-Side Design (Spans Milestones 3 & 4)
1. **Emit compositional micro-steps from deterministic normalizers into `Rewrite_proof`**:
   - **Two-layer proofs for polynomial/quadratic MBAs**:
     - *Layer 1 (Linear disjoint-minterm basis, zero `bvmul`)*: Rewrite each bitwise factor over variables $(x, y, \dots)$ into sums of pairwise-disjoint minterms (e.g., $m_1 = x\&y,\; m_2 = x\&\neg y,\; m_3 = \neg x\&y$, so $x = m_1 + m_2$, $y = m_1 + m_3$, $x|y = m_1 + m_2 + m_3$). Because minterms are bitwise-disjoint, there are no carries; every Layer-1 equality is a tiny linear bitvector identity Bitwuzla proves in milliseconds.
     - *Layer 2 (Pure ring normalization over abstracted basis atoms, zero bitwise ops)*: Replace $m_i$ by fresh typed variables (leveraging `Rewrite_proof.abstract_pair`) and emit small ring micro-steps (distributivity, collecting like monomials, cancelling zero terms, Horner/polynomial composition reduction mod $2^w$). Each micro-step is trivial for Bitwuzla and replays cleanly through `mba_proof`'s congruence closure without extending the trusted computing base.
   - **Micro-steps for AC / linear-MBA / invertible-polynomial rewrites**: Emit small associative/commutative swaps, cancellations, and per-component linear reductions so neither producer acceptance nor `mba_proof` ever faces a monolithic 64-bit arithmetic chain.
2. **Budget-tagged inconclusive caching (`src/greysynth/rewrite.ml:80-82`)**:
   - Currently `Rewrite.proofs` only caches `Yes | No` and discards `Unknown | Timeout`.
   - Cache `(verdict, budget_used)` for `Unknown | Timeout` and skip re-checking unless a strictly larger budget is supplied. This stops OES/relational/CHS from repeatedly burning `equiv_timeout` on the same unprovable 64-bit pair.
3. **Reusable solver context (`src/utils/utils.ml:255-259`)**:
   - `are_equivalent_seconds` constructs and destroys a fresh Bitwuzla solver instance per rewrite check. Where `Libsolver` supports push/pop or incremental assertions, reuse a solver context across local obligations (respecting timeout reset / clean teardown on timeout).

---

## 4. Concrete Algorithmic Upgrades for MBA Simplification

### 4.1 Deterministic Normalizer (`src/greysynth/normalization.ml`, Milestone 3)
These directly target the two datasets where GreySynth trailed GAMBA in Paper Table 2 (`Synthetic MBA`: 1.4× vs 1.0×, 20.2s vs 3.5s; `C-MBA / MBA-Obfuscator`: 4.6× vs 2.6×, 97.9s vs 9.3s):

1. **2-value affine-Boolean extraction + 3/4-variable Boolean minimization**:
   - In `linear_candidates`, inspect the distinct values in `target`. Whenever `target` takes only **2 distinct values** $\{v_0, v_1\} \pmod{2^w}$, the entire expression equals $v_0 + (v_1 - v_0)\cdot B(a_1,\dots,a_k)$ (or $v_1 + (v_0 - v_1)\cdot \neg B$).
   - Synthesize minimal $B$ using an NPN-equivalence lookup table for $k \le 3$ (14 classes) and ANF/ESOP factoring / Shannon decomposition for $k = 4$. This immediately recovers `67 + (a | b | c)` and `a ^ b ^ c`.
   - For general multi-valued `target`, extract linear arithmetic weights ($\sum c_i a_i$) first, then group subsets with matching/negated Möbius coefficients into compact bitwise operations (`|`, `^`, `&`, `~`) rather than emitting raw AND-monomial expansions.
2. **Connected-component partitioning + sparse AC linear collector**:
   - Flatten `+`, `-`, unary `-`, `const * e`, and `e << const` into an internal sparse linear IR $\sum c_i t_i + c_0$ with no 4-atom or 256-node ceiling.
   - Partition bitwise terms by connected components of shared atoms, solve each component independently, and combine/cancel in the outer sparse sum. Add finite-difference auxiliary-variable elimination to drop dead atoms before truth-table solving.
3. **Bit-partitioned semilinear normalization for folded masks**:
   - `normalization.ml:211` only accepts `0` and `-1` as Boolean constants. Folded complementary masks like `(x & 0x1234) + (x & 0xedcb)` become two independent opaque atoms and fail to simplify.
   - Partition bit positions by the bit-vectors of all constant masks in the linear subexpression (at most $2^m$ non-empty bit classes, typically 2–8 in practice), solve the linear MBA per bit-partition, and reconstruct masked sums/ORs.
4. **Disjoint-minterm polynomial normalizer + permutation-polynomial inversion**:
   - Map bitwise factors over $\le 3$ shared variables into the carry-free disjoint-minterm additive basis and normalize in $\mathbb{Z}/2^w\mathbb{Z}[m_1,\dots,m_{2^k-1}]$. This deterministically collapses quadratic/polynomial MBAs (`Poly`, `poly_mba_cancel`, `zero_poly_ghost`) and yields the two-layer proof structure in Section 3.
   - Add univariate/affine permutation-polynomial inversion ($P(Q(x)) \equiv x \pmod{2^w}$ when linear coeff is odd and higher coeffs are even) to peel `MBA-Obfuscator`'s `non_polynomial+zero` layers.
5. **Internal-IR canonicalization + post-CHS normalization**:
   - Perform AC/distributive/linear canonicalization in an internal IR before projecting back to `Sexpr.Expr.t` and calling `Rewrite.accepts`, rather than requiring every intermediate step to strictly reduce local cost (`normalization.ml:347`).
   - Run lightweight normalization after each CHS horizon (alongside `oes_quiet` in `greysynth.ml:69`) and after final OES, so identities exposed by CHS (like `c ^ (~b ^ ~a) -> c ^ (b ^ a)` or newly adjacent additive terms) are immediately collapsed.
6. **Optional external MBA backends (`Rumba`, `CoBRA`, `binsnake-cobra`) as *local* subtree oracles**:
   - Note licenses: `../rumba` is MIT (~45–150 µs median on GAMBA's 41k corpus); `../CoBRA` and `../binsnake-cobra` are Apache-2.0.
   - Beyond whole-expression use, invoke them on **maximal pure-MBA subtrees** detected by `src/utils/mba_classifier.ml` inside mixed/non-MBA expressions (`C-BeyondMBA`, `OMVLL`), keeping GreySynth's proof boundary as the verifier.

### 4.2 OES, CHS & Synthesizer Pipeline (`oes.ml`, `synthesis.ml`, `synth_backends.ml`)
1. **DAG memoization across traversals**:
   - `normalization.ml:313` memoizes on `Sexpr.BvTbl`, whereas `oes.ml`, `synthesis.ml`, and `utils.ml` (`size_of_expr`, `depth_of_expr`) recurse over `Sexpr.Expr.t` as unmemoized trees. Memoizing DAG nodes prevents exponential slowdowns on deeply shared expressions (Tigress levels 6–8).
2. **Semantic-boundary truncation in CHS**:
   - Complement uniform depth truncation (`synthesis.ml:111-132`) with:
     - AC tree balancing (implementing the currently inert `balanced_tree` knob);
     - **Repeated-class truncation**: stop descending when hitting a node whose OES fingerprint appears $\ge 2$ times inside the target subtree, cutting cleanly at MBA rule argument boundaries even on unbalanced ASTs.
3. **Dynamic Xyntia grammar scoping via `Mba_classifier`**:
   - Switching `default.json` to `"xyntia_grammar": "full"` globally adds 7 extra operators—including **4 ternary division/modulo operators**—to every pure-MBA query, inflating Xyntia's mutation branching factor.
   - Inspect each synthesis subtree (and cut-leaf context) with `Mba_classifier.classify`: select `"mba"` for pure MBA subtrees, `"mba_shift"` when shifts appear, and `"full"` only when division/modulo/non-MBA ops are present.
4. **Derived constant seeding + two-stage XSmir escalation**:
   - Currently `outside_tools/xyntia/src/lib/oracle.ml:250` only seeds `1` plus verbatim subtree constants (`synthesis.ml:165-176`). Seed `0`, `-1`, `2`, and a bounded set of pairwise sums/differences/negations/complements of constants in the truncated subtree.
   - **Important XSmir constraint**: Xyntia's `LinearComb` (`outside_tools/xyntia/src/lib/distance.ml:677-705`), used by `Affine` and `Poly2`, **asserts** that the sample bank contains `(0,...,0)`, `(1,...,1)`, and **every one-hot basis vector** `(0,...,1,...,0)`. `sample_evaluator.ml:58-68` currently assigns every variable the same value on samples `0..4`, causing `Affine`/`Poly2` to raise `Assert_failure` (silently swallowed as `None` in `run_backend`).
   - Once Milestone 6 adds one-hot basis samples, use a two-stage schedule (Milestone 7): fast plain Xyntia probe first (0.1–0.3s, solving easy nodes in milliseconds), escalating to XSmir inference rules (`Offset,Xor,MaskOTF,Mul,ShiftLeft,UShiftRight` and `Affine,Poly2`) or `cvc5` only on misses.

---

## 5. Suggested Re-Ordering in `docs/PLAN.md`

1. **Move Milestone 8 (explicit cost models, at least `legacy` + `paper_ast` side-by-side) right after Milestone 2, before Milestone 3**:
   - `normalization.ml:26-46` currently gains "free" reductions by introducing `Uext`/`Sext`/`Restrict` wrappers that cost `0` in `legacy`. Adding Milestone 3–7 passes before `paper_ast` is tracked risks optimizing for cast artifacts that regress under AST/readability/instruction cost.
2. **Move Milestone 6 (structured & one-hot sample bank) before Milestones 5 and 7**:
   - Cuts spurious OES/CHS SMT proof calls immediately, guarantees reproducibility via explicit seeds/manifests, and unlocks XSmir's `Affine`/`Poly2` inference rules without `Assert_failure`.
3. **Add a Milestone 3/4 sub-item for proof-tractable decomposed algebraic certificates** (Section 3 above) and verify it on 64-bit quadratic/polynomial MBAs (`zero_poly_ghost`, `poly_mba_cancel`, ProMBA `Poly`/`Non-Poly`, and `C-MBA / MBA-Obfuscator`) with independent `mba_proof` replay.
