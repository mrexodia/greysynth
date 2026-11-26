# GreySynth Round-29 Spec: Known-Bits Abstract Interpretation, Arity-Budgeted Horizon Truncation / Dead-Stub Filtering & Low-Width Exact Vectorial ANF

**Baseline:** Round 28 (Black-Box `{0,1}^k` linear + `{0..d}^k` Newton–Mahler semantic probing & Loki cross-branch semantic DAG CSE)  
**Sources (from `docs/LITERATURE_ANALYSIS.md`):**
- **SimbaS / ProMBA** (`ccs23.md`) — Forward bitvector known-0 / known-1 bitmask abstract interpretation (`known_zero`, `known_one`) for pruning & algebraic simplification
- **GreySynth §6** (`2026-ccs.md`) — Arity-budgeted non-uniform horizon truncation (expanding frontier nodes along shared OES fingerprints while capping $|\text{Vars}| \le k_{\max}$ instead of blind uniform syntactic depth!)
- **Xyntia §8.1** (`3460120.3485250.md`) — Dynamic dead-variable / fake-input perturbation filtering before synthesis
- **BSc Thesis §2.4.2 & §3.2.3** (`bsc.md`) + **Eyrolles PhD §4.2** (`75068_EYROLLES_2017_archivage.md`) — Low-width exact vectorial ANF (`w <= 8` or demand-narrowed byte/nibble masks) & CEGIS distinguishing inputs

**Primary targets:**
- **`datasets/hard_cases/all_failing/tigress_l7/`** (89) & **`tigress_l8/`** (143) & **`qsynth_ea/`** (60) & **`loki_tiny/`** (`--limit 100`)
- **`datasets/hard_cases/core_hard/`** (406 non-GB) & **`datasets/hard_cases/regression_smoke/`** (62 guards)

---

## 1. Forward Known-Bits Abstract Interpretation (`src/greysynth/known_bits.ml`, `.mli` & `normalization.ml`)

Implement a clean, fast, sound forward bitvector abstract domain `(zeros : Z.t, ones : Z.t)` (where bit `i` of `zeros` = 1 means bit `i` is **guaranteed 0**, bit `i` of `ones` = 1 means bit `i` is **guaranteed 1**, invariant `(zeros & ones) == 0`, DAG-memoized in $O(|V_{\text{DAG}}|)$!):

**Exact sound transfer functions (width $w$, mask $M = 2^w - 1$):**
- `Cst c`: `zeros = M ^ c`, `ones = c`
- `Var _`: `zeros = 0`, `ones = 0`
- `Not x`: `zeros = x.ones`, `ones = x.zeros`
- `And (x, y)`: `zeros = x.zeros | y.zeros`, `ones = x.ones & y.ones`
- `Or (x, y)`: `zeros = x.zeros & y.zeros`, `ones = x.ones | y.ones`
- `Xor (x, y)`: `zeros = (x.zeros & y.zeros) | (x.ones & y.ones)`, `ones = (x.zeros & y.ones) | (x.ones & y.zeros)`
- `Lsl (x, Cst k)`: if `k >= w` then `(M, 0)` else `zeros = ((x.zeros << k) | ((1 << k) - 1)) & M`, `ones = (x.ones << k) & M`
- `Lsr (x, Cst k)`: if `k >= w` then `(M, 0)` else `zeros = (x.zeros >> k) | (M ^ ((1 << (w - k)) - 1))`, `ones = x.ones >> k`
- `Asr (x, Cst k)`: sign-bit known propagation!
- `Plus (x, y)` (exact carry-propagation lower/upper bound!):
  - `min_sum = x.ones + y.ones`, `max_sum = (M ^ x.zeros) + (M ^ y.zeros)`
  - Carry-out cannot alter bits where `(min_sum ^ max_sum)` is 0, AND standard LLVM/Hacker's Delight exact known-bits addition formula:
    `possible_carry = (x_max + y_max) ^ (x_min + y_min)` / exact `carry_zero` & `carry_one`!
  - Plus **disjoint-bits shortcut**: if `(M ^ x.zeros) & (M ^ y.zeros) == 0` (no bit position can be 1 in both `x` and `y`!), then `x + y == x | y` (ZERO carry anywhere -> `ones = x.ones | y.ones`, `zeros = x.zeros & y.zeros`!)!
- `Mul (x, y)`: trailing zero count `ctz(x) + ctz(y)` guaranteed zero; plus constant-bit mask when one operand is `Cst`!
- `Uext (n, x)`: high `n` bits guaranteed zero!
- `Restrict (lo, hi, x)`: slice `(zeros >> lo) & sub_mask`, `(ones >> lo) & sub_mask`!
- `Ite (c, t, e)`: `zeros = t.zeros & e.zeros`, `ones = t.ones & e.ones` (or exact branch if `c` is known `0`/`1`!).

**High-Value Constructive Simplifications Enabled by Known-Bits (all gated via `Rewrite.accepts`!):**
1. **Exact constant collapse:** whenever `(zeros | ones) == M`, the expression is **provably constant `ones`**!
2. **Redundant mask / bitwise identity elimination:**
   - `x & c` where `((M ^ c) & x.zeros) == (M ^ c)` (every cleared bit of `c` is ALREADY known 0 in `x`!) $\to$ `x`!
   - `x | c` where `(c & x.ones) == c` $\to$ `x`!
   - `x + y` where `(M ^ x.zeros) & (M ^ y.zeros) == 0` $\to$ `x | y` (or `x ^ y`!), unlocking linear/semi-linear MBA cancellation!
   - `x & y` where `(M ^ x.zeros) & (M ^ y.zeros) == 0` $\to$ `0`!
   - `x <u Cst k` where `max_unsigned(x) = M ^ x.zeros < k` $\to$ `1` (and `min_unsigned(x) = x.ones >= k` $\to$ `0`) — directly collapsing opaque comparison predicates & `ITE` guards!
   - `x == Cst k` where `(k & x.zeros) <> 0 || ((M ^ k) & x.ones) <> 0` $\to$ `0` (impossible equality -> collapses dead `ITE` branches!).
3. **Prune impossible candidates inside `Smir_interp.synthesize_exact`** (skip cores whose output known-bits contradict the target's observed bit envelope!).

---

## 2. Arity-Budgeted Non-Uniform Horizon Truncation & Dead-Stub Perturbation Filtering (`src/greysynth/synthesis.ml`)

1. **Dead-Stub Perturbation Filter (Xyntia §8.1):**
   - In `Synthesis.build_problem` / `synthesize`, when a truncated window has `k >= 2` Greek stubs, test each stub `i` by perturbing ONLY stub `i` across 4 concrete values while holding all other stubs fixed:
   - If the output is completely invariant to stub `i` across all 4 perturbations (e.g., cancelled by an opaque zero or masking!), try `Smir_interp` / synthesis **without stub `i`** first! (Always strictly verified by `Rewrite.accepts` on the restored original expression, so false dead-stub guesses are 100% rejected!)
2. **Arity-Budgeted Non-Uniform Truncation (GreySynth §6):**
   - Currently `truncate` cuts uniformly at depth `h`, which explodes stub count `k` on wide trees (stalling both `Smir_interp` and Xyntia!).
   - Add an **arity-aware truncation helper** for horizons `h >= 3`: when expanding a frontier node would push distinct Greek stub count above `k_max = 4`, ONLY expand children whose `outhash` already matches an existing stub (merging stubs instead of creating new ones!) or children with `<= 1` new variable! Keeps CHS stub arity compact (`<= 4`) at deeper horizons (`h = 3, 4, 5`) so `Smir_interp.synthesize_exact` stays in its sweet spot!

---

## 3. Low-Width Exact Vectorial ANF & Bit-Slice Synthesis (`w <= 8`, `src/greysynth/smir_interp.ml` / `normalization.ml`)

For 8-bit expressions (or subexpressions narrowed to `<= 8` bits via `restrict(0, 7, ...)` or `& 0xff` / `& 0x0f`):
- Add a tiny exact **bit-sliced / low-width algebraic normal form (ANF) recognizer** for `w <= 8` and `1 <= k <= 2` variables (`256` total inputs for 1-var 8-bit!):
  - Recognizes exact 1-var 8-bit affine/bitwise/shift/rotate/byte-swap/parity idioms (and exact `c_0 + c_1*x + ...` via full 256-point evaluation when `k = 1, w <= 8`, which is 100% exhaustive on `w <= 8`!) and feeds them cleanly through `Rewrite.accepts`!

---

## 4. Fast, Focused Verification Gate for Round 29 (Target Wall Time: ~4–6 min!)

1. **Unit & Soundness Tests (`test/round29_test.ml`):**
   - Known-bits transfer-function soundness tests (randomized Bitwuzla cross-check on 8-bit & 16-bit that `x & known_zeros == 0` and `x & known_ones == known_ones` hold for ALL ops: `~`, `&`, `|`, `^`, `+`, `*`, `<<`, `>>`, `>>s`, `uext`, `restrict`, `ite`!).
   - Constructive known-bits simplifications: `((x & 0xff) & 0xfff) -> x & 0xff`, `((x << 2) & 3) -> 0`, `((x & 0x0f) + (y & 0xf0)) -> (x & 0x0f) | (y & 0xf0)`, `((x & 0xff) <u 256) ? a : b -> a`, `((x | 1) == 0) ? a : b -> b` — all independently replayed via `mba_proof`!
   - Dead-stub perturbation filter test (`((x ^ x) * y) + (z + 1)` drops dead stub `y` cleanly!).
   - Arity-budgeted truncation test (keeps stub count `<= 4` on wide depth-4 trees!).
   - Low-width 8-bit exact recognizer test.
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/all_failing/tigress_l7/`** (89) & **`tigress_l8/`** (143)
   - **`datasets/hard_cases/all_failing/qsynth_ea/`** (60)
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases) & **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted!)
4. Record concise Round-29 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
