# GreySynth Round-25 Spec: Decidable `semilinear_mba_mod2w` (Non-Uniform Constants), $2^k$-Pullout, Demand-Bit Width Narrowing & Alternation-Reducing Proof Bridge

**Baseline:** Round 24 (Quotient-Ring DAG `poly_mod2w`, `BitTrans`-to-`poly_mod2w` hybrid solving `Permutation64` `13/13` to `< GT`, centered sparse recovery, 6-step Newton inversion!)  
**Sources (from `docs/LITERATURE_ANALYSIS.md`):**
- **MSiMBA** (Skees, `2406.10016v2.md`, Thm 1.0–1.1 & §5–§6) — Decidable $O(w \cdot 2^t)$ bit-slice signature matrix for semi-linear MBAs with arbitrary non-uniform bitwise constants + closed-form modular don't-care merging
- **Eyrolles PhD** (`75068_EYROLLES_2017_archivage.md`, §3.1, §3.4.3, §4.1.3) — Disjoint bitmask partitioning for arbitrary-constant linear MBAs, $2^k$-factor pullout out of bitwise ops, backward `& (2^k - 1)` width narrowing
- **RUMBA** (`arxive.md`, §7.1) — Dynamic masking `&(2^m - 1)` and shift-width narrowing `<< k`
- **GAMBA** (`2305.06763v2.md`, §5.2) — Power-of-2 bitwise factoring + disjoint-constant bitwise merging
- **MSc Thesis** (`msc.md`, Ch. 3) — Staged alternation-reducing proof bridge (`E_orig -> E_bridge` algebraically, SMT only on `E_bridge == E_cand`)

**Primary targets:**
- **`datasets/hard_cases/all_failing/omvll/`** (the 89 weak + non-GB OMVLL cases like `target_2558` with `0xffffffff` / `0xffffffff00000000` constants!)
- **`datasets/hard_cases/all_failing/tigress_l5..l8/`** & **`datasets/hard_cases/all_failing/obfuscatorx/`** (7 cases) & **`datasets/hard_cases/all_failing/oses/`** (4 cases)
- **`datasets/hard_cases/core_hard/`** (413 cases) & **`datasets/hard_cases/regression_smoke/`** (62 guards)

---

## 1. Decidable `semilinear_mba_mod2w` Proof Kernel Rule (`src/proof/rewrite_proof.ml`, `.mli`)

Today `linear_mba_mod2w` strictly treats ANY non-uniform constant (`c <> 0 && c <> -1`) inside `& | ^ ~` as an opaque atom, so valid semi-linear MBA identities like:
- `(x & 0xff) + (x & ~0xff) == x`
- `(x & 0x55) + (x | 0x55) == x + 0x55`
- `(x & 0x0f) + (x & 0xf0) == x & 0xff`
- `((0 - x0) - ((~x0) | 0xffffffff00000000)) - 0x100000000 == x0 & 0xffffffff` *(from `omvll/target_2558`!)*
- `(2 * x) ^ (2 * y) == 2 * (x ^ y)` *(power-of-2 shift-mixed!)*
cannot be certified by `linear_mba_mod2w`.

**Exact mathematical theorem (MSiMBA Theorem 1.0–1.1 & Eyrolles Disjoint Bitmask Partitioning):**
Let $E(a_0, \dots, a_{k-1})$ be a **semi-linear MBA** of width $w \le 128$ over $k \le 6$ opaque atoms $a_0, \dots, a_{k-1}$:
- **Linear arithmetic layer:** `const v`, `bvadd`, `bvsub`, `bvneg`, `bvnot` (`-1 - e`), `bvmul(const, _)`, `bvshl(_, const)`, and pure-bitwise subexpressions (note: `bvshl` by constant $s$ is *also* allowed inside bitwise ops as a bit-aligned shift ONLY if we handle it in the bit-slice evaluator — wait: be careful! `(x << s) & y` mixes bit position $i$ of `y` with bit position $i - s$ of `x`, which breaks single-bit slice independence! So **CRITICAL SOUNDNESS RULE**: `bvshl` is allowed ONLY in the arithmetic layer as `* 2^s`, NEVER inside `bvand`/`bvor`/`bvxor` unless treated as an opaque atom!).
- **Semi-linear bitwise layer (`bvand`, `bvor`, `bvxor`, `bvnot`):** allows opaque atoms $a_0, \dots, a_{k-1}$ AND **arbitrary bitvector constants $c \in [0, 2^w - 1]$** (uniform OR non-uniform!). Any arithmetic node (`bvadd`, `bvmul`, `bvshl`, etc.) inside bitwise ops is still treated strictly as an **opaque atom**!
- **Theorem (Exact Soundness & Completeness mod $2^w$):**
  Because every semi-linear bitwise term $B(\vec{a}; \vec{c})$ operates independently on each bit position $i \in \{0, \dots, w - 1\}$, its bitvector value decomposes as:
  $$B(\vec{a}; \vec{c}) = \sum_{i=0}^{w-1} 2^i \cdot B_i(a_{0,i}, \dots, a_{k-1,i}) \pmod{2^w}$$
  where $B_i(b) \in \{0, 1\}$ is the bit-$i$ truth table of $B$ (evaluating constant $c$ at bit $i$ to `(c lsr i) land 1`)!
  Therefore, for ANY semi-linear MBA $E$, defining $c_0 = E(0, \dots, 0) \bmod 2^w$ and for every bit $i \in \{0, \dots, w - 1\}$ and non-zero assignment $m \in \{1, \dots, 2^k - 1\}$:
  $$\Delta_{i, m}(E) := \big(E(2^i \cdot m_0, \dots, 2^i \cdot m_{k-1}) - c_0\big) \bmod 2^w$$
  (or directly evaluating bit-by-bit in the linear-combination representation: for each bit $i$, track the coefficient $t_i[m] \in \mathbb{Z}/2^w\mathbb{Z}$ of $2^i \cdot M_{m, i}$ where $M_{m,i}$ is bit $i$ of minterm $m$, canonicalized by $M_{0, i} = 1 - \sum_{m=1}^{2^k - 1} M_{m, i}$, so $c' = (c + \sum_{i=0}^{w-1} 2^i t_i[0]) \bmod 2^w$ and $d_{i, m} = (2^i (t_i[m] - t_i[0])) \bmod 2^w$!):
  $$L \equiv R \pmod{2^w} \iff c'(L) = c'(R) \;\land\; \forall i \in [0, w-1],\; \forall m \in [1, 2^k - 1],\; d_{i, m}(L) = d_{i, m}(R)!$$
  - **Double-check why $d_{i,m} = (2^i (t_i[m] - t_i[0])) \bmod 2^w$ is BOTH sound AND complete:**
    - Substituting $M_{0, i} = 1 - \sum_{m=1}^{2^k - 1} M_{m, i}$ into $c + \sum_{i=0}^{w-1} 2^i \sum_{m=0}^{2^k-1} t_i[m] M_{m,i}$ yields:
      $$c + \sum_{i=0}^{w-1} 2^i t_i[0] + \sum_{i=0}^{w-1} \sum_{m=1}^{2^k-1} \underbrace{2^i (t_i[m] - t_i[0])}_{d_{i,m} \bmod 2^w} M_{m,i} \pmod{2^w}!$$
    - **Automatic modular don't-cares!** Notice that multiplying by $2^i$ modulo $2^w$ AUTOMATICALLY zeroes out the top $i$ bits of $t_i[m] - t_i[0]$ — which is literally MSiMBA's `CanChangeCoefficientTo` / `CanChangeMaskTo` theorem (`v_2(m1 - m2) + i >= w`) built directly into the canonical form!!
    - **Even faster (Eyrolles Bitmask Grouping Optimization!):** Instead of running $w$ times, compute bit-parallel `Z.t` bitmasks directly! Even simpler: for $k \le 6$ (`2^k <= 64`) and $w \le 128$, evaluating $E$ on `(0,...,0)` and the $w \cdot (2^k - 1)$ single-bit inputs `2^i * m` is only **at most $128 \times 63 = 8,064$ scalar DAG evaluations** — or with Eyrolles's disjoint bitmask partition (grouping identical bit positions of the occurring constants into $r \le \min(w, 2^m)$ equivalence classes!), when only 1–4 constants appear ($r \le 16$), it's **at most $16 \times 63 = 1,008$ ops = < 0.5 milliseconds**!!
    - Wait: be super careful with Eyrolles's bitmask grouping vs exact per-bit check! On two bit positions $i < j$ that happen to share the same constant bits, $(t_i[m] - t_i[0]) \cdot 2^i \equiv 0 \pmod{2^w}$ has a *stricter* modulus ($2^{w-i}$) than bit $j$ ($2^{w-j}$), so checking **only the lowest bit `i = ctz(M_g)` of each uniform mask group $M_g$** is *sufficient* (and exact for all bits in $M_g$ simultaneously: if $2^{\text{ctz}(M_g)} \cdot \delta \equiv 0 \pmod{2^w}$, then $2^j \cdot \delta \equiv 0 \pmod{2^w}$ for every $j \in M_g$ because $j \ge \text{ctz}(M_g)$!!)!
    - Wait — let's double-check! What if on group $M_g$ with bits $\{0, 63\}$, bit 0 has $\delta = 0$ and bit 63 has $\delta = 2$ (which vanishes mod $2^1$ at bit 63)? Because every bit in $M_g$ has the **exact same constant bits**, the linear MBA has the **exact same coefficient $\delta = t_i[m] - t_i[0]$** at EVERY bit $i \in M_g$! So:
      $$\forall i \in M_g,\; 2^i \cdot \delta \equiv 0 \pmod{2^w} \iff 2^{\text{ctz}(M_g)} \cdot \delta \equiv 0 \pmod{2^w}!$$
      **WHAT A THEOREM!!** For a 64-bit expression with 3 non-uniform constants (at most $r \le 8$ distinct bit-tuples!), we ONLY evaluate $r \le 8$ mask groups (NOT 64 bits!), check `c'(L) = c'(R)` (summing `t_g[0] * M_g` mod $2^w$ — exact because $\sum_{i \in M_g} 2^i = M_g$!) and check `(t_g[m] - t_g[0]) * 2^(ctz(M_g)) == 0 (mod 2^w)` (exact!) — **< 0.2 milliseconds in `mba_proof`!!**

**Deliverables in `src/proof/rewrite_proof.ml` & `.mli`:**
1. Add equality rule `"rule": "semilinear_mba_mod2w"` + `Rewrite_proof.record_semilinear_mba` + `semilinear_mba_proofs` metric field in `verify` JSON output.
2. Implement `semilinear_mba_equal g left right` using the exact Eyrolles/MSiMBA disjoint-mask-group canonical theorem above (DAG-memoized, caps: `max_atoms = 6`, `width <= 128`, `max_mask_groups = 128`, `max_visited_nodes = 16_384`, `max_ops = 2_000_000`; fail closed!).
   - **CRITICAL SOUNDNESS RULE:** Any arithmetic node (`bvadd`, `bvsub`, `bvmul`, `bvshl`, `bvlshr`, `bvashr`, etc.) inside a bitwise op (`bvand`, `bvor`, `bvxor`) MUST remain a strict **opaque atom**! ONLY arbitrary bitvector constants and `bvnot`/`bvand`/`bvor`/`bvxor` enter the semi-linear bitwise layer!
3. **Mandatory Positive & Negative Bitwuzla Cross-Tests in `test/proof_test.ml`:**
   - Positive: `(x & 0xff) + (x & ~0xff) == x`, `(x & 0x55) + (x | 0x55) == x + 0x55`, `omvll/target_2558` mask identity `((0 - x0) - ((~x0) | 0xffffffff00000000)) - 0x100000000 == x0 & 0xffffffff`, modular don't-care `2 * (x & 0x80) == 0` on 8-bit (`v_2(2) + 7 = 8`), `(x << 3) & 0 == 0`? Wait — test `(2*x) + (2*y) == 2*(x+y)` and `2*(x & 0x7f) == (2*x) & 0xfe`? Note `(2*x) & 0xfe` has `2*x` under `&` so it's NOT semi-linear until $2^k$-pullout rewrites it first!
   - **Negative Bitwuzla cross-tests (8-bit & 16-bit, MUST be rejected by `semilinear_mba_mod2w` AND refuted by Bitwuzla!):**
     - `(x & 5) == x`
     - `2 * (x & 0x40) == 0` on 8-bit (one bit below the don't-care threshold `v_2(2) + 6 = 7 < 8`!)
     - `((x << 1) & y) == (x & y) << 1` (shift under bitwise is NOT bit-aligned — MUST be rejected!)
     - `((x + y) & 5) == (x & 5) + (y & 5)` (arithmetic under bitwise — MUST be rejected!)

---

## 2. Producer: Semi-Linear MBA Solver, $2^k$-Pullout & Backward Demand-Bit Narrowing (`src/greysynth/normalization.ml`, `rewrite.ml`, `egraph.ml`, `greysynth.ml`)

**Deliverables:**
1. **Wire `~semilinear_mba_equalities` through `Rewrite.accepts_compositional` and `Egraph` proof records**, recording via `Rewrite_proof.record_semilinear_mba`.
2. **Semi-Linear MBA Reducer (`semilinear_mba_candidate` in `src/greysynth/normalization.ml`):**
   - Triggers when an expression contains at least one non-uniform constant inside `& | ^ ~` (with $k \le 5$ opaque atoms, `dag_size <= 2048`).
   - Computes the exact disjoint-mask-group canonical signature `(c', d_g)` mod $2^w$:
     - **Linear shortcut (MSiMBA §6):** If all mask groups have compatible coefficients (via `v_2(m1 - m2) + ctz(M_g) >= w`), collapse directly to pure linear MBA (e.g., `(x & 0xff) + (x & ~0xff) -> x`, or `c_0 + sum c_i x_i`!).
     - **Per-basis mask merging & unmasking (MSiMBA §5.2–§5.3):**
       - For each non-empty conjunction $C_S$ (from per-group Möbius inversion!), collect `(mask, coeff)` pairs, drop zero/don't-care terms where `v_2(coeff) + ctz(mask) >= w`, merge disjoint masks with equal (or don't-care-compatible) coefficients into `(m1 | m2) & C_S`, and apply structural unmasking (`m*(~c & B) - m*(c & B) + m*c -> m*(c ^ B)` and `m1*(c & B) + m2*(~c & B) -> (m1 - m2)*(c & B) + m2*B`)!
     - **Single-edge certification:** Certify `original == candidate` with **ONE `semilinear_mba_mod2w` edge** (zero Bitwuzla SMT calls!)!
   - Wire into `dag_bottom_up_simplify`, `Normalization.local_candidates`, `Normalization.run`, and `Egraph.optimize`!
3. **Power-of-2 Factor Pullout from Bitwise Ops (Eyrolles §3.1 / GAMBA §5.2):**
   - Add local constructive rewrite rules in `Normalization.local_candidates` / `dag_bottom_up_simplify`:
     - `(2^k * A) & (2^k * B) -> 2^k * (A & B)` (and same for `|`, `^`, plus `(A << k) op (B << k) -> (A op B) << k`!)
     - `(2^k * C) & ~(2^k * A) -> 2^k * (C & ~A)` (handles Eyrolles's `254 & (-2x - 1) -> 2*(127 & ~x)`!)
     - `(2^k * A) & C` where `C` is divisible by `2^k` $\to$ `2^k * (A & (C >> k))`!
     - Certify via tiny 1-step local SMT / congruence edge (trivial for Bitwuzla on abstracted atoms `A, B`, `< 1 ms`!).
4. **Backward Demand-Bit Width Narrowing (Eyrolles §3.4.3 / RUMBA §7.1 / `bsc.md` Def 2.21):**
   - When a subexpression has the form `E & M` where `M = (1 << k) - 1` (low-$k$-bit mask, $1 \le k < w$) and `E` is built strictly from T-function ops (`+`, `-`, `*`, `&`, `|`, `^`, `~`, `<<`, constants):
     - Reduce every constant inside `E` modulo $2^k$ (immediately killing high-bit constant noise and exposing even-multiple zeroes like `(2*x + 4*y) & 1 -> 0`!).
     - Even better: check if `E` reduces modulo $2^k$ via our `poly_mod2w` / `ring_mod2w` / `linear_mba_mod2w` at **narrowed width $k$** (catching `(x*(x-1)) & 1 -> 0`, `(x*(x-1)*(x-2)*(x-3)) & 7 -> 0`, etc.!).
     - Certify via `restrict(0, k-1)` equivalence or 1-step `semilinear_mba_mod2w` / tiny local SMT edge!
5. **Alternation-Reducing Proof Bridge (`msc.md` Ch. 3) in `Rewrite.accepts` / `Egraph`:**
   - When an expensive direct SMT equality check `lhs == rhs` is about to run on a high-alternation expression (e.g., `size_of_expr lhs >= 32` and not already covered by a decidable rule), if fast decidable algebraic reduction (`linear_mba_mod2w` / `semilinear_mba_mod2w` / `ring_mod2w` / `poly_mod2w`) reduces `lhs -> lhs_bridge` with strictly lower size/alternation, record the decidable bridge edge `lhs == lhs_bridge` and query SMT on the much simpler `lhs_bridge == rhs` instead!

---

## 3. Fast, Focused Verification Gate for Round 25 (Target Wall Time: ~4–6 min!)

1. **Unit & Soundness Tests (`test/proof_test.ml`, `test/normalization_test.ml`, `test/round25_test.ml`):**
   - `semilinear_mba_mod2w` positive + mandatory negative Bitwuzla cross-tests (including off-by-one don't-care bit `2*(x & 0x40) == 0` on 8-bit, shift-under-bitwise trap, arithmetic-under-bitwise trap).
   - Direct regression tests (with independent `mba_proof` replay!):
     - `omvll/target_2558` (`((x0 & 0xffffffff) + (x1 & 0xffffffff))` exact collapse!)
     - Eyrolles constant-injection (`129 + x + 2*(127 & ~x) -> x ^ 127` on 8-bit) and `254 & (-2*x - 1) -> 2*(127 & ~x)`
     - Demand-bit narrowing (`(x * (x - 1)) & 1 -> 0`, `(x + 0x12345600) & 0xff -> x & 0xff`)
     - MSiMBA mask-merging (`(x & 0x0f) + (x & 0xf0) -> x & 0xff`, `(x & 0x55) + (x | 0x55) -> x + 0x55`).
2. **Run `make test`** — 100% green.
3. **Fast Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB; skip the 7 >80 MB flat-text OMVLL files in parallel 20s batches or note their text sizes explicitly!):**
   - **`datasets/hard_cases/all_failing/omvll/`** (the 89 weak + non-GB OMVLL cases — target: strong jump in solved & quality!)
   - **`datasets/hard_cases/all_failing/obfuscatorx/`** (7 cases) & **`datasets/hard_cases/all_failing/oses/`** (4 cases)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted!)
   - **`datasets/hard_cases/core_hard/`** (413 cases — track overall solved count climbing!)
4. Record concise Round-25 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
