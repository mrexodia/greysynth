# GreySynth Round-40 Spec: Arithmetic-Atom Boundary Extraction for `probe_opaque_atoms` + Generalized Algebraic-Complement & Multi-Term Zero-SMT Product Peeling

**Baseline:** Round 39 (`9f6ba71` / `add8164` — `Tigress L5 all_non_exact` `25.41x -> 5.21x` with **`+155` new exact GT** and **`0` stalls**, refreshed `core_hard` `24.31x -> 3.43x` with **`+71` new exact GT** and **`353/353` direct parallel**, `Tigress L8` slashed **`7,861x -> 66.15x`** (119x better!), `regression_smoke` `62/62`, `53` exact GT, `0.8304x`, `0` refutations).

**Forensic Diagnosis of `/tmp/r39-core/out.jsonl` & `/tmp/r39-l5/out.jsonl`:**
Inspecting the residual `80–474`-node outputs of giant `Tigress L8` expressions (`target_126` `2.48M -> 80`, `target_3601` `2.66M -> 80`, `target_6503` `2.70M -> 96`, `target_3135` `2.48M -> 192`, `target_2818` `13k -> 16`, `target_1349` `50k -> 424`, `target_1169` `4.37M -> 474`) and the worst remaining `Tigress L5` cases (`target_4174` `3435`, `target_1187` `969`, `target_3135` `580`, `target_2136` `489`, `target_2127` `460`, `target_2923` `412`, `target_6014/6086/6027` `411`, `target_3728` `207`, `target_2968` `46`) revealed **two crystal-clear, 100%-general algebraic gaps**:

1. **Why `probe_opaque_atoms` missed `target_126` (`80`), `target_3601` (`80`), `target_6503` (`96`), `target_3728` (`207`), `target_2968` (`46`), `target_6014/6086/6027` (`411`):**
   - Look at `probe_opaque_atoms` (`src/greysynth/norm_probes.ml:851–857`):
     - `attempt true` (`shared_boundary`) stopped at **repeated bitwise/shift obfuscation-shell nodes** (like `((B | A) * 2) | (~(A ^ B))`, which appears twice!), producing `count > 3` atoms and aborting!
     - `attempt false` (`operator_boundary`) walked straight **through pure-arithmetic base atoms** (`A = (x1 * uext(16) x2) + x0`, `A = 0x10 - uext(60)(restrict(0,3)(x2+x0))`, `A = x0 + x1`) that sit *inside* bitwise/shift ops (`|`, `^`, `&`, `~`, `<<`), splitting `A` into sub-atoms whose sum has bit-carries inside `|`/`^` and breaking `{0, 1}^k` Möbius!
     - Inside `dag_bottom_up_simplify` (`normalization.ml`), `probe_opaque_atoms` was also gated at `cost <= 64`, skipping `80–256`-node shells completely!
2. **Why `nonlinear_product_identity_candidate` missed `target_2818` (`16 -> 3`), `target_4174` (`3435`), `target_2136` (`489`), `target_2127` (`460`), `target_1187` (`969`), `target_3135` (`192`/`580`), `target_2923` (`412`), `target_1349` (`424`):**
   - **Operand-order proof bug (`target_2818`):** In `build` & `build_constants` (`norm_semilinear.ml:602–666`), `substituted` hardcoded `(first_replacement * second_replacement) + (u * union_replacement)`. When `regular` is `(a | b) * (a & b)` (`union` on the LEFT, as in `target_2818`), congruence substitution produces `(union_replacement * u)`, which didn't match `(u * union_replacement)` without a ring-commutativity edge -> silently rejected as `smt_inconclusive`!
   - **Algebraic complements (`target_4174`, `2136`, `2127`, `1187`, `1349`):** `parse_cross` only matched syntactic `~B` (`E.Unary { f = E.Not; ... }`) or constant `~C`, missing algebraic complements `B'` where `B + B' == -1` (e.g. `-2 - S == ~(S+1)`, `-x0 == ~(x0 - 1)`, `0xffffffffffffffcd - x0 == ~(x0 + 0x32)`).
   - **Multi-term / negated additive sums (`target_2136`, `2127`, `1187`, `3135`):** `nonlinear_product_identity_candidate` only matched bare top-level `E.Plus (x, y)`, missing `(C - P1) - P2` and `P1 + (P2 + X)`!
   - **`uext(k)` around `&` (`target_3135`, `target_2923`):** `((uext(32) x0) | (uext(32) x2)) * (uext(32) (x0 & x2))` has `uext(32)` wrapped around `x0 & x2` instead of `(uext(32) x0) & (uext(32) x2)`.

---

## 1. Arithmetic-Atom Boundary Extraction & Full-Power `probe_opaque_atoms` (`src/greysynth/norm_probes.ml`, `src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

1. **Add `attempt_arithmetic_atoms` as the PRIMARY abstraction level in `probe_opaque_atoms`:**
   - Precompute a DAG-memoized table `has_bitwise_or_shift : bool Nodes.t` over `expression`:
     - True for `E.Unary { f = E.Not; _ }`, `E.Binary { f = (E.And | E.Or | E.Xor | E.Lsl); _ }`, or any node whose same-width child in the shell has `has_bitwise_or_shift = true`.
     - False for `Var`, `Cst`, `Uext`/`Sext`/`Restrict` (width-crossing boundary), `Udiv`/`Sdiv`/`Umod`/`Smod`/`Lsr`/`Asr`/`Rol`/`Ror`, and pure arithmetic trees (`+`, `-`, `*`) whose children all have `has_bitwise_or_shift = false`.
   - Walk top-down `collect ~inside_bw is_root node`:
     - If `E.sizeof node <> width` or `not (shell node)`: record `node` as an opaque atom.
     - Else if `not is_root && not (has_bitwise_or_shift node)` and `(inside_bw || (cost node >= 3 && freq node >= 2))`:
       - **Record `node` as an opaque atom** (do NOT split a pure-arithmetic subexpression like `(x1 * uext(16) x2) + x0`, `0x10 - uext(60)(restrict(0,3)(x2+x0))`, or `x0 + x1` that sits inside bitwise/shift ops!).
     - Else (node IS part of the bitwise/shift shell or root arithmetic): recurse into children, passing `inside_bw = (inside_bw || is_bitwise_or_shift_op node)`!
     - Never stop at a repeated bitwise/shift shell node — that guarantees `target_126`, `target_3601`, `target_6503`, `target_3728`, `target_2968`, `target_6014` extract the **exact `1–2` base atoms**!
   - Fallback order: `attempt_arithmetic_atoms ()` -> `attempt_shared_boundary ()` -> `attempt_operator_boundary ()`.
2. **Enrich candidate synthesis on `abstract_expression` (`1 <= count <= 3`):**
   - Keep `{0, 1}^k` Möbius + `linear_candidates ~max_atoms:3 cost raw`.
   - When `count = 1`: ALSO include `Smir_interp.analytical_candidates` on `abstract_expression` (recovering `p0 + C`, `p0 - C`, `(p0 & M) + C`, `p0 ^ C`, `a * p0 + b`, etc.)!
   - When `count = 2`: ALSO test direct affine-offset templates `p0 + p1 + c0`, `p0 - p1 + c0`, `p1 - p0 + c0`, `(p0 | p1) + c0`, `(p0 & p1) + c0`, `(p0 ^ p1) + c0` where `c0 = f(0, 0)` (filtered in `< 0.1 ms` by the 16 full-width samples!).
   - Keep the 16-sample full-width filter on `abstract_expression` (make sure the 16 samples use **independent** values per variable, e.g. varying seeds per `(sample_idx, var_idx)`, NOT correlated `seed + index * 0x9e37` which could accidentally correlate `p0 - p1`!).
3. **Raise `dag_bottom_up_simplify` size window for `probe_opaque_atoms` to `9 <= cost !result <= 256`:**
   - Inside `dag_bottom_up_simplify` (bounded-SMT mode, respecting `smt_budget`!), try `probe_opaque_atoms cost !result` up to `cost <= 256` (while keeping `probe_low_width_exact` / `probe_semantic_linear_mba` / `probe_semantic_poly` at `<= 64`).
   - Acceptance order for `probe_opaque_atoms` candidates (in both `dag_bottom_up_simplify`, `run_root_semantic_probes`, and `run_cleanup`):
     1. Zero-SMT `linear_mba_mod2w`,
     2. Zero-SMT `semilinear_mba_mod2w`,
     3. Bounded SMT `Rewrite.accepts ~timeout:0.20` (which automatically uses `Rewrite_proof.abstract_pair` to prove over `p_1..p_k` with zero nonlinear ops in `5–30 ms`!).

---

## 2. Generalized Zero-SMT Product Peeling (`nonlinear_product_identity_candidate`, `src/greysynth/norm_semilinear.ml`)

Upgrade `nonlinear_product_identity_candidate` so it stays **100% zero-SMT** (except optional tiny abstract bridge for `uext` distribution) and handles ALL four missing cases cleanly:

1. **Fix operand-order proof construction in `build` & `build_constants` (`target_2818` `16 -> 3`!):**
   - Preserve the exact left/right operand positions of `cross` (`left_cross * right_cross`) and `regular` (`left_reg * right_reg`) when constructing `substituted_cross` and `substituted_regular`, AND preserve the exact order of `cross` vs `regular` in `substituted_sum`.
   - Emit ONE clean `ring_mod2w` edge `(substituted_sum, E.binary E.Mul a b)` (since `ring_mod2w` is AC-commutative and handles all 8 factor permutations automatically!).
2. **Algebraic complement matching (`target_4174`, `2136`, `2127`, `1187`, `1349`):**
   - When matching `cross = (a & b_comp) * (a_comp & b)` (in any operand order), accept `b_comp` as the complement of `b` if EITHER:
     - **(a)** `b_comp` is syntactically `~b`, OR
     - **(b)** `b` and `b_comp` are constants with `b_comp == ~b`, OR
     - **(c)** `ring_polynomial_candidate cost (b + b_comp) == Some (fill width)` (i.e. `b + b_comp == -1 mod 2^w`, e.g., `-2 - S` and `S + 1`, or `-x0` and `x0 - 1`, or `0xffffffffffffffcd - x0` and `x0 + 0x32`!).
   - **Zero-SMT proof bridge for case (c):**
     - `ring_mod2w` proves `b_comp == -1 - b` (`E.binary E.Minus (E.unary E.Minus b) (integer width 1)`),
     - `linear_mba_mod2w` proves `-1 - b == ~b`,
     - Congruence + `linear_mba_mod2w` proves `(a & ~b) == a - (a & b)`,
     - `ring_mod2w` proves the final sum equals `a * b`!
     - **100% zero-SMT, independently replayed by `mba_proof`!**
3. **Multi-term & negated additive sum matching (`target_2136`, `2127`, `1187`, `3135`):**
   - Flatten any top-level `+/-` additive tree (up to 8 additive terms, DAG-safe) into signed terms `(sign : bool, term : E.t)` (`true` = `+`, `false` = `-`).
   - Scan pairs `(i, j)` with **equal sign** (`sign_i = sign_j`): if `(term_i, term_j)` matches `(cross, regular)` for `a * b`:
     - Replace the pair with `(sign_i, a * b)` alongside the remaining terms `rest`, producing `candidate`.
     - Certify via the exact same compositional zero-SMT proof: inner `linear_mba_mod2w`/`semilinear_mba_mod2w` edges for `cross` & `regular` factors + ONE `ring_mod2w` edge proving the substituted multi-term sum equals `candidate`!
4. **`uext(k)`-lifted `&` matching inside `parse_regular` / `parse_cross` (`target_3135`, `target_2923`):**
   - If `regular` has `(uext(k) X) | (uext(k) Y)` paired with `uext(k) (X & Y)` (or `(uext(k) X) | C` paired with `uext(k) (X & C_low)` where `C = uext(k)(C_low)`):
     - Recognize `uext(k) (X & Y)` as equal to `(uext(k) X) & (uext(k) Y)` (and similarly `uext(k) (X & C_low)` as `(uext(k) X) & C`, and `uext(k) (X & ~C_low)` as `(uext(k) X) & ~C` since the top `k` bits of `uext(k) X` are guaranteed `0`!)!
     - Record that single tiny abstract equality `(uext(k) (X & Y), (uext(k) X) & (uext(k) Y))` in `equalities` (abstracted over 1–2 fresh vars, Bitwuzla proves it in **`< 5 ms`**, zero nonlinear ops!) alongside the zero-SMT `linear_mba_mod2w` + `ring_mod2w` edges!

---

## 3. Verification Gate for Round 40 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round40_test.ml`):**
   - End-to-end tests with independent `mba_proof` replay covering:
     - `probe_opaque_atoms` with `attempt_arithmetic_atoms` on `target_126`-style 2-layer shift-MBA over `A = (x1 * uext(16) x2) + x0, B = uext(16) x3` (`80 -> 7` exact!), AND `target_3728`-style 1-atom shared arithmetic subterm `A = x0 + x1` (`-> A - 0x775cd0c7`)!
     - Operand-order product peel `target_2818`: `(uext(32) (((0xffffec77 & x0) * ((~x0) & 0x1388)) + ((x0 | 0x1388) * (x0 & 0x1388)))) -> uext(32) (x0 * 0x1388)` (zero-SMT!).
     - Algebraic-complement + multi-term negated product peel `target_2136`-style: `(C - (((x0 + 0x32) & x1) * ((x0 + 0x32) | x1))) - (((~x1) & (x0 + 0x32)) * (x1 & (0xffffffffffffffcd - x0))) -> C - ((x0 + 0x32) * x1)` (zero-SMT!).
     - `uext`-lifted product peel `target_3135`-style: `(((uext(32) x0) | (uext(32) x2)) * (uext(32) (x0 & x2))) + ((((~(uext(32) x0)) & (uext(32) x2)) * ((~(uext(32) x2)) & (uext(32) x0))) + x1) -> ((uext(32) x0) * (uext(32) x2)) + x1`!
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r40-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` cases — target: big jump past **`200+`** new exact GT and slash geomean from `5.21x` toward **`< 3.0x`**!)
   - **`datasets/hard_cases/core_hard/`** (`353` cases — target: big jump past **`90+`** exact GT and slash `Tigress L8` geomean from `66x` well below **`20x`** and overall `core_hard` below **`2.5x`**!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — must stay `62/62` established, `0` refuted, `<= 0.90x`!)
3. Record concise Round-40 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`, and do NOT touch `src/proof/rewrite_proof.ml`).
