# GreySynth Round-44 Spec: Fix `substitute_equalities` Cycle (`qsynth_ea__line_0000026`) + Exact Bit-0 GF(2) Homomorphism Pushdown for `restrict(0, 0)`

**Baseline (Post-Round-43 Authoritative Corpus-Wide Prune):**
- **Corpus-Wide (`54,105` audited expressions across 32 suites):**
  - **Formally Proved:** **`54,094 / 54,102` (`99.985%`)**, **`0` refutations**!
  - **Exact `<= GT`:** **`50,414 / 52,647` (`95.76%`)** (up from `94.12%` in R34; **`+866` newly solved `<= GT`** in Round 43!)
  - **`all_non_exact/` shrunk:** **`3,100 -> 2,234`** (refreshed `core_hard/`: **`342`** rows, `regression_smoke/`: `62` rows).
- **Forensic Classification of the Newly Shrunk `all_non_exact/` (`Tigress L5–L8`: `1,159` remaining):**
  - **`179 / 335` (`53.4%`!)** of ALL remaining `Tigress L8` rows (and `41 / 251` of remaining `Tigress L5`, plus hundreds of `L6/L7`) are blocked by **`uext(w-1) (restrict(0, 0) <large arithmetic/shift/MBA subtree>)`**!
    - Example (`tigress_lvl_8__target_6526`, `899,428` AST): `uext(31) (restrict(0,0) (~ (((x1 | x0) << 1) - (x1 ^ x0))))` — bit 0 of `((x1 | x0) << 1)` is `0`, bit 0 of `A - B` is `A_0 ^ B_0`, so the ENTIRE inner subtree collapses immediately to `~ (restrict(0,0) x1 ^ restrict(0,0) x0)`!
    - Example (`tigress_lvl_8__target_1930`, `2880`, `3716`, `524`, `6909`): nested `uext(w-1) (restrict(0,0) (...))` layers wrapping huge arithmetic/shift/product MBAs!
  - **Deterministic crash caught in R43B:** `qsynth_ea__line_0000026` hit `Stack overflow` inside `Norm_semilinear.nonlinear_product_identity_candidate.substitute_equalities.visit` due to a cyclic replacement chain (`visit result` with no cycle guard).
  - **`target_547` (`3900 -> 3900` in `<96>`):** Contains `<< (uext(32) 0x10<64>)` — constant-cast folding wasn't applied before `zero_smt` peeling, blocking shift recognition!

---

## 1. Fix `substitute_equalities` Cycle Crash (`src/greysynth/norm_semilinear.ml`)

- In `nonlinear_product_identity_candidate` -> `substitute_equalities`:
  - Add an explicit `active = Nodes.create 16` cycle-guard set (using `Fun.protect` or clean add/remove around recursive calls): if `Nodes.mem active node`, return `node` immediately instead of looping infinitely!
  - Better still: do NOT call `visit` recursively on the replacement of a top-level replacement edge that has already been expanded, or only apply the substitution edges in a single non-cyclic pass (e.g. phased: `lifted` -> `complement_ring` -> `complement_linear` -> `factor_replacements`), AND keep the `active` cycle guard as defense-in-depth!
- Verify `datasets/hard_cases/all_non_exact/qsynth_ea/qsynth_ea__line_0000026.json` runs cleanly to an established proved verdict (`0` crash, `0` refutation) and add a unit test in `test/round44_test.ml`!

---

## 2. Exact Bit-0 `GF(2)` Homomorphism Pushdown for `restrict(0, 0)` (`src/greysynth/norm_peepholes.ml`, `src/greysynth/norm_probes.ml`, `src/greysynth/normalization.ml`)

**100% General, Elementary Modular-Arithmetic Theorem (`mod 2` is a ring homomorphism!):**
For ANY bitvector expression `e` of width `w >= 1`, extracting bit 0 (`restrict(0, 0) e`, width `1`) obeys exact local rules:
- `restrict(0, 0) (Cst c)` $\to$ `Cst (c & 1)<1>`
- `restrict(0, 0) (Not x)` $\to$ `Not (bit0 x)`
- `restrict(0, 0) (Unary Minus x)` $\to$ `bit0 x` (since `-x == x (mod 2)`!)
- `restrict(0, 0) (x + y)` $\to$ `(bit0 x) ^ (bit0 y)`
- `restrict(0, 0) (x - y)` $\to$ `(bit0 x) ^ (bit0 y)`
- `restrict(0, 0) (x * y)` $\to$ `(bit0 x) & (bit0 y)`
- `restrict(0, 0) (x & y)` $\to$ `(bit0 x) & (bit0 y)`
- `restrict(0, 0) (x | y)` $\to$ `(bit0 x) | (bit0 y)`
- `restrict(0, 0) (x ^ y)` $\to$ `(bit0 x) ^ (bit0 y)`
- `restrict(0, 0) (x << C)` where constant `C >= 1` $\to$ `0<1>` (and if `C = 0`, `bit0 x`)!
- `restrict(0, 0) (Uext _ x)` or `restrict(0, 0) (Sext _ x)` $\to$ `bit0 x`
- `restrict(0, 0) (Restrict { lo; hi } x)` when `lo = 0` $\to$ `bit0 x` (and when `lo > 0`, `Restrict { lo; hi = lo } x` — keeping exact 1-bit leaf!)
- Any other non-homomorphic leaf `t` (e.g. `Var`, `Udiv`, `Lsr`, `Ror`, variable shift, `Ite`) $\to$ `Restrict { lo = 0; hi = 0 } t` (width `1`!).

**Implementation (`bit0_restrict_homomorphism_candidate` — 100% DAG-memoized, strictly proof-gated!):**
1. Trigger on any `E.Unary { f = E.Restrict { lo = 0; hi = 0 }; x = inner; _ }` (or `E.Unary { f = E.Uext amount; x = E.Unary { f = E.Restrict { lo = 0; hi = 0 }; x = inner; _ }; _ }`!) when `cost inner >= 3` and `dag_size_bounded ~limit:1024 inner <= 1024`.
2. Push `restrict(0, 0)` down over `inner` using a DAG-memoized pass (`Nodes.t`), collecting the 1-bit Boolean leaves `L_1, ..., L_k` (each of width `1`, e.g. `restrict(0, 0) x_i` or `restrict(lo, lo) x_i` or `restrict(0, 0) (div_expr)`).
3. Simplify the resulting 1-bit Boolean DAG:
   - Always apply immediate 1-bit constant folds (`0 ^ a -> a`, `a ^ a -> 0`, `0 & a -> 0`, `1 & a -> a`, `1 | a -> 1`, `0 | a -> a`, `~0 -> 1`, `~1 -> 0`, `~~a -> a`, `a & a -> a`, `a | a -> a`, `a & ~a -> 0`, `a | ~a -> 1`, `a ^ ~a -> 1`)!
   - Whenever the number of distinct 1-bit leaves `k <= 5`: compute the **exact 1-bit truth table** (`2^k <= 32` entries, `< 0.05 ms`!) and synthesize the **minimum-size 1-bit Boolean expression** (constant `0`/`1`, single literal `L_i` or `~L_i`, 2-var op `L_i ^ L_j` / `&` / `|` / `~(...)`, or ANF/XOR-sum / `linear_candidates` at width 1!).
   - **CRITICAL PROOF STRATEGY (Compositional, ZERO giant SMT!):**
     - Do **NOT** throw `restrict(0, 0) <10,000-node inner> == <tiny 1-bit result>` as one giant monolithic SMT query (Bitwuzla would time out on 64-bit multiplies inside `inner`!).
     - Instead, certify **COMPOSITIONALLY** via `Rewrite.accepts_compositional`:
       - Emit the tiny local 1-step homomorphism equality for each DAG node `n` in `inner` where `bit0` was pushed (e.g., `restrict(0,0) (a + b) == restrict(0,0) a ^ restrict(0,0) b`, `restrict(0,0) (a * b) == restrict(0,0) a & restrict(0,0) b`, `restrict(0,0) (a << c) == 0<1>`), **plus** ONE `linear_mba_mod2w` (zero-SMT!) equality connecting the resulting 1-bit Boolean DAG to the minimized 1-bit candidate!
       - **WAIT — EVEN BETTER:** Every local step `restrict(0,0) (p + q) == restrict(0,0) p ^ restrict(0,0) q` is abstracted over `(p, q)` by `Rewrite_proof.abstract_pair` — Bitwuzla proves EACH unique operator schema (`+`, `-`, `*`, `&`, `|`, `^`, `~`, `<< c`) in **`< 2 milliseconds`**, AND `Rewrite.proofs` caches them (only `<= 10` total Bitwuzla queries even for a 500-node DAG!!)!
       - Wait: double-check `Rewrite_proof.abstract_pair` on `restrict(0,0) (a + b) == restrict(0,0) a ^ restrict(0,0) b` — both `a` and `b` occur on BOTH sides, so `abstract_pair` replaces `a -> $p0`, `b -> $p1` automatically, proving `restrict(0,0) ($p0 + $p1) == restrict(0,0) $p0 ^ restrict(0,0) $p1` in **`1 ms`** (ZERO nonlinear ops from `a`, `b`!!)!
       - What about `restrict(0,0) (a << c) == 0<1>`? `a` only occurs on LHS, so if `a` is a giant nonlinear expression, abstracting `a` isn't done by `abstract_pair` — so for `restrict(0,0) (a << c) == 0<1>` when `cost a > 16`, emit `(a << c) & 1 == 0`? Even simpler: `restrict(0,0) (a << c) == (restrict(0,0) a) & 0<1>` (now `a` occurs on BOTH sides -> `abstract_pair` replaces `a -> $p0` -> Bitwuzla proves `restrict(0,0) ($p0 << c) == (restrict(0,0) $p0) & 0<1>` in **`1 ms`**!!), followed by `(restrict(0,0) a) & 0<1> == 0<1>` via zero-SMT `linear_mba_mod2w`!! **GENIUS!!**
     - Gate on `cost candidate < cost expression` (or strictly fewer AST nodes!) and wire into `dag_bottom_up_simplify` (in bounded-SMT mode, counting into `smt_spent`, AND notice once `bit0` collapses `restrict(0,0) (...)` inside `uext(w-1) (restrict(0,0) (...))`, `dag-semilinear-mba` and `probe_opaque_atoms` immediately collapse the parent layers!) AND into `local_candidates`!

---

## 3. Constant-Cast Folding in Fast Pass (`target_547` & Wide `<96>`/`<224>` Shifts)

- In `dag_bottom_up_simplify` (`src/greysynth/normalization.ml`):
  - Currently `dag-constant-cast` only runs when `not zero_smt`. On `target_547` (`3900 -> 3900`), `uext(32) 0x10<64>` sits on the RHS of `<<`, preventing shift-aware `linear_mba_mod2w` / `semilinear_mba_mod2w` from recognizing the shift constant during the `zero_smt` pass!
  - Make `constant_cast_fold_candidate` check pure syntactic constant casts (`uext C`, `sext C`, `restrict C`) — wait, it needs a 1ms proof edge (`Rewrite.accepts ~allow_equal_cost:true`), so in `greysynth.ml` run a single ultra-fast `constant_cast_only` pre-pass (or allow `dag-constant-cast` on pure `E.Cst` children with a tiny `0.15s` cap!) when `expression` contains any `Uext`/`Sext`/`Restrict` applied directly to `E.Cst`!

---

## 4. Verification Gate for Round 44 (Target Wall Time: ~6–8 min!)

1. **Unit & Regression Tests (`test/round44_test.ml`):**
   - `qsynth_ea__line_0000026` regression test: verify `greysynth` does NOT stack-overflow and produces a proved, replayed output!
   - Bit-0 `GF(2)` homomorphism pushdown tests (with independent `mba_proof` replay):
     - `restrict(0,0) (~ (((x1<32> | x0<32>) << 1) - (x1<32> ^ x0<32>)))` -> `~(restrict(0,0) x1 ^ restrict(0,0) x0)` (or equivalent size <= 4, proved compositionally in `< 0.1s`!)
     - `uext(63) (restrict(0,0) (((x0 * x1) + (x2 << 3)) - (x0 * x1)))` -> `0<64>` (constant collapse through nonlinear products & shifts, `< 0.1s`!)
     - `uext(63) (restrict(0,0) (((x0<64> + x1<64>) ^ 1) + ((x2 * x3) << 1)))` -> collapses inner bit-0 cleanly!
   - Constant-cast shift pre-fold test: `(uext(32) x0<64>) << (uext(32) 0x10<64>)` folds `uext(32) 0x10<64> -> 0x10<96>` cleanly.
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r44-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (NOW SHRUNK to **`251`** remaining hard cases! -> `/tmp/r44-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (NOW REFRESHED to **`342`** remaining hard cases! -> `/tmp/r44-core/out.jsonl`)
   - **`datasets/hard_cases/all_non_exact/qsynth_ea/qsynth_ea__line_0000026.json`** (verify clean established proof, `0` crash!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases -> `/tmp/r44-smoke/out.jsonl` — must stay `62/62`, `0` stalls, `0` refuted, `<= 0.80x`!)
3. Record concise Round-44 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, `docs/EXTENDED_AUDIT_WAVE*.md`, or `src/proof/rewrite_proof.ml`).
