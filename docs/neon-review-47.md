# GreySynth Round-47 Spec: Bitwise-Atom Boundary Consistency in `norm_linear.ml` & `linear_mba_mod2w` (Zero-SMT Collapse of Compound Additive Atoms!)

**Baseline:** Round 46 (`228b793` / `afa7a45` — shrunk `Tigress L5` **`+30` new exact GT, `10.56x -> 8.53x`** (`Tigress L5` now `77.9%`!), refreshed `core_hard` **`+18` new exact GT, `7.07x -> 5.69x`**, `regression_smoke` **`62/62` strict decreases, `54` exact GT, `0.7921x`** (all-time best!), `mba-ladders-v1` `39 -> 46/72`, `mba-extra-floor-v1` `19 -> 23/54`, `mba-stress64-v1` `11.26x -> 9.14x`, `0` refutations).

**Forensic Diagnosis of `/tmp/r46-leeky-dev64/out.jsonl` (`mba-frontier64-v1` & `mba-stress64-v1` & `Tigress L5–L8`):**
Inspecting `2dda45799bcf74a9_w64` (`in = 2,025 -> out = 923`, `ref = 9`) and `7507b8965666bc39_w64` (`in = 2,119 -> out = 1,015`, `ref = 14`) exposed **one astonishingly clean, 100%-general algebraic blind spot** in BOTH `norm_linear.ml` and `Rewrite_proof.linear_mba_equal`:

- Consider ANY linear MBA containing a compound additive subexpression `A` (e.g., `A = (x0 & x1) + (x0 ^ x2)` in `mba-frontier64-v1`, or `A = x2*x4 + x0` / `x0 + x1` in `Tigress L5–L8`) that appears **BOTH** inside a bitwise operator (`A & B`, `~A`, `A | B`) **AND** in linear position (`A + B - 2*(A & B)`, `48*A + ...`)!
- Inside `A & B`, `boolean` / `collect_bitwise` MUST stop at `A` and intern `A` as an **atomic variable `a_0`**.
- **BUG:** In linear position (`A + B`), `linear` / `collect_linear` did **NOT** stop at `A` — it descended right THROUGH `A`'s `+` operator into `x0 & x1` and `x0 ^ x2`, splitting `A` into unrelated atoms `a_1, a_2, a_3` and **completely severing the algebraic identity between `A` in linear position and `A` in bitwise position**!
  - As a result, `linear_mba_mod2w` could NOT even prove `((x0 & x1) + (x0 ^ x2)) + B - 2*(((x0 & x1) + (x0 ^ x2)) & B) == ((x0 & x1) + (x0 ^ x2)) ^ B`!
  - In `mba-frontier64-v1`, EVERY 400-node zero-identity sub-MBA over `(A, B, M, x_i)` failed to collapse to `0` in one step and instead fragmented into 158 partial `dag-minterm-ring-poly` / `dag-ring-mod2w` steps that distributed `B = (x0 - x2)*(x1 | x2)` and timed out at `923` nodes!
- **Mathematical Soundness Theorem (100% Universal Substitution!):**
  If a set of subexpressions `S` (specifically, the non-bitwise atoms already forced opaque by `collect_bitwise`) are treated as **opaque atoms in BOTH `collect_bitwise` AND `collect_linear`** on both `left` and `right`, then checking `linear_mba_equal` with `S` treated as opaque atoms proves the equality holds for **ALL bitvector values** of each $a \in S$. By universal substitution, the concrete equality holds unconditionally! (It is strictly stronger, NEVER weaker — and if it returns `Ring_not_equal` or `Ring_limit_exceeded`, we simply fall back to the existing standard `linear_mba_equal` pass!)

---

## 1. Bitwise-Atom Boundary Consistency in `src/greysynth/norm_linear.ml` & `src/proof/rewrite_proof.ml`

1. **In `src/proof/rewrite_proof.ml` (`linear_mba_equal`):**
   - Factor the body of `linear_mba_equal` into a helper `linear_mba_equal_with_stops ~stop_ids g left right` where `stop_ids : (int, unit) Hashtbl.t`:
     - In `collect_linear id` and `linear id`: **FIRST** check `if Hashtbl.mem stop_ids id then add_atom id` (respectively `atom id` in evaluation/expansion)!
     - **Soundness invariant (CRITICAL):** `stop_ids` is ONLY checked in `collect_linear` / `linear` (and of course `collect_bitwise` ALREADY stops at any non-bitwise `id`, or stops at `stop_ids` too so BOTH sides treat `id` consistently as the exact same opaque atom!). Never skip `width` checks!
   - Compute `bitwise_atoms` with a tiny DAG-memoized pre-pass over `left` and `right`: collect every node `id` reached by `collect_bitwise` that `collect_bitwise` interns as an atom AND whose shape is a linear-position operator (`bvadd`, `bvsub`, `bvneg`, `bvmul`, `bvshl`) — i.e., compound linear subterms that ALREADY occur inside `&`, `|`, `^`, `~`!
   - Run order in `linear_mba_equal g left right`:
     1. If `Hashtbl.length bitwise_atoms > 0`, try `linear_mba_equal_with_stops ~stop_ids:bitwise_atoms g left right`. If it returns **`Ring_equal`**, return **`Ring_equal`** immediately!
     2. Otherwise, run the existing standard `linear_mba_equal_with_stops ~stop_ids:(Hashtbl.create 0) g left right` unchanged!
   - **Zero regression risk, 100% sound (universal substitution), and we MUST add both positive AND negative Bitwuzla cross-tests in `test/proof_test.ml`!**
2. **In `src/greysynth/norm_linear.ml` (`linear_candidates_with_rings`):**
   - Before running `linear`, run the exact same DAG-memoized pre-pass over `expression` to collect `bitwise_linear_atoms : unit Nodes.t` — every compound linear-position subexpression (`E.Binary { f = (E.Plus | E.Minus | E.Mul | E.Lsl); _ }` or `E.Unary { f = E.Minus; _ }`) that appears inside a bitwise operator (`&`, `|`, `^`, `~`)!
   - Note: ALSO canonicalize AC order (`canonical_ac_atom`) on `bitwise_linear_atoms` so if `(x0 & x1) + (x0 ^ x2)` appears inside `&` and `(x0 ^ x2) + (x0 & x1)` appears in linear position, they unify to the exact same opaque atom via `ring_mod2w`!
   - Try `linear_candidates_with_rings` with `bitwise_linear_atoms` treated as opaque atoms (in addition to `opaque_atoms`)! If that produces strictly cheaper candidates, offer them (and if `Nodes.length bitwise_linear_atoms > 0` and it yields `[]`, optionally fall back to the existing pass without stopping at `bitwise_linear_atoms` so nothing regresses!).
   - Also check `extract_product_scalar`: when `a * (k * b)` appears inside a bitwise op vs in linear position, `bitwise_linear_atoms` should NOT stop `extract_product_scalar` from pulling `k` out of `a * (k * b)` in linear position (since `a * b` is the atom inside `&`, NOT `a * (k * b)`!). Specifically: check `extract_product_scalar` **BEFORE** checking `bitwise_linear_atoms` on `E.Mul`!

---

## 2. Preserve Partial Work & Avoid Premature Polynomial Timeouts on `mba-stress64-v1` (`src/greysynth/greysynth.ml`, `src/greysynth/normalization.ml`)

Look at `7a3c5b5205027e63_w64` (`mba-stress64-v1`, `in = 3,066 -> out = 3,066`, `proved = 40`, `inconclusive = 1`, `t = 5.00s`):
- It proved `40` `dag-linear-mba` reductions inside `dag_bottom_up_simplify`, then hit a `5.00s` timeout in ONE `inconclusive` step and threw away ALL 40 proved reductions!
- Inspect why `7a3c5b5205027e63_w64` threw away its 40 proved reductions (`greysynth.ml` / `normalization.ml`):
  1. Ensure the early zero-SMT `dag_bottom_up_simplify ~zero_smt:true` prepass in `greysynth.ml` ALWAYS updates `best := ...` cleanly on soft timeout (preserving every memoized simplified subtree!), and give it up to `1.5s` (with `soft_stop` margin!) when `size > 512 && dag_size <= 4096`.
  2. In `dag_bottom_up_simplify`: during `zero_smt = true`, skip `nonlinear_poly_candidate` when `cost !result > 512` so the zero-SMT pass focuses 100% on collapsing linear/semilinear/product-peel factors first (`< 0.2s`!) before expensive polynomial expansion runs!
  3. Check why `mba-long-frontier-v1` dropped `44 -> 37` in R45/R46 (likely a side effect of `root-linear-group` or `polysim` budget on 10–16-var expressions) and restore it cleanly if it's a simple budget guard!

---

## 3. Verification Gate for Round 47 (Target Wall Time: ~8–10 min!)

1. **Proof-Kernel Positive + Negative Soundness Tests (`test/proof_test.ml`):**
   - Positive test: `linear_mba_mod2w` proves `A + B - 2*(A & B) == A ^ B` where `A = (x0 & x1) + (x0 ^ x2)` and `B = (x0 - x2) * (x1 | x2)` in `< 5 ms` (and independent `mba_proof` replay passes!).
   - Negative test: `linear_mba_mod2w` REJECTS a false identity over compound additive atoms (e.g., `A + B - (A & B) == A ^ B`, false at `A = 1, B = 1`), cross-checked with Bitwuzla `No`!
2. **Unit & Regression Tests (`test/round47_test.ml`):**
   - End-to-end test on a `2dda45799bcf74a9_w64`-style 400-node sub-MBA over `A = (x0 & x1) + (x0 ^ x2)`, `B = (x0 - x2) * (x1 | x2)`, `M = 7038830054286223081 & x2`, plus scalar `((x0 - x2) * (k * (x1 | x2)))`: verify zero-SMT collapse (`ring_mod2w` + `linear_mba_mod2w`) in `< 0.1s` with independent `mba_proof` replay!
   - Test `7a3c5b5205027e63_w64`-style sum of products of linear MBAs (`mba-stress64-v1`): verify strictly reduced output preserved well under `2.0s`!
   - Run `make test` — warning-clean, 100% green.
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain JSONLs under `/tmp/r47-*/out.jsonl`):**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases — **still keeping held-out `mba-balanced-v1` strictly untouched!** -> `/tmp/r47-leeky-dev64/out.jsonl` — target: **MASSIVE** jump on `mba-frontier64-v1` from `3/96` (`25.4x`) and `mba-stress64-v1` from `0/96` (`9.1x`), plus recovery of `mba-long-frontier-v1`!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`251` shrunk cases -> `/tmp/r47-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`342` refreshed cases -> `/tmp/r47-core/out.jsonl`)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases -> `/tmp/r47-smoke/out.jsonl` — must stay `62/62` strict decreases, `0` refuted, `<= 0.80x`!)
4. Record concise Round-47 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
