# GreySynth Round-61 Spec (Single-Focus): Cost-Minimizing `demorgan_not` (with `Xor` Pushdown) + Subtraction-Form `offer_linear_sum` (`R - (~B)`) + `~(A - B) -> B + demorgan_not A` (`norm_linear.ml` & `norm_peepholes.ml`)

**Baseline:** Round 60B (Full Corpus Prune Sweep #4 + Milestone-60 Held-Out Check — **NEW AUTHORITATIVE CORPUS-WIDE RECORD `51,442 / 52,647` (`97.711%`) EXACT `<= GT`** (`<= 1.25x`: `98.131%`, `<= 1.50x`: `98.308%`, `<= 2.00x`: `98.423%`), `0` refutations, `all_non_exact` shrunk `1,364 -> 1,206`, `core_hard` shrunk `328 -> 277`, `Tigress L5–L8` at `80.88%`, `mba_obf_nonlinear` & `neureduce` down to only 5 remaining cases each!).

**Scope:** Producer-side ONLY (ZERO `src/proof/rewrite_proof.ml` edits!). Two source files (`src/greysynth/norm_linear.ml` & `src/greysynth/norm_peepholes.ml`).

**Why This Single-Focus Change Closes Dozens of `GT+1` Remaining Cases Across 6+ Suites (100% General Boolean & Two's-Complement Algebra!):**
- Forensic scan of the `441` remaining non-Tigress non-exact cases found **`82` cases at `GT+1`** and **`64` at `GT+2`** (`146` within `GT+2`!), with TWO universal algebraic identities accounting for a massive chunk of them:
  1. **Cost-Minimizing `demorgan_not` with `Xor` Pushdown (`~(A ^ B) == (~A) ^ B == A ^ (~B)`):**
     - Currently `demorgan_not` in `src/greysynth/norm_linear.ml:20-33` blindly expands `~(x & y)` into `(~x) | (~y)` (cost **5** vs cost **4**!) AND completely omits `E.Xor`!
     - By taking the minimum-cost equivalent among:
       - `E.Unary { f = E.Not; x; _ }` -> `x`
       - `E.Binary { f = E.And; x; y; _ }` -> `min_cost (E.unary E.Not expr) (E.binary E.Or (demorgan_not x) (demorgan_not y))`
       - `E.Binary { f = E.Or; x; y; _ }` -> `min_cost (E.unary E.Not expr) (E.binary E.And (demorgan_not x) (demorgan_not y))`
       - `E.Binary { f = E.Xor; x; y; _ }` -> `min_cost (E.unary E.Not expr) (min_cost (E.binary E.Xor (demorgan_not x) y) (E.binary E.Xor x (demorgan_not y)))`
       we get **100% strictly-smaller-or-equal** Boolean negation everywhere!
     - Example: `~(z ^ (y & (~x)))` (cost 7) -> **`z ^ ((~y) | x)` (cost 6)** -> immediately closes `11 * (~(z ^ (y & (~x))))` (`9 -> 8` exact on `mba_flatten` lines `742, 820, 1740, 1818` & `pldi_nonpoly` lines `743, 821`!) AND `~(x & y)` stays cost 4 instead of blowing up to `(~x) | (~y)` (cost 5)!
  2. **Subtraction-Form `offer_linear_sum` (`R + (-(~B)) -> R - (~B)`):**
     - Currently `offer_linear_sum` (`norm_linear.ml:324-336`) combines `absorbed = scale (-offset) (demorgan_not body)` with `remaining` using `build_balanced E.Plus (absorbed :: values)`!
     - When `offset = 1`, `neg_offset = -1` (`mask`), so `absorbed` is `-(~B)` (cost `cost(~B) + 1`) and `Plus (-(~B), R)` wastes **1 extra node** compared to **`R - (~B)`** (`E.binary E.Minus (sum remaining) (demorgan_not body)`)!
     - Example: `1 + 3*x + (x & y)` (cost 9) -> **`3*x - (~(x & y))` (cost 8 = EXACT GT!)** -> immediately closes `mba_flatten` lines `145, 396, 1143, 1153, 1247, 1394, 1102`, `pldi_nonpoly` lines `146, 105`, and dozens more!
     - General rule in `offer_linear_sum`: whenever building ANY sum of `(coeff, body)` terms (both direct AND absorbed!), partition into `neg_one` (`Z.equal c mask`, coefficient `-1`) and `others` (`c <> -1`): if `others <> []`, subtract each `neg_one` body using **`E.Minus`** (instead of `Plus (-body)`)!
  3. **Direct Zero-SMT `~(expr)` & `~(A - B) -> B + demorgan_not A` Cleanup (`norm_peepholes.ml` + `normalization.ml`):**
     - For any `E.Unary { f = E.Not; x; _ }` (in `norm_peepholes.ml` `peepholes` AND as a tiny zero-SMT `linear_mba_mod2w` step in `dag_bottom_up_simplify` when `cost !result <= 64`):
       - Offer `demorgan_not x` whenever `cost (demorgan_not x) < cost (E.unary E.Not x)`.
       - When `x = E.Binary { f = E.Minus; x = a; y = b; _ }`, ALSO offer `E.binary E.Plus b (demorgan_not a)` whenever `cost (E.binary E.Plus b (demorgan_not a)) < cost (E.unary E.Not x)`!
         - Proof: `~(a - b) == -1 - (a - b) == b + (-1 - a) == b + (~a)` mod `2^w` (exact `linear_mba_mod2w`, ZERO SMT!).
         - Example: `~((((~x1) & x3) ^ x2) - x0)` (cost 9) -> **`x0 + ((x1 | (~x3)) ^ x2)` (cost 8 = EXACT GT** across `c_mba_obfuscator__target_1251`, `omvll__target_1251`, and `tigress_lvl_5..8__target_1251`!!).

---

## Exact Edits (`src/greysynth/norm_linear.ml`, `src/greysynth/norm_peepholes.ml`, & 1 tiny zero-SMT call in `src/greysynth/normalization.ml`)

1. **In `src/greysynth/norm_linear.ml`:**
   - Replace `demorgan_not` (lines 20–33) with a cost-minimizing version (using `Greysynth_utils.Utils.size_of_expr` — memoized or bounded depth `<= 12` so it is O(1) on small expressions and never blows up on large DAGs!):
     - Handles `Not`, `And`, `Or`, `Xor`, `Cst 0/-1`, picking the minimum-cost form at every node!
   - Upgrade `offer_linear_sum` (lines 306–337):
     - Write `build_signed_sum terms` so terms with `Z.equal c mask` (`-1`) are folded via **`E.Minus`** onto the non-`-1` sum (when non-empty!), and use `build_signed_sum` for BOTH the direct form AND the `offset`-absorbed form (so `1 + 3*x + (x & y)` emits `3*x - (~(x & y))` at cost **8**!).
   - Also in `linear_candidates_with_rings` (`lines 529–531` and `554–555`), use the new cost-minimizing `demorgan_not` (safe for ALL `count`, not just `count = 3`, because it never increases cost!).
2. **In `src/greysynth/norm_peepholes.ml` (`peepholes`) & `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`):**
   - Add a tiny helper `not_pushdown_candidate cost expression` (bounded to `cost expression <= 64`):
     - On `E.Unary { f = E.Not; x; _ }`: try `demorgan_not x`, and if `x = E.Binary { f = E.Minus; x = a; y = b; _ }` also try `E.binary E.Plus b (demorgan_not a)`, returning the smallest strictly cheaper candidate (`cost cand < cost expression`)!
   - Invoke `not_pushdown_candidate` inside `dag_bottom_up_simplify` (certified **100% ZERO-SMT** via `Rewrite.accepts_compositional ~pass:"dag-not-pushdown" ~equalities:[] ~linear_mba_equalities:[ !result, candidate ] !result candidate`) and in `peepholes`!

---

## Verification Gate for Round 61

1. **Regression Tests (`test/round61_test.ml`, plus warning-clean `make test`):**
   - `1 + 3*x + (x & y)` -> cost `8` (`3*x - (~(x & y))`), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `11 * (~(z ^ (y & (~x))))` -> cost `8` (`11 * (z ^ ((~y) | x))`), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `~((((~x1) & x3) ^ x2) - x0)` -> cost `8` (`x0 + ((x1 | (~x3)) ^ x2)`), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `1 + b + 2 * (x & (~b))` -> cost `9`, zero-SMT `linear_mba_mod2w`!
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r61-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r61-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r61-leeky-dev64/out.jsonl`)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`165` newly-shrunk cases -> `/tmp/r61-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`277` newly-refreshed cases -> `/tmp/r61-core/out.jsonl` — expect immediate exact `<= GT` wins across `mba_flatten`, `pldi_nonpoly`, `c_mba_obfuscator`, `omvll`, `Tigress L5–L8`!)
3. Record concise Round-61 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
