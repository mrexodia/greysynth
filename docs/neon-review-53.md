# GreySynth Round-53 Spec: Post-Cleanup Opaque-Atom Probing (`target_1349`/`1417`/`6350`) + `~A = -1-A` & `uext(~x)` Complementary Bridges (`96`-Bit `Tigress L5–L8`!) + `build_constants` `uext` / `~P - Q` Peeling (`target_2923`/`4853`)

**Baseline:** Round 52 (`2c10c6b` / `6a1ea1e` — `regression_smoke` **ALL-TIME RECORD `62/62` strict, `55/58` exact, `0.7995x`**; newly shrunk `Tigress L5 (195)` **`+17` more exact** pushing overall L5 to **`82.2%`**; refreshed `core_hard (334)` **`+43/334` more exact (`12.9%`!)**; Leeky `dev_64 (884)` **ALL-TIME RECORD `505/880` exact (`2.14x`)** with `mba-projection-v1` `52/54`, `mba-long-frontier-v1` `46/72`, `mba-stress64-v1` `9/96`, `mba-interactions-v1` `24/33`; `0` refutations across all 1,475 cases!).

**Zero proof-kernel changes required in Round 53** (`src/proof/rewrite_proof.ml` stays untouched!).

---

## 1. Post-Cleanup `run_root_semantic_probes` & Multi-Mode Opaque Probing (`src/greysynth/greysynth.ml`, `src/greysynth/norm_probes.ml`) — Collapses `target_1349` (`209 -> 5`), `target_1417` (`201 -> 5`), `target_6350` (`461 -> 5`)!

Forensic verification with `mba_equiv.exe` proved directly:
- On `tigress_lvl_5__target_1349` (`out=209`, `gt=5`) and `target_1417` (`out=201`, `gt=5`), abstracting the two `E.Mul` products `P` and `Q` into `(v0, v1)` yields a 49-node multiplication-free shell `shell(v0, v1) == v0 + v1` that **Bitwuzla proves in `0.082s` (32-bit) and `0.299s` (64-bit)** via `Rewrite_proof.abstract_pair`! Then `dag-product-peel` immediately collapses `P + Q -> GT (size 5)` with **ZERO SMT**!
- Why didn't `run_root_semantic_probes` collapse them in R52?
  1. Both `target_1349` (`t=4.53s`) and `target_1417` (`t=4.01s`) had `has_timed_out = true` by the time `Normalization.run` / `OES` reduced `15,770 -> 209`, AND `run_root_semantic_probes` was NOT called again after `Normalization.run` / `OES` shrunk the expression into `[9, 1024]`!
  2. In `src/greysynth/norm_probes.ml` (`probe_opaque_atoms`, lines 1139–1147), `probe_opaque_atoms` returns ONLY a single `E.t option` from the first mode that matches (`Arithmetic -> Shared -> Operator -> Maximal`). If an earlier mode returns a candidate whose proof times out (e.g. without abstracting `E.Mul` products `P` and `Q`), `attempt 'Operator` (which abstracts `P` and `Q` cleanly!) is NEVER tried!

**100% General Fixes:**
1. **In `src/greysynth/norm_probes.ml`:**
   - Add `probe_opaque_atoms_list ?(max_cost = 512) ?(maximal_repeated = true) cost expression : E.t list` that collects the best candidate from EACH of `Operator`, `Arithmetic`, `Shared`, and (if `maximal_repeated`) `Maximal`, deduplicated and sorted by cost ascending (putting `Operator` candidates on par so `P + Q` is NEVER shadowed by an unprovable mode!). Keep `probe_opaque_atoms` as the head wrapper for compatibility.
   - In `probe_opaque_atoms`'s `binary_templates` (and for `count = 3`): include `v0 + v1`, `v0 - v1`, `v1 - v0`, `v0 ^ v1`, `v0 | v1`, `v0 & v1` (with `c0` offset), AND for `count = 3` also include `v0 + v1 + v2`, `v0 + v1 - v2`, `v0 - v1 + v2`, `v1 + v2 - v0`, and each single `v_i` (with `c0` offset) — directly covering `target_6350` (`atoms = [P; Q; A*B] -> A*B`)!
2. **In `src/greysynth/greysynth.ml`:**
   - In `run_root_semantic_probes`: iterate through `probe_opaque_atoms_list ~max_cost:max_size size_of_expr !best` (trying up to 3 cheapest distinct candidates until one certifies!), and after accepting a candidate, run `nonlinear_product_identity_candidate` + `semilinear_mba_candidate` + `dag_bottom_up_simplify ~zero_smt:true` (1 quick pass) so `P + Q` immediately peels to `A * B` (size 5)!
   - Reserve a `0.8s` post-normalization probe window when `g_total_timeout >= 4.0` (e.g., cap `Normalization.run`'s soft deadline at `g_start_time +. !g_total_timeout -. 0.85` when `!best` has `size <= 2048`), AND invoke `run_root_semantic_probes ~max_size:1024 ~timeout:0.75 ()` **right after `Normalization.run` / `run_small_dag ()`** whenever `size_of_expr !best >= 9 && size_of_expr !best <= 1024` and `not !g_has_timedout`!

---

## 2. Universal `~A = -1 - A` Ring Bridge & `uext(k)(~x) = (2^w - 1) - uext(k)(x)` Complementary-Extension Bridge (`src/greysynth/norm_poly.ml`, `src/greysynth/norm_semilinear.ml`, `src/greysynth/normalization.ml`) — Unlocks 96-Bit / 128-Bit / 224-Bit `Tigress L5–L8` (`target_1776`, `target_1933`, ...)

Forensic inspection of the `56` remaining `wide_96` `Tigress L5` cases (`tigress_lvl_5__target_1776`: `out=568, gt=5`; `target_1933`: `out=536, gt=9`) revealed TWO missing universal identities:
1. **`~A` inside ring polynomials (`target_1776`: `(~A)*(A & B) + (1 + A)*(A & B) == 0`!):**
   - `ring_polynomial_candidate` currently treats `E.Unary { f = E.Not; x; _ }` as an opaque atom, so `(~A) * T + (1 + A) * T` never cancels to `0`!
   - **100% General Zero-SMT Fix (`ring_not_bridge_candidate` in `norm_poly.ml`):**
     - On a ring node (`E.Plus | E.Minus | E.Mul`, `cost <= 2048`, `dag_size <= 512`), scan ring-position subterms (`+`, `-`, `*`, unary `-`): if `E.Unary { f = E.Not; x; _ }` appears directly in a ring position AND `x` ALSO appears elsewhere in the expression (even inside `&`/`|`/`^` or another ring term!), replace `~x` in ring positions with `E.binary E.Minus (constant width (Z.neg Z.one)) x`, recording `(E.unary E.Not x, E.binary E.Minus (constant width (Z.neg Z.one)) x)` in **`linear_mba_equalities`** (proved in `< 0.1 ms` with **ZERO SMT** by `linear_mba_mod2w`!).
     - Run `ring_polynomial_candidate` on the substituted form; if strictly cheaper than `expression`, certify via `Rewrite.accepts_compositional ~pass:"dag-ring-not-mod2w" ~equalities:[] ~linear_mba_equalities ~ring_equalities:[ substituted, candidate ]` (**ZERO SMT**!).
2. **Complementary Zero-Extension `uext(amount)(~low_x) == (2^(sizeof low_x) - 1) - uext(amount)(low_x)` (`target_1776`, `target_1933`!):**
   - `target_1776` has BOTH `uext(32) x0<64>` AND `uext(32) (~ x0<64>)`; `target_1933` has BOTH `uext(32) x2<64>` AND `uext(32) (~ x2<64>)`!
   - Extend `complementary_slice_candidate` in `src/greysynth/norm_semilinear.ml` (lines 529–569): in addition to `uext(amount)(restrict(0, hi)(~base))`, ALSO match **`E.Unary { f = E.Uext amount; x = E.Unary { f = E.Not; x = low_x; _ }; _ }`** whenever `amount > 0` AND `E.unary (E.Uext amount) low_x` ALSO occurs in `expression`!
   - Rewrite `uext(amount)(~low_x)` to `E.binary E.Minus (constant (E.sizeof rebuilt) (Z.pred (Z.shift_left Z.one (E.sizeof low_x)))) (E.unary (E.Uext amount) low_x)`, recording the single local equality in `equalities` (already certified by `dag-complementary-slice` / `root-complementary-slice`!).
   - *(Note: gate `dag-complementary-slice` with `try_smt` + `~timeout:0.15` when `equalities <> []` so it never leaks SMT budget during `zero_smt = true`!)*

---

## 3. Complete `build_constants` `uext` Lifting + `~P - Q` Peeling in `src/greysynth/norm_semilinear.ml` (`target_2923`, `target_4853`, `target_1514`, `target_2123`!)

1. **`build_constants` `uext` Constant-Mask Lifting (`target_2923`: `283 -> 5`!):**
   - In `nonlinear_product_identity_candidate.build_constants.and_constant` (`norm_semilinear.ml` lines 800–805):
     ALSO match `E.Unary { f = E.Uext amount; x = E.Binary { f = E.And; x = E.Cst low_c; y = low_a; _ }; _ }` (and commuted `y = E.Cst low_c; x = low_a`), allowing it to pair in `try_pair` with `(~(uext(amount) low_a)) & wide_base` whenever `Bitvector.value_of low_c = Z.logand (Bitvector.value_of (Bitvector.lognot wide_base)) (low_mask (sizeof low_a))`! Record `(actual, E.binary E.And (E.unary (E.Uext amount) low_a) (E.constant (Bitvector.lognot wide_base)))` in `lifted_equalities`!
2. **`~P - Q` Additive Flattening (`target_4853`: `258 -> 5`!):**
   - In `nonlinear_product_identity_candidate.additive` (lines 845–855):
     When `node` is `E.Unary { f = E.Not; x = (E.Binary { f = E.Mul; _ } as prod); _ }`, record the linear bridge `(node, E.binary E.Minus (constant width (Z.neg Z.one)) prod)` and flatten it into `(sign, constant width (Z.neg Z.one))` + `(not sign, prod)`!
   - Then `(~P) - Q` immediately exposes `(-1) - P - Q` (both `P` and `Q` negative -> `sign = other_sign`!), peeling `(~P) - Q -> (-1) - (A * B)` with **ZERO SMT**!
3. **Inspect `tigress_lvl_5__target_1514` (`9283 -> 9283` stall in R52):**
   - Check why `target_1514` (`in = 9,283`, contains `(x1 & 0x4c)*(x1 | 0x4c) + (x1 & ~0x4c)*(~x1 & 0x4c)`!) stalled at `9,283` in R52 (`t = 20.55s`) — likely because `local_budget = 0.0` in `greysynth.ml:537` when `not shared && not exposed_product` or `dag_bottom_up_simplify` timed out! Fix cleanly so `target_1514` strictly collapses!

---

## 4. Verification Gate for Round 53 (Target Wall Time: ~12 min!)

1. **Full-Pipeline Regression Tests (`test/round53_test.ml`):**
   - `tigress_lvl_5__target_1349` (`15770 -> <= 5`!)
   - `tigress_lvl_5__target_1417` (`10874 -> <= 5`!)
   - `tigress_lvl_5__target_2923` (`4080 -> <= 5`!) and `tigress_lvl_5__target_4853` (`4080 -> <= 5`!)
   - `tigress_lvl_5__target_1776` (`96`-bit, `15861 ->` major collapse!)
   - `tigress_lvl_5__target_1514` (`9283 ->` strict reduction, no `in == out` stall!)
   - All independently replayed by `mba_proof`, warning-clean `make test`, **zero edits to `src/proof/rewrite_proof.ml`!**
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r53-*/out.jsonl`, do NOT run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r53-smoke/out.jsonl`): must keep **`62/62` strict decreases, `>= 54/58` exact, `<= 0.80x`, `0` refutations**!
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`195` shrunk cases -> `/tmp/r53-l5/out.jsonl` — target: **`>= 30/195` new exact `<= GT`, geomean `< 5.5x`**, pushing overall `Tigress L5` past **`83.5%+`!!**)
   - **`datasets/hard_cases/core_hard/`** (`334` refreshed cases -> `/tmp/r53-core/out.jsonl` — target: **`>= 50/334` new exact `<= GT`, geomean `< 4.5x`**!)
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r53-leeky-dev64/out.jsonl` — target: maintain/improve `>= 505/880` exact, `<= 2.15x`, `0` refutations!)
3. Record concise Round-53 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
