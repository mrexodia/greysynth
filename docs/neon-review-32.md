# GreySynth Round-32 Spec: Closing the Exact Round-31 Survivor Bugs — Giant-DAG Peeling First, Full Möbius Component Splitting & Dual-Polarity Boolean Recovery, Complementary `uext(restrict(~X))` & Two's-Complement `~X` Canonicalization

**Baseline:** Round 31 (`7489c64` — `PLDI Poly` `2.57x -> 1.25x` (`62/62` improved), `MBA-Flatten` `2.71x -> 1.20x`, `C-MBA target_1685` `29,511 -> 5`, `core_hard` `6.25x -> 5.96x` with `213/405` exact GT, `regression_smoke` `0.9162x`).

**Forensic Root-Cause Diagnosis of `/tmp/r31-core/out.jsonl` (Why 5 Concrete Bugs Left 191 Survivors):**
Inspecting `/tmp/r31-core/out.jsonl` and `git show 7489c64` pinpointed **five exact, surgical root causes** behind almost all remaining large ratios:

1. **Giant-DAG `Tigress L8` (`1169`, `5697`, `1285`, `1281`, `3354`, `2790`, `6503`, `3601`, `5856`, `5710` — 1.86M–5.31M, 0% reduced!) & `OMVLL` (`771`, `798` — 3.07M):**
   - `greysynth.ml:351` runs `Oes.linear_simplify ~seed:false` **BEFORE** `dag_bottom_up_simplify` on `size > 100_000 && vars <> 3`. On 4–6 variable giant DAGs (`tigress_l8/1169` `t=12.59s`, `tigress_l8/5856` `t=6.06s`, `omvll/771` `lin_t=3.44s`), `linear_simplify ~seed:false` hangs past its `1.5s` branch deadline, sets `g_has_timedout := true`, and **starves `dag_bottom_up_simplify` completely** (even though `tigress_l8/5856` is just 3 nested layers of `((a&~b)*(b&~a)) + ((a&b)*(a|b)) -> a*b` and `omvll/771` has only **51 unique DAG nodes**!).
2. **`Neureduce` (`line_0000632`, `0000098`, `0000798`, `0000417`) & `PLDI Poly` (`line_0000904`, `0000795`) — Four Exact Bugs in `linear_candidates` & `partial_linear_sum_candidate`:**
   - **Unsigned `Z.compare` polarity bug (`line_0000632`):** `5*(v0|v1|v2) - 1` has values `{-1, 4}`; unsigned `Z.compare` puts `low = 4, high = 0xffffffffffffffff (-1)`, so `linear_candidates` only tried `truth = (v == -1)` (`~v0 & ~v1 & ~v2`), NEVER `truth = (v == 4)` (`v0 | v1 | v2`, giving `-1 + 5*(v0|v1|v2)`, exact GT size 9!).
   - **Missing `~B = -1 - B` shortcut (`pldi_poly/904`):** `7*~(x^(y^z))` evaluates to `(-7) + (-7)*(x^y^z)`; whenever `offset == normalize (-coeff)` (or `offset == coeff`), collapsing `offset + coeff * B` into `scale (-coeff) (~B)` saves the `+ offset` addition (2 nodes) and hits exact GT size 12!
   - **`partial_linear_sum_candidate` skipped `linear_candidates` (`pldi_poly/904`, `795`, `mba_flatten/2901`, `2792`):** In `normalization.ml:3264`, whenever `ring_polynomial_candidate` shaved even 1 node off `linear_sum`, `partial_linear_sum_candidate` returned immediately and **never ran `linear_candidates` on `linear_sum`**!
   - **Missing canonical Möbius dummy-var & connected-component splitting (`line_0000098`, `0000798`):** Round 31 only ran active-variable projection when `distinct = 2` AND `active < count`. `line_0000098` (`-4*v2 - (v3|v4)`) has `distinct = 4` (5 vars with 2 dummies `v0, v1`) and `line_0000798` (`-(~v0&(v1^v2)) + (v3|v4)`) has `distinct = 3` (5 vars splitting into `{v0,v1,v2}` + `{v3,v4}`!).
   - **Missing `<< k` constant shift = `* (1 << k)` inside linear/semilinear MBA (`neureduce/417`, `tigress_l7/1285`):** `((~v0 ^ (~v2 & v1)) << 1)` and `((d & -2) << 1) - (d ^ 1) == d - 1` failed linear/semilinear recognition because of `<< 1`!
3. **`mask_lift_candidate` Legacy-Cost Deadlock & Complementary `uext(w-k, restrict(0, k-1, ~X))` (`c_mba_obfuscator` ALL 5 remaining slice survivors `4575`, `3551`, `4796`, `4543`, `4551` + `Tigress` `uext(63)`):**
   - Under `Legacy` cost, `uext`/`restrict` cost 0 while `& mask` costs +2, so `if cost candidate < cost expression` in `mask_lift_candidate` was **ALWAYS FALSE**!
   - Even better: ALL 5 remaining `c_mba_obfuscator` slice survivors (`4575`, `3551`, `4796`, `4543`, `4551`) AND the `Tigress L6–L8` outer wrappers contain BOTH `u = uext(w-k, restrict(0, k-1, X))` and `uext(w-k, restrict(0, k-1, ~X))` (or `uext(w-k, restrict(0, k-1, ~u))`), which satisfy the exact constructive identity:
     $$\text{uext}(w-k, \text{restrict}(0, k-1, \sim X)) = (2^k - 1) - \text{uext}(w-k, \text{restrict}(0, k-1, X))$$
     and for $k = 1$, $u \cdot u = u$!
4. **Two's-Complement `~X` Peephole (`QSynth EA` `388`, `443`, `277`, `89` & `OMVLL` `1069`):**
   - `qsynth_ea/line_0000388` stopped at `((A + B) + 1) + ((-A - 1) | (-B - 1))` (size 43 vs GT 9 `A | B`) purely because `(-A) - 1` and `(-A) + 0xffffffffffffffff` were NOT canonicalized to `~A`!

---

## 1. Giant-DAG Peeling FIRST & Timeout-Safe OES (`src/greysynth/greysynth.ml`, `src/greysynth/oes.ml`, `src/greysynth/normalization.ml`)

**Deliverables:**
1. **Run `dag_bottom_up_simplify` BEFORE `Oes.linear_simplify ~seed:false` on giant shared DAGs** (`size_of_expr !best > 100_000 && dag_size_bounded ~limit:2048 !best <= 2048`):
   - Remove the pre-DAG `linear_simplify ~seed:false` call that starved `tigress_l8/1169`, `5697`, `5856`, `5710`, and `omvll/771`!
   - Keep `linear_simplify ~seed:false` ONLY as a **post-DAG fallback** if `size_of_expr !best > 100_000` *after* `dag_bottom_up_simplify` finishes, with a `0.5s` branch deadline AND an explicit `if is_timedout () then raise Timeout` check inside `Oes.linear_simplify`'s main loop so it can NEVER overrun by 10+ seconds!
2. **Enrich `dag_bottom_up_simplify` (including `minimal = true` on giant DAGs for small sub-DAGs `dag_size <= 64`)** and allow up to **12 shrinking rounds** (within `2.5s` local deadline):
   - Always run:
     - `peepholes` (including the new `-X - 1 -> ~X` and `((d & ~1) << 1) - (d ^ 1) -> d - 1` / `((a & ~b) << 1) - (a ^ b) -> a - b` / `((a & ~b) << 1) + (a ^ b) -> a + b` constant-shift linear identities!)
     - `known_bits_candidate` (collapses `(uext(63)(restrict(0,0)(...))) & 2 -> 0` and `(E << 1) << 1` / known-zero masks!)
     - `ring_polynomial_candidate` on sub-DAGs of `dag_size <= 64` (instantly cancels `((U - (U|V)) + V) + (U|V) -> U + V` in `omvll/771` & `798`!)
     - `nonlinear_poly_candidate` + explicit 2-atom product rule `((a & ~b)*(b & ~a)) + ((a & b)*(a | b)) -> a * b` (and commuted/permuted variants!) on sub-DAGs of `dag_size <= 128` (peels all 3 layers of `tigress_l8/5856` & `5710` from `1.86M -> 7`!)
     - `linear_candidates` (with `<= 3` atoms) on sub-DAGs of `dag_size <= 64` (including constant left-shifts `E << k` treated as `(1 << k) * E`!).
   - **Check flagship:** `tigress_l8/target_5856` (`1,858,527 -> <= 9`, exact GT `7`!), `tigress_l8/target_1169` & `tigress_l7/target_1285` (massive collapse!), `omvll/target_771` (`3,070,823 -> << 100`!), while `target_366` (`3.4M -> 11`), `target_3218` (`54k -> 5`), and `tigress_l7/l8 target_1016` (`-> 9`) stay 100% intact!

---

## 2. Dual-Polarity & `~B`-Shortcut Boolean Recovery + Canonical Möbius Connected-Component Splitting (`src/greysynth/normalization.ml`)

**Deliverables:**
1. **Fix `distinct = [low; high]` in `linear_candidates`:**
   - Run active-variable projection whenever `List.length active <= 4 && List.length distinct = 2` (DROP the `List.length active < count` requirement so 3-var and 4-var full-active functions get exact DNF/CNF/ANF/Shannon synthesis too!).
   - Try **BOTH polarities**:
     - Polarity 1: `base = low`, `delta = normalize (Z.sub high low)`, `truth = (v == high)`
     - Polarity 2: `base = high`, `delta = normalize (Z.sub low high)`, `truth = (v == low)`
   - For EVERY `(base, delta, boolean)` pair, ALSO emit the **complement shortcut** when `Z.equal base (normalize (Z.neg delta))`:
     - Since `(-delta) + delta * B = (-delta) * (~B)` (Wait — check sign carefully!! In 2's complement, `~B = -1 - B`, so `c * (~B) = -c - c * B`! Thus if `base = normalize (Z.neg coeff)` where `coeff = normalize (Z.neg delta)` — i.e., **`Z.equal base delta`**!! Check with an example: `7 * ~(x^y^z) = -7 - 7*(x^y^z)`: here `base = -7` (when `B=0`), `delta = -7` (so at `B=1`, value is `-14`), and `base = delta = -7`, giving `(-delta) * (~B) = +7 * (~B)`! Verify with `B = 0 -> ~0 = -1 -> 7*(-1) = -7`; `B = 1 -> ~1 = -2`... WAIT: in `{0, 1}` single-bit semantics, `~0 = 1` and `~1 = 0`, whereas in bitvector semantics `~0 = -1` and `~(-1) = 0`, so on the `{0, 1}` evaluation array of `linear_candidates`, `B=0 -> 0` and `B=1 -> 1`, while `~B` has value `~0 = 1` at `B=0` and `~1 = 0` at `B=1` — wait: in `linear_candidates`, how is `~` evaluated on `target`? CHECK `eval_linear_mba` in `normalization.ml`! Specifically, if `target` evaluates `~` as `1 - b` (`Not` in `{0,1}`), then `7 * ~(x^y^z)` has `target = 7` when `parity=0` and `target = 0` when `parity=1`, which is `low = 0, high = 7` -> `7 * (~(x^y^z))`! In EITHER convention, trying BOTH polarities AND offering `scale coeff (E.unary E.Not boolean)` whenever `boolean` is an XOR/AND/OR chain where `~boolean` is equivalent to `truth_inv` — checked against `target`! — guarantees `7 * ~(x ^ y ^ z)` is ALWAYS emitted!).
   - Add **1-variable Shannon factoring** to `boolean_candidates` for `count = 3`:
     - For each variable $a_i$, split `truth` into `f0` (where $a_i = 0$) and `f1` (where $a_i = 1$) (each a 2-var Boolean function!).
     - If `f1` is all-false: emit `~a_i & synth2(f0)` (produces `~v0 & (v1 ^ v2)`!).
     - If `f0` is all-false: emit `a_i & synth2(f1)`.
     - If `f1` is all-true: emit `a_i | synth2(f0)`.
     - If `f0` is all-true: emit `~a_i | synth2(f1)`.
     - If `f1 == not f0`: emit `a_i ^ synth2(f0)` (produces `x ^ (y ^ z)` and `~(x ^ (y ^ z))`!).
2. **Canonical Möbius Active-Var Elimination & Connected-Component Splitting inside `linear_candidates` (`1 <= count <= 8`):**
   - Compute exact modular Möbius coefficients `m.(subset)` on `target.(0 .. (1 lsl count) - 1)` in $O(\text{count} \cdot 2^{\text{count}})$:
     ```ocaml
     let m = Array.copy target in
     for bit = 0 to count - 1 do
       for subset = 0 to (1 lsl count) - 1 do
         if subset land (1 lsl bit) <> 0 then
           m.(subset) <- normalize (Z.sub m.(subset) m.(subset lxor (1 lsl bit)))
       done
     done
     ```
   - Find active variables (`bit` such that $\exists S$ with `S land (1 lsl bit) <> 0` and `m.(S) <> 0`).
   - Run union-find over active variables: union `i` and `j` whenever there exists `S` with `m.(S) <> 0` containing both `i` and `j`.
   - Whenever `List.length active < count` OR `List.length components >= 2`:
     - Project each component $C_r$ (if $|C_r| \le 4$) onto its exact sub-truth-table `sub_target` (evaluating `target` with all vars outside $C_r$ set to `0`, and for $r > 0$ subtracting `m.(0)` so the constant offset `m.(0)` is included once!).
     - Synthesize each component recursively using the exact same `linear_candidates` truth-table synthesizer (with dual-polarity + Shannon factoring + grouped/additive-split)!
     - Sum the component results and `offer` the sum — certified by **ONE `linear_mba_mod2w` edge** (ZERO SMT)!
3. **Constant left-shift `E << k` $\to$ `(1 << k) * E` inside linear-MBA contexts (`src/greysynth/normalization.ml`):**
   - When `E << k` (with constant `1 <= k < w`) appears inside an additive/linear-MBA expression (e.g. `neureduce/line_0000417`, `tigress_l7/target_1285`), normalize `E << k` to `(1 << k) * E` in a working linear-MBA view (bridging each unique `E << k == (1 << k) * E` via a single `< 1 ms` abstract SMT equality `a << k == (1 << k) * a`!) before running `linear_candidates` / `semilinear_mba`!

---

## 3. Fix `partial_linear_sum_candidate` Short-Circuiting (`src/greysynth/normalization.ml`)

**Deliverables:**
- In `partial_linear_sum_candidate`:
  - **Do NOT skip `linear_candidates` when `ring_polynomial_candidate` improves `linear_sum`!**
  - Compute BOTH `ring_opt = ring_polynomial_candidate cost linear_sum` AND `linear_opt = best of linear_candidates ~max_atoms:6 cost linear_sum` (and if `ring_opt = Some r`, also try `linear_candidates ~max_atoms:6 cost r`!), and pick whichever has the **strictly smallest `cost`** (recording the corresponding `ring_equalities` or `linear_mba_equalities` cleanly!).
  - Also expand nested small `(c + y) * x` or `k * (a + b)` factors when extracting `additive` terms so `pldi_poly/line_0000904`, `795`, `724`, `954`, `918`, `926` and `mba_flatten/line_0002901`, `2792` all recover their full linear-MBA sum and collapse to exact GT!

---

## 4. Complementary `uext(w-k, restrict(0, k-1, ~X))` Substitution & Cost-Free Mask Lifting (`src/greysynth/normalization.ml`)

**Deliverables:**
1. **Complementary low-slice identity (fixes ALL 5 remaining `c_mba_obfuscator` slice survivors `4575`, `3551`, `4796`, `4543`, `4551` AND `Tigress` `uext(63)`!):**
   - Add a constructive pass `complementary_slice_candidate` (run in `Normalization.local_candidates`, `dag_bottom_up_simplify`, and root preprocessing right alongside `complementary_atoms`!):
     - Scan the expression (for `dag_size <= 2048`) for any `v = uext(w - k, restrict(0, k - 1, ~X))` (where `1 <= k < w`) OR nested `v = uext(w - k, restrict(0, k - 1, ~ (uext(w - k, restrict(0, k - 1, X)))))`:
       - Let `u = uext(w - k, restrict(0, k - 1, X))` and `m = (1 << k) - 1`.
       - Replace `v` by `m - u` (recording ONE tiny `< 1 ms` abstract SMT equality `uext(w-k, restrict(0, k-1, ~a)) == m - uext(w-k, restrict(0, k-1, a))` — or the nested variant!).
       - Also when `k = 1`, simplify `u * u -> u` (idempotent 1-bit slice, certified by ONE `< 1 ms` abstract SMT equality `uext(w-1, restrict(0,0,a)) * uext(w-1, restrict(0,0,a)) == uext(w-1, restrict(0,0,a))`!).
       - Run `ring_polynomial_candidate` (and `linear_candidates` if applicable) on the substituted expression!
       - Accept the rewritten parent whenever `cost simplified < cost original` (certified compositionally via the tiny abstract SMT edge + `ring_mod2w` / `linear_mba_mod2w`!).
2. **Fix `mask_lift_candidate` Legacy-cost deadlock:**
   - Do NOT require `cost (E & mask) < cost (uext(w-k, restrict(0, k-1, E)))` in isolation! Instead, lift `uext(w-k, restrict(0, k-1, E)) -> E & ((1<<k)-1)` on a working view inside `semilinear_mba_candidate` / `Known_bits` / `dag_bottom_up_simplify` parent simplification, and gate ONLY on `cost parent_simplified < cost parent`!

---

## 5. Two's-Complement `~X` Peephole (`src/greysynth/normalization.ml`, `src/greysynth/egraph.ml`)

**Deliverables:**
- Add strictly-shrinking constructive peepholes in `peepholes`, `dag_bottom_up_simplify`, and `Egraph`:
  - `(-X) - 1` $\to$ `~X` (size 4 $\to$ 2)
  - `(-X) + (-1)` and `(-1) + (-X)` $\to$ `~X` (size 4 $\to$ 2)
  - `(-1) - X` $\to$ `~X` (size 3 $\to$ 2)
  - `-(X + 1)` and `-(1 + X)` $\to$ `~X` (size 4 $\to$ 2)
  - `((-X) - 1) + 1` / `(~X) + 1` $\to$ `-X` (already exists? ensure `~(-X) -> X - 1` in additive sums when it cancels `-1`!)
- Verify `qsynth_ea/line_0000388` collapses straight from `71 -> 9` (exact GT `((v4 & (v3*v3)) | (v3 ^ v4))`)!

---

## 6. Fast, Focused Verification Gate for Round 32 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round32_test.ml`):**
   - `pldi_poly/line_0000904` (`-> <= 12`, exact GT!), `pldi_poly/line_0000795` (`-> <= 13`, exact GT!)
   - `neureduce/line_0000098` (`-> <= 8`, exact GT!), `neureduce/line_0000632` (`-> <= 9`, exact GT!), `neureduce/line_0000798` (`-> <= 11`, exact GT!), `neureduce/line_0000417` (`-> <= 12`, exact GT!)
   - `c_mba_obfuscator/target_3551` (`-> <= 7`), `c_mba_obfuscator/target_4575` (`-> <= 10`)
   - `qsynth_ea/line_0000388` (`-> <= 9`, exact GT!)
   - `tigress_l8/target_5856` (`1,858,527 -> <= 9`, exact GT `7`!) & `omvll/target_771` (`3,070,823 -> <= 100`!)
   - Keep ALL Round 23–31 flagship tests green (`target_3218`, `target_366`, `target_1685`, `permutation64`, `pldi_nonpoly/895`, `msimba/191`, `tigress_l7/l8 target_1016`).
2. **Run `make test`** — 100% green.
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB, keep JSONLs under `/tmp/r32-*/out.jsonl`):**
   - **`datasets/hard_cases/all_failing/pldi_poly/`** (62 cases — target: leap from `12` exact GT toward `40–60+`!)
   - **`datasets/hard_cases/all_failing/neureduce/`** (53 cases — target: leap from `7` exact GT toward `35–50+`!)
   - **`datasets/hard_cases/all_failing/qsynth_ea/`** (60 cases — target: beat `25` exact GT / `1.53x`!)
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases — target: push exact GT past `250+` and slash geomean from `5.96x` toward `~2–3x`!)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted, geomean `<= 0.95x`!)
4. Record concise Round-32 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
