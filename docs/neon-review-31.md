# GreySynth Round-31 Spec: Data-Driven Survivor Crushing — `uext(restrict(0,k-1))` Mask Lifting, Partial Linear-Sum Extraction, Canonical-Polynomial Disjoint Splitting & Giant-DAG Multi-Layer Peeling

**Baseline:** Round 30 (`f5b99d7` — restored `regression_smoke/` `2.37x -> 0.92x` and drove `core_hard/` down to `6.25x` with `208/405` exact GT!)  
**Forensic Diagnosis of the Top Remaining Survivors in `/tmp/r30-core/out.jsonl`:**
Inspecting the exact 197 unsolved rows in Round 30's `core_hard/` revealed **four concrete, general algebraic bottlenecks** responsible for almost all remaining large ratios:

1. **`uext(w-k, restrict(0, k-1, E))` hiding `& (2^k - 1)` in giant `Tigress L7–L8` & `C-MBA-Obfuscator`:**
   - Top 10 worst ratios in the entire corpus (`tigress_l8/1169` `4.38M`, `3354` `3.22M`, `2790` `2.46M`, `6503` `2.70M`, `3601` `2.67M`, `1635` `2.80M`, `tigress_l7/1955`, `6526`, `1285`, `1281`) all wrap their outer layers in `uext(63) (restrict(0, 0) E)` (`= E & 1`) and `uext(63) (restrict(0, 0) (~ (uext(63) (restrict(0, 0) E))))` (`= (~E) & 1`), and `c_mba_obfuscator/4575` & `4796` wrap in `uext(24) (restrict(0, 39) ...)` and `uext(48) (restrict(0, 15) ...)`. Because `uext`/`restrict` broke syntactic bitwise recognition, `linear_mba` / `semilinear_mba` / `PolySim` / `Known_bits` treated them as opaque walls!
2. **Factor-grouping stealing linear terms from `pldi_poly` (25/25 unsolved) & `mba_flatten` (19/19 unsolved):**
   - E.g. `pldi_poly/line_0000904` (GT `x*y + 7*~(x^(y^z))`, size 12) produced `(y - 7)*x + (-7 + ...)` (size 31) because factoring stole `-7*x` out of the 3-var linear MBA into `x*y`, destroying the compact 2-value signature of `7*~(x^(y^z))`!
3. **Canonical-polynomial disjoint splitting & low-size root linear MBA in `neureduce` (21 unsolved):**
   - `neureduce/line_0000098` (GT `-4*v2 - (v3|v4)`, size 8, output 66), `line_0000632` (GT `5*(v0|v1|v2) - 1`, size 9, output 69), `line_0000798` (GT `-(~v0&(v1^v2)) + (v3|v4)`, size 11, output 76) are pure 3–5 variable linear MBAs of size 72–79 where dummy variables (`v0, v1` in `line_0000098`) only vanish *after* canonical Möbius/multilinear reduction — syntactic additive union-find missed them because `v0, v1` still appeared in the input AST!
4. **Giant 3–6 variable DAGs (`tigress_l8/5856`, `5710` `1.86M`; `omvll/771`, `798` `3.07M`; `c_mba_obfuscator/1685` `29.5k`):**
   - `tigress_l8/5856` & `5710` are 4-variable DAGs of `((a&~b)*(b&~a)) + ((a&b)*(a|b)) -> a*b` layers that skipped the `<= 2`-var zero-seed OES pre-pass; `c_mba_obfuscator/1685` is masked by `3 & (...)` (2-bit narrowing!); `omvll/771` & `798` need up to 8–10 bottom-up DAG peeling iterations on tiny unique DAGs!

---

## 1. `uext(w - k, restrict(0, k - 1, E))` $\leftrightarrow$ `E & (2^k - 1)` Mask Normalization (`src/greysynth/normalization.ml`, `src/greysynth/egraph.ml`)

**Deliverables:**
1. Add fast bottom-up constructive rewrite rules in `Normalization.local_candidates` and `dag_bottom_up_simplify`:
   - `uext(w - k, restrict(0, k - 1, E))` (where `1 <= k < w` and `sizeof E = w`) $\to$ `E & ((1 << k) - 1)`!
   - Also handle the double-wrapped complement idiom directly:
     `uext(w - k, restrict(0, k - 1, ~ (uext(w - k, restrict(0, k - 1, E)))))` $\to$ `(~E) & ((1 << k) - 1)`!
   - **Important:** Only emit `E & (2^k - 1)` when it is **strictly cheaper** OR inside an enclosing bitwise/MBA/ring context (note: in `Legacy` cost model, `uext`/`restrict` have cost 0 while `E & mask` has cost `+2`, so a pure `size_of_expr` check would reject replacing `uext(63, restrict(0,0,E))` alone! Therefore:
     - In `dag_bottom_up_simplify` and `Normalization.local_candidates`, recognize `uext(w-k, restrict(0, k-1, E))` **transparently as `E & ((1 << k) - 1)`** inside `semilinear_mba_candidate`, `demand_bit_narrowing` (`E & ((1<<k)-1)`), `Known_bits`, AND add a **context-triggered rewrite** when `uext(w-k, restrict(0, k-1, E))` appears inside a larger expression where rewriting it enables a strict overall reduction — e.g., `(uext(63, restrict(0,0, ~ (uext(63, restrict(0,0, E))))) -> (~E) & 1` or inside `dag_bottom_up_simplify` normalize `uext(w-k, restrict(0, k-1, E))` into `E & ((1<<k)-1)` temporarily on a working view, simplify the parent, and accept the parent rewrite ONLY when the **overall parent** strictly shrinks in `size_of_expr`! Certify each `uext(w-k, restrict(0, k-1, E)) == E & ((1<<k)-1)` bridge edge via tiny local SMT on abstracted atom `E` (`< 1 ms`!)!).
2. **Apply backward demand-bit narrowing inside `dag_bottom_up_simplify` for low-bit masks `M = (1 << k) - 1` (`k <= 16`) on giant DAGs too (fixes `c_mba_obfuscator/target_1685` `29,511 -> 7`!):**
   - For `M & E` (or `E & M`) where `M = (1 << k) - 1` (`k <= 16`, e.g., `3 & E` for `k = 2`), reduce `E` directly at width `k` (all constants mod `2^k`, running `PolySim` / `linear_mba` / `poly_mod2w` at width `k`!), then lift back with `M & E'`!

---

## 2. GAMBA §5.3 Partial Linear-Sum Extraction BEFORE Factor Grouping (`src/greysynth/normalization.ml`)

Fixes the exact `pldi_poly` (25/25) & `mba_flatten` (19/19) regression where factor-grouping stole `-7*x` from `7*~(x^(y^z))` into `x*y`!

**Deliverables (`partial_linear_sum_candidate`):**
1. Given an additive sum $T_1 + T_2 + \dots + T_m$ ($m \ge 3$, `dag_size <= 1024`) containing BOTH:
   - **Nonlinear terms** $N = \{T_i : \text{contains variable}\times\text{variable multiplication}\}$ (e.g., `x * y`), AND
   - **Pure linear-MBA terms** $L = \{T_i : \text{linear\_mba\_compatible } T_i\}$ (including constants, scaled variables, and scaled bitwise terms!).
2. Partition the sum into `N_sum + L_sum` (certified by **ONE `ring_mod2w` edge** `original == N_sum + L_sum`!):
   - Simplify `L_sum` independently using our complete SiMBA/GAMBA `linear_candidates` (with up to 6 active atoms, certified by **ONE `linear_mba_mod2w` edge** `L_sum == L_simp`!).
   - Simplify `N_sum` independently using `ring_polynomial_candidate` / `shared_factor_group_candidate` (certified by `ring_mod2w`!).
   - Recombine `N_simp + L_simp`!
   - Also check the **expanded** form of `original` first when `original` already got partially factored into `(y - 7)*x + L_rem` (distribute small linear-times-var products like `(y + c) * x -> x*y + c*x` so `c*x` returns to `L_sum` where it cancels back into `7*~(x^(y^z))`!!).
3. Wire `partial_linear_sum_candidate` into `Normalization.local_candidates`, `Normalization.run`, and `Egraph.optimize` **BEFORE** `factor_group_candidate`, AND verify on `pldi_poly/line_0000904`, `941`, `795` that all three collapse directly to **exact GT (`12`, `12`, `13`)** with zero SMT edges!

---

## 3. Canonical-Polynomial Disjoint Splitting & Unrestricted Root Linear MBA (`src/greysynth/normalization.ml`, `greysynth.ml`)

Fixes ALL remaining `neureduce` 3–5 variable pure linear MBAs (`line_0000098 -> -4*v2 - (v3|v4)`, `line_0000632 -> 5*(v0|v1|v2) - 1`, `line_0000798 -> -(~v0&(v1^v2)) + (v3|v4)`):

**Deliverables:**
1. **Run canonical-polynomial disjoint-component splitting INSIDE `linear_candidates` (NOT just syntactic additive union-find!):**
   - Given ANY linear MBA over $1 \le t \le 12$ opaque atoms (even at small sizes like `size >= 15`!):
   - Compute its exact canonical sparse multilinear AND-conjunction polynomial $c_0 + \sum_{S \neq \emptyset} c_S \bigwedge_{i \in S} x_i \pmod{2^w}$ (using our Round 23 sparse multilinear evaluator — takes `< 0.5 ms` even for 10 variables!).
   - **Step A (Exact dummy-variable elimination):** Drop every variable $x_i$ that appears in **zero** non-zero monomials $S$! (In `neureduce/line_0000098`, `v0` and `v1` vanish immediately, collapsing a 5-var problem to 3 vars `{v2, v3, v4}`!)
   - **Step B (Canonical co-occurrence connected components):** Build union-find components over the surviving variables using ONLY the non-zero monomials $S$ (an edge connects $i, j \in S$ whenever $|S| \ge 2$ and $c_S \neq 0$)!
     - In `line_0000098`: `{v2}` (1 var!) and `{v3, v4}` (2 vars!) split cleanly into `-4*v2` and `-(v3 | v4)`!
     - In `line_0000798`: `{v0, v1, v2}` (3 vars!) and `{v3, v4}` (2 vars!) split cleanly into `-(~v0 & (v1 ^ v2))` and `(v3 | v4)`!
   - **Step C (3-var exact Boolean synthesis for `line_0000632`):** Ensure `boolean_candidates` for $k' \le 4$ always emits compact **single-clause OR** (`v0 | v1 | v2`), **single-cube AND** (`v0 & v1 & v2`), **single-XOR** (`v0 ^ v1 ^ v2`), **cofactor factored forms** (`~v0 & (v1 ^ v2)`, `v0 | (v1 ^ v2)`, `v0 ^ (v1 & v2)`), AND **negated single-term / constant-shifted forms** (`5*(v0 | v1 | v2) - 1`)!
   - **Step D (Lower root linear MBA threshold in `greysynth.ml`):** Run fast decidable root `linear_candidates` (with `linear_mba_mod2w` single-edge certification, zero SMT!) for ALL linear-MBA-compatible roots with `size_of_expr !best >= 15` (not just `>= 600`!), so `neureduce` size-70 expressions collapse to exact GT in `< 1 ms`!

---

## 4. Lift Giant-DAG Variable Cap on Zero-Seed OES & Multi-Layer Peeling (`src/greysynth/greysynth.ml`, `src/greysynth/normalization.ml`)

Fixes `tigress_l8/5856`, `5710` (`1.86M`, 4 vars), `omvll/771`, `798` (`3.07M`), and deep `Tigress L7–L8`:
- Lift the `<= 2`-variable restriction on the cheap zero-seed `Oes.linear_simplify ~seed:false` pre-pass for giant shared DAGs (`size_of_expr > 4096 && dag_size_bounded ~limit:2048 <= 2048`): instead of restricting to `<= 2` vars, run it whenever `dag_size <= 2048` and `size_of_expr > 4096` with a strict `0.25s` local deadline (never starving `target_366`, which has `dag_size = 627` and still finishes `3.4M -> 11` cleanly!).
- Allow `dag_bottom_up_simplify` up to **8 iterations** (instead of 4) on giant shared DAGs (`dag_size <= 2048`) as long as `dag_size` or `size_of_expr` shrinks strictly by `>= 5%` each pass and `<= 1.5s` has elapsed, including the explicit 2-atom nonlinear product identity `((a & ~b) * (b & ~a)) + ((a & b) * (a | b)) -> a * b` (and commuted forms!) via `BitTrans`+`ring_mod2w` on sub-DAGs of `dag_size <= 128`!

---

## 5. Fast, Focused Verification Gate for Round 31 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round31_test.ml`):**
   - `pldi_poly/line_0000904`, `941`, `795` collapse to exact GT (`<= 12`, `<= 12`, `<= 13`) with zero SMT edges!
   - `neureduce/line_0000098` (`-> <= 8`), `line_0000632` (`-> <= 9`), `line_0000798` (`-> <= 11`) collapse to exact GT with ONE `linear_mba_mod2w` edge!
   - `uext(63, restrict(0, 0, E))` mask-lifting test + `c_mba_obfuscator/target_1685` (`29,511 -> <= 7`) + `tigress_l8/target_5856` (`1.86M` dramatic collapse!).
   - Keep ALL Round 23–30 flagship tests green (`target_3218`, `target_366`, `permutation64`, `pldi_nonpoly/895`, `msimba/191`, `tigress_l7/l8 target_1016`).
2. **Run `make test`** — 100% green.
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/all_failing/pldi_poly/`** (62 cases — target: huge jump from `0` exact GT!)
   - **`datasets/hard_cases/all_failing/neureduce/`** (53 cases — target: big jump from `17` exact GT!)
   - **`datasets/hard_cases/all_failing/mba_flatten/`** (96 cases)
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases — target: push exact GT past `240+` and slash geomean from `6.25x` toward `~2–3x`!)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted, geomean `<= 0.95x`!)
4. Record concise Round-31 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
