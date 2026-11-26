# GreySynth Round-33 Spec: Exact Bitvector Offset Theorem & Full Canonical Möbius Splitting in `linear_candidates`, Abstract-Certified Giant-DAG Peeling & Strict SMT Timeout Clamping

**Baseline:** Round 32 (`2267ac0` — `PLDI Poly` `1.25x -> 1.18x` with `line_0000904: 93 -> 12` exact GT!, `MBA-Flatten` `1.20x -> 1.09x` (`13/25` exact), `ObfuscatorX` `6/7` exact (`0.984x`), `OMVLL` `90.95x -> 75.25x`, `Tigress L7` `2,926x -> 2,224x`, `Tigress L8` `21,724x -> 18,569x`, `core_hard` `5.96x -> 5.82x` with `229/405` exact GT, `regression_smoke` `0.9034x`).

**Forensic Diagnosis of `/tmp/r32-core/out.jsonl` (Why 4 Exact Bugs Held Back `Neureduce`, `QSynth EA`, `C-MBA 1685`, `Tigress L8 5856/1169` & `OMVLL 771`):**
Reading `src/greysynth/normalization.ml` alongside `/tmp/r32-core/out.jsonl` pinpointed **four exact, 100%-confirmed bugs**:

1. **The Bitvector 2-Value Offset Bug in `linear_candidates` (`neureduce/line_0000632`, `pldi_poly/line_0000941`, `mba_obf_nonlinear/line_0000972`):**
   - In `linear_candidates`, `Atom i` evaluates to `{0, +1}`, while `Not x` evaluates to `logxor mask x` = `{-1, -2}`!
   - Therefore, on $\{0, 1\}^k$:
     - Any **zero-preserving** Boolean expression $B_0$ ($B_0(0,\dots,0) = 0$) takes values `0` (false) and `+1` (true) $\implies$ exact MBA is **`v0 + (v1 - v0) * B_0`** (where `v0 = target.(0)`, `v1 = other_value`, `truth0 = (v == v1)` so `truth0.(0) = false`!).
     - Any **one-preserving** Boolean expression $B_1$ ($B_1(0,\dots,0) = 1$, e.g. `~v0 & ~v1 & ~v2`, `~(x ^ y ^ z)`, `x | ~y`) takes values **`-1` (true) and `-2` (false)** $\implies$ exact MBA is **`(2*v0 - v1) + (v0 - v1) * B_1`** (where `truth1 = (v == v0)` so `truth1.(0) = true`!) — and when `2*v0 == v1 (mod 2^w)` (e.g. `7 * ~(x^y^z)` or `7 * (x | ~y)`), `2*v0 - v1 == 0`, so the constant term **vanishes completely**!!
   - Because Round 32 sorted `distinct` with unsigned `Z.compare` (`low = 4, high = -1` on `neureduce/line_0000632`), `truth = (v == -1)` had `truth.(0) = true` (`~v0 & ~v1 & ~v2`), so `low + (high - low) * (~v0 & ~v1 & ~v2)` evaluated to `+9` instead of `-1` and **failed `samples_agree`**!
2. **Missing Canonical Möbius Active-Var Elimination, Connected-Component Splitting & 1-Var Shannon Factoring (`neureduce` 21/25 unsolved: `line_0000098`, `798`, `489`, `140`, `pldi_poly/941`, `mba_flatten/2938`):**
   - `neureduce/line_0000098` (`-4*v2 - (v3|v4)`), `line_0000798` (`-(~v0&(v1^v2)) + (v3|v4)`), `line_0000489` (`-2*(v0^~v1) + (v3&v4)`), and `line_0000140` (`-(~v0&(v1^v2)) - (v3&v4) - 1`) are ALL 5-variable pure linear MBAs where dummy variables disappear and independent variable components split ONLY after the canonical Möbius transform $m[S] \pmod{2^w}$ on `target.(0 .. 2^count - 1)`!
   - And `pldi_poly/line_0000941` (`x*y + 3*(~x&(y^z))`), `mba_flatten/line_0002938`, and `neureduce/line_0000798` all need 1-variable Shannon factoring (`~a & f0`, `a & f1`, `a | f0`, `~a | f1`, `a ^ f0`) in `boolean_candidates` for `count = 3` so `~x & (y ^ z)` (size 6) beats the 11-node ANF `(y^z) ^ ((y&x) ^ (x&z))`!
3. **Raw Full-Tree SMT Hanging on Giant Nodes in `dag_bottom_up_simplify` (Caused `c_mba_obfuscator/target_1685` `5 -> 29,511` regression AND starved `tigress_l8/5856`, `1169`, `omvll/771`!):**
   - In Round 32, `known_bits_candidate` was moved ABOVE `if not minimal` in `dag_bottom_up_simplify` and calls raw `Rewrite.accepts` (full-tree Bitwuzla SMT!) on giant nodes (`target_1685`: `29,511` nodes, `t = 7.00s`, `inconclusive: 2`; `tigress_l8/1169`: `4.38M` nodes, `t = 10.86s`, `candidates: 1`; `tigress_l8/5856`: `1.86M` nodes, `proved: 4, inconclusive: 1`, aborted on timeout!).
   - Meanwhile `peepholes` (`-X - 1 -> ~X`) wasn't even called inside `dag_bottom_up_simplify`, AND `qsynth_ea/line_0000388` (`size=71`) hung for **18.46 seconds** on a single unclamped Bitwuzla SMT call!

---

## 1. Exact 2-Value Offset Theorem, 1-Var Shannon Factoring & Full Canonical Möbius Splitting in `linear_candidates` (`src/greysynth/normalization.ml`)

**Deliverables:**
1. **Fix `boolean_candidates` for `1 <= count <= 4` (with 1-var Shannon factoring for `count = 3`):**
   - Keep DNF (`minterms`), CNF (`clauses`), and ANF (`anf`).
   - For `count = 3`, ALSO generate 1-variable Shannon-factored forms for each variable $i \in \{0, 1, 2\}$:
     - Split `truth` into 2-variable cofactors `f0` ($x_i = 0$) and `f1` ($x_i = 1$), synthesize minimal 2-var expressions for `f0` and `f1` (single var, negated var, `&`, `|`, `^`, `~(...)`, `~a & b`, `a & ~b`, etc.), and emit:
       - If `f1` is all-false: `~a_i & s0` (emits `~x & (y ^ z)` and `~v0 & (v1 ^ v2)`!)
       - If `f0` is all-false: `a_i & s1`
       - If `f1` is all-true: `a_i | s0`
       - If `f0` is all-true: `~a_i | s1`
       - If `f1 = not f0`: `a_i ^ s0` (emits `x ^ (y ^ z)` and `~(x ^ (y ^ z))`!)
   - Also simplify trivial `~(~E) -> E` and `(0xfff... ^ E) -> ~E` inside `boolean_candidates`!
2. **Fix 2-value synthesis using the Exact Bitvector Offset Theorem (NO unsigned `low/high` bug!):**
   - Whenever `distinct` has exactly 2 values (`v0 = target.(0)` and `v1` = the unique other value in `distinct`, for ANY `active_count <= 4` — drop `cost expression <= 128` cap too so giant linear MBAs also benefit!):
     - **Zero-preserving polarity (`truth0.(i) = Z.equal reduced.(i) v1`, so `truth0.(0) = false`):**
       - `delta0 = normalize (Z.sub v1 v0)`
       - For every `b0` in `boolean_candidates truth0`:
         - Offer `if Z.equal v0 Z.zero then scale delta0 b0 else E.binary E.Plus (constant width v0) (scale delta0 b0)`!
         - *(Verify: `neureduce/line_0000632`: `v0 = -1, v1 = 4, delta0 = 5, b0 = v0 | v1 | v2` $\implies$ **`-1 + 5 * (v0 | v1 | v2)`** — exact on all 64 bits, size 9!)*
     - **One-preserving polarity (`truth1.(i) = Z.equal reduced.(i) v0`, so `truth1.(0) = true`):**
       - `delta1 = normalize (Z.sub v0 v1)`
       - `offset1 = normalize (Z.sub (Z.add v0 v0) v1)` (*exact `2*v0 - v1` mod $2^w$!*)
       - For every `b1` in `(boolean_candidates truth1 @ List.map (fun b0 -> E.unary E.Not b0) (boolean_candidates truth0))` (with `~(~e) -> e` simplified):
         - Offer `if Z.equal offset1 Z.zero then scale delta1 b1 else E.binary E.Plus (constant width offset1) (scale delta1 b1)`!
         - *(Verify: `pldi_poly/line_0000904`: `v0 = -7, v1 = -14, delta1 = +7, offset1 = 0, b1 = ~(x^(y^z))` $\implies$ **`7 * ~(x ^ (y ^ z))`**!)*
         - *(Verify: `mba_obf_nonlinear/line_0000972`: `7 * (x | ~y)` has `v0 = -7, v1 = -14` $\implies$ **`7 * (x | ~y)`** — size 6!)*
         - *(Verify: `neureduce/line_0000489` component `{v0, v1}`: `-2 * ~(v0 ^ v1)` has `v0 = +2, v1 = +4, delta1 = -2, offset1 = 0` $\implies$ **`-2 * ~(v0 ^ v1)`**!)*
3. **Full Canonical Möbius Active-Var Elimination & Connected-Component Splitting inside `linear_candidates` (`1 <= count <= 8`):**
   - Factor the core truth-table synthesizer (`synthesize_table atoms target`) into a clean reusable inner helper that handles:
     - Constant (`List.length distinct = 1`)
     - 2-value exact synthesis (both zero-preserving and one-preserving polarities above!)
     - Grouped-by-value & 4-value additive split (`count <= 4`)
     - Compact Möbius sum (existing conjunction fallback)
   - In `linear_candidates` (for any `1 <= count <= 8`):
     - Compute the exact modular Möbius array `m.(0 .. (1 lsl count) - 1)` in $O(\text{count} \cdot 2^{\text{count}})$ (`< 0.1 ms`!):
       ```ocaml
       let m = Array.copy target in
       for bit = 0 to count - 1 do
         for subset = 0 to Array.length m - 1 do
           if subset land (1 lsl bit) <> 0 then
             m.(subset) <- normalize (Z.sub m.(subset) m.(subset lxor (1 lsl bit)))
         done
       done
       ```
     - Find `active` variables: all `bit` such that $\exists S \ni \text{bit}$ with `not (Z.equal m.(S) Z.zero)`.
     - If `active = []`: `offer (constant width m.(0))`!
     - Otherwise run union-find over `active`: union `i` and `j` whenever $\exists S$ with `not (Z.equal m.(S) Z.zero)` containing both `i` and `j`.
     - Partition `active` into connected components `comps = [C_0; ...; C_{r-1}]`.
     - Whenever `List.length active < count` OR `List.length comps >= 2`:
       - If every component has `|C_j| <= 4`:
         - For each component `C_j`, build its zero-offset sub-table `zero_table_j` (`target.(orig_assignment) - m.(0)` with all non-`C_j` vars set to `0`), AND its shifted sub-table `shifted_table_j` (`zero_table_j + m.(0)`).
         - Synthesize best expression `e_zero.(j)` for `zero_table_j` and `e_shifted.(j)` for `shifted_table_j`.
         - If `Z.equal m.(0) Z.zero`: offer `sum_j e_zero.(j)`.
         - Else: try attaching `m.(0)` to **each** component `k` (`e_shifted.(k) + sum_{j <> k} e_zero.(j)`) AND keeping `m.(0)` separate (`m.(0) + sum_j e_zero.(j)`), and `offer` all of them!
       - Every offered candidate is certified by **ONE `linear_mba_mod2w` edge** (ZERO SMT)!
       - *(Verify on `neureduce/line_0000098` -> `-4*v2 - (v3|v4)` size 8; `line_0000632` -> `5*(v0|v1|v2)-1` size 9; `line_0000798` -> `-(~v0&(v1^v2))+(v3|v4)` size 11; `line_0000489` -> `-2*(v0^~v1)+(v3&v4)` size 11; `line_0000140` -> `-(~v0&(v1^v2))-(v3&v4)-1` size 13!)*

---

## 2. Eliminate Raw Full-Tree SMT on Giant Nodes in `dag_bottom_up_simplify` + Abstract-Certified Peeling (`src/greysynth/normalization.ml`, `src/greysynth/rewrite.ml`, `src/utils/utils.ml`)

**Deliverables:**
1. **NEVER call raw full-tree SMT (`Rewrite.accepts` with empty compositional proof) on large nodes inside `dag_bottom_up_simplify`:**
   - Move `known_bits_candidate` BACK inside `if not minimal && cost !result <= 256` (this immediately fixes the Round-32 `c_mba_obfuscator/target_1685` `5 -> 29,511` regression AND stops the 10s Bitwuzla hang on `tigress_l8/target_1169`!).
   - Keep `demand_bits_candidate` enabled for low-mask `M & E` (`M = (1 << k) - 1, k <= 16`) even when `minimal = true` ONLY when certified via `ring_mod2w`/`linear_mba_mod2w` or small `cost <= 256` — AND make sure `c_mba_obfuscator/target_1685` (`3 & (...)`, 29,511 nodes) hits the exact Round-31 path that reduced it to `5`!
   - Guard `complementary_slice_candidate` in `dag_bottom_up_simplify` to `dag_size_bounded ~limit:512 !result <= 512`, and certify each `uext(w-k, restrict(0,k-1, ~base)) == mask - uext(w-k, restrict(0,k-1, base))` via a **1-variable abstract equality** (on a fresh var `a` of width `w`, NOT substituting the giant `base` into Bitwuzla!) so it takes `< 1 ms` even when `base` has 1,000,000 tree nodes!
   - Guard `mask_lift_candidate` the same way (ONLY via 1-variable abstract equality, never raw giant-tree SMT!).
2. **Add fast, abstract-certified constructive rules to `dag_bottom_up_simplify` (even when `minimal = true` on giant DAGs!):**
   - **Two's-complement & peepholes (`peepholes`):** Run `peepholes` inside `dag_bottom_up_simplify`! For the universal two's-complement peepholes (`(-X) - 1 -> ~X`, `(-X) + (-1) -> ~X`, `(-1) - X -> ~X`, `-(X + 1) -> ~X`, `~(~X) -> X`), certify via **1-variable abstract equality** (`(-a) - 1 == ~a` -> `< 0.5 ms`!) or `linear_mba_mod2w`! (Instantly turns `qsynth_ea/line_0000388` from `43` to `9`!)
   - **2-atom nonlinear product peeling (`((a & ~b)*(b & ~a)) + ((a & b)*(a | b)) -> a * b` and commuted variants):**
     - Detect this exact syntactic pattern directly on any `E.Binary { f = Plus; x = E.Binary { f = Mul; ... }; y = E.Binary { f = Mul; ... } }` (even when `a` and `b` have 500,000 tree nodes!), and certify via **ONE `nonlinear_poly_candidate` / 2-variable abstract proof** (`((p & ~q)*(q & ~p)) + ((p & q)*(p | q)) == p * q` on fresh vars `p, q` — `< 1 ms`!!)!
     - *(Verify: `tigress_l8/target_5856` (`1,858,527`) peels all 3 layers straight to `x0 - (x1 * x2 * x3)` — size `7` = EXACT GT in `< 0.2s`!)*
   - **2-atom shift-add/sub peeling (`((a & ~b) << 1) - (a ^ b) -> a - b`, `((a & b) << 1) + (a ^ b) -> a + b`, `((a | b) << 1) - (a ^ b) -> a + b`, `((d & ~1) << 1) - (d ^ 1) -> d - 1`):**
     - Detect directly at the node level and certify via **1–2 variable abstract proof** (`< 1 ms` regardless of child tree size!) so `tigress_l8/1169` & `tigress_l7/1285` peel instantaneously!
   - **Fast `ring_polynomial_candidate` on giant-DAG additive chains (`omvll/target_771` & `798`!):**
     - On `E.Binary { f = (Plus | Minus); ... }` inside `dag_bottom_up_simplify` (even when `minimal = true`!), run `ring_polynomial_candidate` on sub-DAGs of `dag_size_bounded ~limit:64 !result <= 64` (certified by `ring_mod2w`, ZERO SMT!), which collapses `(((U - (U|V)) + V) + (U|V)) -> U + V` across all 6 layers of `omvll/target_771` & `798` in `< 0.2s`!
3. **Clamp SMT timeout to remaining global budget (`src/greysynth/rewrite.ml` / `src/utils/utils.ml`):**
   - Whenever `!g_total_timeout > 0.`, compute `remaining = !g_total_timeout -. (Unix.gettimeofday () -. !g_start_time)`.
   - If `remaining <= 0.1`, set `g_has_timedout := true` and return `Unknown` immediately without spawning Bitwuzla!
   - Otherwise pass `min requested_timeout (max 1 (int_of_float (ceil remaining)))` to `are_equivalent` so a 5-second global timeout can NEVER hang for 18.5 seconds on `qsynth_ea/line_0000388` or `tigress_l8/target_1169`!

---

## 3. Fast, Focused Verification Gate for Round 33 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round33_test.ml`):**
   - **Real corpus rows directly loaded & verified end-to-end with `mba_proof` replay:**
     - `neureduce/line_0000098` (`-> <= 8`), `line_0000632` (`-> <= 9`), `line_0000798` (`-> <= 11`), `line_0000489` (`-> <= 11`), `line_0000140` (`-> <= 13`) — ALL with ONE `linear_mba_mod2w` edge and ZERO SMT!
     - `pldi_poly/line_0000904` (`-> <= 12`), `pldi_poly/line_0000941` (`-> <= 12`)
     - `mba_obf_nonlinear/line_0000972` (`-> <= 6`)
     - `qsynth_ea/line_0000388` (`-> <= 9`, wall `< 2s`!)
     - `c_mba_obfuscator/target_1685` (`29,511 -> <= 7`, restored!)
     - `tigress_l8/target_5856` (`1,858,527 -> <= 9`, exact GT `7`!)
     - `omvll/target_771` (`3,070,823 -> <= 100`!)
   - Keep ALL Round 23–32 flagship tests green (`target_3218`, `target_366`, `permutation64`, `pldi_nonpoly/895`, `msimba/191`, `tigress_l7/l8 target_1016`).
2. **Run `make test`** — 100% green.
3. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB, retain JSONLs under `/tmp/r33-*/out.jsonl`):**
   - **`datasets/hard_cases/all_failing/neureduce/`** (53 cases — target: massive leap from `7` exact GT toward `35–50+`!)
   - **`datasets/hard_cases/all_failing/pldi_poly/`** (62 cases — target: leap from `17` exact GT toward `30–50+`!)
   - **`datasets/hard_cases/all_failing/qsynth_ea/`** (60 cases)
   - **`datasets/hard_cases/core_hard/`** (non-GB 406 cases — target: push exact GT past **`260+`** and slash geomean from `5.82x` toward **`~2–3x`**!)
   - **`datasets/hard_cases/regression_smoke/`** (62 cases — must stay `62/62` established, `0` refuted, geomean `<= 0.95x`!)
4. Record concise Round-33 results in `docs/IMPLEMENTATION_RESULTS.md` and commit atomically (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
