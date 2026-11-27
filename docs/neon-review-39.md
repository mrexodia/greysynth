# GreySynth Round-39 Spec: Full DAG Memoization (Giant `Tigress L8` 100-Node DAGs) + Two-Phase Zero-SMT-First `dag_bottom_up_simplify` with Soft-Timeout Preservation

**Baseline:** Round 38 (`120d33f` / `663c513` — `Tigress L5 all_non_exact` `25.41x -> 6.90x` with **`+134` new exact GT**, refreshed `core_hard` `24.31x -> 6.52x` with **`+63` new exact GT**, `regression_smoke` `62/62`, `54` exact GT, `0.8232x`, `0` refutations).

**Forensic Diagnosis of `/tmp/r38-core/out.jsonl` & `/tmp/r38-l5/out.jsonl` (Why 25 `Tigress L5–L8` Rows in `core_hard` & All Top-16 Worst Rows in `r38-l5` Still Returned `out == in`!):**
Inspecting the proof certificates and timing profiles of ALL `25` `Tigress L5–L8` `in == out` rows in `r38-core` and ALL `16` `in == out` rows in `r38-l5` uncovered **two pure engineering/algorithmic bottlenecks** (100% general, zero benchmark specificity!):

1. **Exponential Unmemoized Tree Walks on Tiny-DAG / Million-Node-AST Expressions (ALL 12 giant `Tigress L8` `in == out` rows + the 3 `Tigress L8` timeouts!):**
   - Every single giant `tigress_lvl_8` `in == out` expression in `core_hard` (`target_1169` `4.37M`, `target_3354` `3.21M`, `target_6503` `2.70M`, `target_3601` `2.66M`, `target_2273` `2.64M`, `target_126` `2.48M`, `target_3135` `2.48M`, `target_2790` `2.46M`, `target_2403` `2.27M`, `target_5853`/`5710`/`5856` `1.85M`) actually has ONLY **`97` to `102` unique DAG nodes**!
   - Yet `simplifier_report.time` scales **linearly with expanded AST size** (`1.85M -> 5.7s`, `4.37M -> 14.0s`, `~3.2 µs / AST node`!) with `candidates = 1, proved = 0` and `wall_seconds = 38s–95s`!
   - **Root cause:** ~45 unmemoized recursive traversals over `Sexpr.Expr.t` (`contains_load`, `has_nonlinear_product`, `constant_value`, `collect_bitwise`/`collect_ring`/`pure_bitwise`/`truth`/`parse`/`pure_ring` in `norm_poly.ml` & `norm_nonlinear.ml`, `narrow`/`additive` in `norm_semilinear.ml`, `linear`/`pure` in `norm_linear.ml`, `count` in `probe_opaque_atoms`, plus polymorphic `Hashtbl` keyed by `E.t` instead of `Sexpr.BvTbl` in `rewrite_proof.ml` and `rewrite.ml`!) visit all `4.37M` exponential paths of a `100`-node DAG!
   - **Bonus:** On `size_of_expr !best > 32_768`, running a pure zero-SMT `dag_bottom_up_simplify` pass **BEFORE** `run_root_minterm_poly` / `run_root_polysim_poly` peels a `100`-node `4.37M`-AST Tigress L8 DAG (`((a & ~b)*(b & ~a)) + ((a & b)*(a | b))` + linear MBAs) down to `~7–9` nodes in **`< 100 ms`**!
2. **Unbounded SMT Timeouts + Discarded Partial Work Inside `dag_bottom_up_simplify` (ALL 16 `in == out` rows in `r38-l5` + ALL 13 `tigress_l5..l7`/`l8__2818` `in == out` rows in `r38-core`!):**
   - Look at `tigress_lvl_5__target_456` (`25,979` AST, only `135` DAG nodes), `tigress_lvl_7__target_841` (`130,893` AST, `429` DAG nodes), `tigress_lvl_5__target_4493` (`5,843` AST, `126` DAG nodes), `tigress_lvl_8__target_2818` (`13,729` AST, `111` DAG nodes):
   - **Every single one** ALREADY proved **`11` to `40` subtree simplifications** inside `dag_bottom_up_simplify`, then burned `5.00s` on `10` to `32` `inconclusive` Bitwuzla calls (including `dag-semantic-probe` at `normalization.ml:121`, which still has **NO `~timeout`**!), raised an uncaught `Timeout_exception` mid-DAG, and **threw away all 11–40 proved simplifications**, returning `out == in`!
3. **One small post-CHS cleanup gap (`target_2618`, `1705 -> 17`, GT `3`, `to=False`):**
   - `((((~ A) & B) * ((~ B) & A)) + ((B | A) * (B & A)))` (`size = 17 <= 128`) bypassed `Egraph` and hit `Normalization.run`, which never called `nonlinear_product_identity_candidate`!

---

## 1. Full DAG Memoization Across Preprocessing, Normalization & Proof/Rewrite Tables (`src/greysynth/*.ml`, `src/proof/rewrite_proof.ml`)

1. **Memoize all recursive AST walks on `Sexpr.Expr.t` using `Nodes.t` (`Sexpr.BvTbl.t`):**
   - `src/greysynth/greysynth.ml`: `contains_load`, `has_nonlinear_product`
   - `src/greysynth/norm_common.ml`: `constant_value` (memoize with a local `Nodes.t` or fast early-out on `E.Var`, and keep it DAG-linear!)
   - `src/greysynth/norm_poly.ml`: `collect_bitwise`/`collect_ring`, `pure_bitwise`, `truth`, `parse`, `pure_ring`, `additive`
   - `src/greysynth/norm_nonlinear.ml`: `has_nonlinear_product`, `collect_bitwise`/`collect_ring`, `pure_bitwise`, `bitwise`/`inspect`, `additive`, `factors`, `nonlinear`, `has_nontrivial_mask`, `collect`
   - `src/greysynth/norm_semilinear.ml`: `narrow`, `additive`
   - `src/greysynth/norm_linear.ml`: `linear`, `pure`, `obvious_minterm`, `obvious_grouped_sum`
   - `src/greysynth/norm_probes.ml`: `collect_bitwise`, `pure_bitwise`, `truth`, and in `probe_opaque_atoms` make `count` DAG-memoized (count distinct parent-edge occurrences across unique DAG nodes, NEVER exponential tree-path recursion!)
   - `src/greysynth/norm_peepholes.ml`: `boolean_value`, `inspect`, `collect`, `flatten` (ensure DAG-memoized where they can be invoked on DAG nodes).
2. **Use `Sexpr.BvTbl` / tag-based keys instead of polymorphic `Hashtbl` on `Sexpr.Expr.t`:**
   - `src/greysynth/rewrite.ml`: key `proofs`, `proof_budgets`, and `compositional_budgets` with hash-consed `Sexpr.Expr.hash`/`is_equal` (or a dedicated `ExprPairTbl` / `ExprPairPassTbl` using `E.hash` and `E.is_equal`) so lookups NEVER invoke OCaml structural `Stdlib.(=)` on giant DAGs!
   - `src/proof/rewrite_proof.ml`: change `graph.expressions` from `(E.t, int) Hashtbl.t` to `int Sexpr.BvTbl.t` (pure hash-cons lookup swap — **do NOT alter any proof verification rule or semantics**!).

---

## 2. Two-Phase Zero-SMT-First `dag_bottom_up_simplify` + Cumulative SMT Cap + Soft-Timeout Partial-Result Preservation (`src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

1. **Add `?(zero_smt = false)`, `?(smt_budget = 1.2)`, and `?(deadline : float option)` to `dag_bottom_up_simplify`:**
   - **Soft-timeout preservation (NEVER throw away proved subtrees!):**
     - Track `soft_stopped = ref false`. Before running candidate passes on a node, check whether `deadline` has passed OR whether global remaining time is `<= 0.35s` (when `!g_total_timeout > 0.`). If so, set `soft_stopped := true` instead of raising `Timeout_exception`!
     - Also wrap the candidate block in `try ... with Timeout_exception -> soft_stopped := true` (re-checking `global_timeout_expired` only outside, NOT discarding `memo`!).
     - When `!soft_stopped`, `visit` skips all candidate checks and finishes rebuilding remaining ancestor nodes from already-memoized simplified children in `memo` in `< 1 ms`!
   - **Pure Zero-SMT Mode (`zero_smt = true`):**
     - Run ONLY zero-SMT decidable passes: `dag-product-peel`, `dag-linear-mba`, `dag-semilinear-mba`, `dag-ring-mod2w`, `dag-minterm-ring-poly`, `dag-poly-mod2w`, `dag-complementary-atoms`, `dag-correlated-null`, `dag-xor-affine-mask`, `dag-semantic-bitwise`, plus pure constant-expression folding if zero-SMT.
     - Zero Bitwuzla calls — peels `100`–`4,096` DAG nodes in tens of milliseconds!
   - **Bounded-SMT Mode (`zero_smt = false`):**
     - Fix `dag-semantic-probe` (`normalization.ml:121`): ALWAYS pass explicit `~timeout:0.15` to `Rewrite.accepts`!
     - Track `smt_spent = ref 0.0` across all SMT-backed calls inside `dag_bottom_up_simplify` (`dag-constant-cast`, `dag-restrict-factor`, `dag-bit0-parity`, `dag-abstract-slice`, `dag-mask-lift`, `dag-known-bits`, `dag-semantic-probe` SMT fallback, `dag-power2-pullout`, `dag-demand-bits`, `dag-peephole`). Measure elapsed wall time around each SMT-backed `Rewrite.accepts` call and add it to `smt_spent`.
     - Once `!smt_spent >= smt_budget`, skip all remaining SMT-backed checks for the rest of the pass while **continuing all zero-SMT decidable passes**!
2. **Phase-order in `run_preprocessing` (`src/greysynth/greysynth.ml`):**
   - **First (before heavy root polynomial passes when `size_of_expr !best > 1024 && dag_size_bounded ~limit:4096 !best <= 4096`):** run a fast fixpoint loop (up to 12 rounds, local deadline `1.5s`) of `dag_bottom_up_simplify ~zero_smt:true ~minimal:(size_of_expr !best > 32_768) ~deadline !best`!
     - This immediately collapses all `1.85M–4.37M` AST / `100`-node DAG `Tigress L8` expressions AND peels all zero-SMT product/linear/semilinear layers of `Tigress L5–L7` in `< 0.2s` BEFORE a single SMT call or giant root expansion ever runs!
   - Then run the existing root decidable passes and the bounded-SMT `dag_bottom_up_simplify ~zero_smt:false ~smt_budget:1.2 ~deadline !best` loop (when `dag_size <= 2048`), followed by `run_root_semantic_probes` (so `target_158`, `target_2968`, `target_3728` arrive with `> 3.5s` remaining!).

---

## 3. Wire Zero-SMT Product Peeling & Opaque Probes into Post-CHS / Small-Root Cleanup (`src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`)

1. **In `Normalization.run` (`src/greysynth/normalization.ml`):**
   - Wire `nonlinear_product_identity_candidate !current` (zero-SMT `Rewrite.accepts_compositional ~pass:"product-peel"`) into the `decomposed` chain right alongside `product_partition_candidate` so small roots (`size <= 128`) and post-CHS cleanup immediately collapse `target_2618` (`((((~ A) & B) * ((~ B) & A)) + ((B | A) * (B & A))) -> A * B`, exact GT `3`)!
2. **In `run_cleanup` (`src/greysynth/greysynth.ml`):**
   - When `not !g_has_timedout && size_of_expr !best >= 9 && size_of_expr !best <= 256`, try `Normalization.probe_opaque_atoms size_of_expr !best` (with decidable `linear_mba_mod2w` replay first, then `~timeout:0.20` SMT fallback) so post-CHS cleanup can also close residual 1–3 atom opaque shells!

---

## 4. Verification Gate for Round 39 (Target Wall Time: ~5–7 min!)

1. **Unit & Regression Tests (`test/round39_test.ml`):**
   - Giant-AST / small-DAG regression test (e.g., actual `tigress_lvl_8__target_5853` or synthetic `> 1,000,000`-AST / `~100`-DAG nested product+MBA expression): verify `greysynth` simplifies it in **`< 1.0s`** with independent `mba_proof` replay!
   - Soft-timeout partial-work preservation test for `dag_bottom_up_simplify`: verify already-simplified subtrees are retained when the soft deadline expires mid-DAG.
   - `target_2618`-style `Normalization.run` test: `((((~ A) & B) * ((~ B) & A)) + ((B | A) * (B & A))) -> A * B` (`A = sext(24) x1<8>, B = sext(24) x0<8>`, exact size 3, zero-SMT compositional proof).
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r39-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` cases — target: `0` `in == out` stalls, big jump in exact GT past **`160+`** and slash geomean from `6.90x` well below `4x`!)
   - **`datasets/hard_cases/core_hard/`** (`353` cases — target: **MASSIVE** drop in `tigress_l8` geomean from `7,861x` and overall `core_hard` geomean from `6.52x`, PLUS eliminate the 3 `tigress_l8` 8-worker timeouts so `core_hard` runs **`353/353` directly in parallel** with a fraction of the wall time!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — must stay `62/62` established, `0` refuted, `<= 0.90x`!)
3. Record concise Round-39 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
