# GreySynth Round-42 Spec: Fix `opaque_probe_calls` Starvation & 64-Bit Abstract Proof Budget Split

**Baseline:** Round 41 (`5d6fcdf` / `00d9041` — `Tigress L8` slashed **`41.13x -> 16.59x`** (`584x` better than R37!), `regression_smoke` **`62/62`, `54` exact GT, `0` stalls, `0.7933x`** (best ever!), refreshed `core_hard` **`353/353` direct parallel, `3.05x`**, `0` refutations).

**Two Crystal-Clear Surgical Diagnoses from `/tmp/r41-l5/out.jsonl` & `/tmp/r41-core/out.jsonl`:**

1. **Why R41 lost `58` R40 exact `Tigress L5` cases (`target_6014`, `6027`, `6086`, `1349`, `798`, `800`, `802`, `2113`, `2127`, `5165`, `911`, `1417`) while gaining `30` new ones:**
   - In Round 41, `dag_bottom_up_simplify` capped `opaque_probe_calls` at `16` **including calls where `probe_opaque_atoms` returned `None`**!
   - In bottom-up traversal, the first 16 small nodes near the leaves (`cost 9..25`) exhausted all 16 slots returning `None` (costing `< 0.05 ms` each!), completely starving the real `cost 50..256` subtrees higher in the DAG (where R40 solved `target_6014`/`798`/`1349` to exact size `5` in `0.06–0.16s`!).
   - **Fix:** ONLY increment `opaque_probe_calls` when `probe_opaque_atoms` actually returns **`Some candidate`** (or when `accept_probe` actually runs SMT — `None` returns are pure OCaml and take microseconds!).
2. **Why ALL FIVE giant 64-bit `Tigress L8` 80–96-node residuals (`target_1169` `4.37M -> 80`, `target_3135` `2.48M -> 80`, `target_1281` `5.31M -> 96`, `target_1285` `5.31M -> 96`, `target_6503` `2.70M -> 96`) stopped right at `80–96` nodes instead of collapsing to exact GT `7–9`:**
   - Direct timing with `mba_equiv` on `tigress_lvl_8__target_1169` (`out = 80`, GT `7`):
     - The abstracted 64-bit 2-variable shift-carry identity `f(a, b) == a + b` is **TRUE** and Bitwuzla proves it UNSAT in **`0.2177 seconds` (`218 ms`)** (concrete takes `0.515s`)!
     - **Why it timed out in R41:** `src/proof/rewrite_proof.ml:329` allocates only `min 1. (timeout *. 0.25)` (**25%!**) to the abstract proof!
       - At `dag-semantic-probe` `~timeout:0.15`, abstract got **`37.5 ms`** (`6x` too short!).
       - At `run_cleanup` `~timeout:0.20`, abstract got **`50.0 ms`** (`4.3x` too short!).
       - At `run_root_semantic_probes` `~timeout:0.25`, abstract got **`62.5 ms`** (`3.5x` too short!).
     - Meanwhile, when an abstract query is FALSE (spurious abstraction), Bitwuzla returns SAT in **`< 5 ms`** (never wasting the budget!).
   - **Fix:**
     1. In `src/proof/rewrite_proof.ml` line 329 (ONLY this single scheduling constant — do NOT alter any proof rule or semantics!): change `min 1. (timeout *. 0.25)` to `min 1. (timeout *. 0.5)`.
     2. Give `probe_opaque_atoms` (whose candidates ALREADY passed 24 full-width independent samples + 132 `Rewrite.samples_agree` samples!) sufficient SMT budget to clear 64-bit 2-layer shift-carry identities (`0.22s`!):
        - `run_root_semantic_probes` (`greysynth.ml`): default `~timeout:0.80` (abstract gets `0.40s` > `0.218s`!),
        - `run_cleanup` (`greysynth.ml`): `~timeout:0.70` (abstract gets `0.35s` > `0.218s`!),
        - `dag_bottom_up_simplify` (`normalization.ml`): `accept_probe` uses `~timeout:0.60` (abstract gets `0.30s` > `0.218s`, strictly inside `try_smt` and charged to `smt_budget`, raising default `smt_budget` modestly from `1.2` to `1.5` so 2–3 real 64-bit opaque collapses fit cleanly!).
        - **Bonus check on `target_547` (the 1 net-neutral row in `r41-l5`):** Inspect why `target_547` returned `in == out` in R41 and make sure it reduces cleanly (e.g. if it was starved by `opaque_probe_calls` or `smt_budget`)!

---

## Verification Gate for Round 42 (Target Wall Time: ~6–8 min!)

1. **Unit & Regression Tests (`test/round42_test.ml`):**
   - End-to-end test on the actual 64-bit 80-node `target_1169` shift-carry shell (`(((((((A | B) * 2) | ~(B ^ A)) << 1) & (B ^ (A ^ ((A | B) * 2)))) << 1) - ((2 * ((((A | B) * 2) | ~(B ^ A)) ^ (A | B))) ^ ~(B ^ A))) + 1` with `A = (x1 - x2) * x3, B = x0`): verify `greysynth` collapses it to **`size <= 7` (exact GT)** in `< 1.0s` with independent `mba_proof` replay!
   - Test that `dag_bottom_up_simplify` does NOT burn `opaque_probe_calls` on `None` returns (e.g., an expression with `> 20` non-matching bitwise subtrees below a matching opaque shell still simplifies the outer shell!).
   - Run `make test` — warning-clean, 100% green.
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM safely under 30 GB, retain JSONLs under `/tmp/r42-*/out.jsonl`):**
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`450` cases — target: recover ALL 58 lost R40 exact cases + keep R41's 30 gains -> **`230+` exact GT** and geomean **`< 3.0x`**, `0` stalls!)
   - **`datasets/hard_cases/core_hard/`** (`353` cases — target: **`100+` exact GT**, slash `Tigress L8` from `16.59x` into **single digits**, and push overall `core_hard` geomean well below **`2.5x`**, `353/353` direct parallel!)
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases — must stay `62/62` established, `0` stalls, `0` refuted, **`<= 0.80x`**!)
3. Record concise Round-42 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
