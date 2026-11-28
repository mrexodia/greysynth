# GreySynth Round-58 Spec (Single-Focus): Seal ALL Timeout Partial-Work Discards (`run_preprocessing` + `dag_bottom_up_simplify`) & Replace `dag-bitwise-ac` `<= 128` Cutoff with `<= 256` + `<= 32`-Call Cap

**Baseline:** Round 57 (`lowk_restrict_pushdown` dead-branch annihilation — **NEW ALL-TIME `dev_64` RECORD `525/880` exact & `1.8791x`** with `mba-ladders-v1` `1.1032x -> 1.0164x`; `r57-l5` `13.51x -> 12.88x`; `regression_smoke` `56/58` exact, `62/62` strict, `0.8018x`; `0` refutations across all 1,444 cases).

**Why This Single-Focus Change Is Huge (Zero `rewrite_proof.ml` Edits!):**
- In R56/R57, `core_hard` still had **20+ `in == out` stalls**, `L5` still had `target_2266` (`162,571 -> 162,571`, was `107` in R54) and `target_1461` (`54,590 -> 54,590`, was `222` in R54), and `dev_64` had **~35 `in == out` stalls** across `mba-frontier64-v1` (`2dda45799bcf74a9_w64`, 810 proved steps discarded!) and `mba-stress64-v1` (`7a3c5b5205027e63_w64`, 253 proved steps discarded!) — ALL because:
  1. `run_preprocessing` (`src/greysynth/greysynth.ml`) has **NO `try ... with Timeout_exception -> g_has_timedout := true; !best` wrapper**, so any `Timeout_exception` firing after `root-polysim-poly-mod2w` or `dag_bottom_up_simplify` unwinds out of `run_preprocessing` and discards `!best`!
  2. `dag_bottom_up_simplify` (`src/greysynth/normalization.ml:153-171`) runs `visit x`, `visit y`, and `semantic_child` **OUTSIDE** `try ... with Timeout_exception` and never checks `should_stop ()` between per-node passes!
  3. R55's `(not zero_smt || cost !result <= 128)` cutoff on `dag-bitwise-ac` (`normalization.ml:409`) broke `target_5334` (`7 -> 102`), whereas restoring `cost !result <= 256` with a clean `<= 32` per-pass call cap gives `target_5334` all 30 of its `dag-bitwise-ac` steps while cutting `2dda4579` (541 calls) and `7a3c5b52` (207 calls) down to `<= 32`!

---

## Exact Edits (ONLY 2 Source Files: `src/greysynth/greysynth.ml` & `src/greysynth/normalization.ml`)

1. **In `src/greysynth/greysynth.ml` (`run_preprocessing`):**
   - Immediately after `let best = ref input in` (around line 290) — wrap the entire body of `run_preprocessing` in:
     ```ocaml
     try
       ...
       !best
     with Timeout_exception ->
       g_has_timedout := true;
       !best
     ```
   - Double-check that EVERY branch inside `run_preprocessing` mutates `best := ...` only on strictly proved reductions (already true!) so returning `!best` on `Timeout_exception` ALWAYS returns the best independently proved simplification reached so far (and its proof certificate is already recorded in `Rewrite.journal`!).

2. **In `src/greysynth/normalization.ml` (`dag_bottom_up_simplify`):**
   - Add `let bitwise_ac_calls = ref 0 in` alongside `let lowk_calls = ref 0` and `let opaque_probe_calls = ref 0`.
   - Wrap the child recursion AND `semantic_child` in `visit` (lines 153–171) so `Timeout_exception` can NEVER escape `dag_bottom_up_simplify`:
     ```ocaml
     let semantic_child child =
       if minimal || should_stop () then child
       else
         try
           match is_semantically_bitwise cost child with
           | Some candidate
             when Rewrite.accepts_compositional ~pass:"dag-semantic-bitwise"
                    ~equalities:[] ~linear_mba_equalities:[ child, candidate ]
                    child candidate -> candidate
           | _ -> child
         with Timeout_exception -> soft_stopped := true; child
     in
     let rebuilt =
       if should_stop () then node
       else
         try
           match node with
           | E.Unary { f = E.Not; x; _ } -> E.unary E.Not (semantic_child (visit x))
           | E.Unary { f; x; _ } -> E.unary f (visit x)
           | E.Binary { f = (E.And | E.Or | E.Xor as f); x; y; _ } ->
               E.binary f (semantic_child (visit x)) (semantic_child (visit y))
           | E.Binary { f; x; y; _ } -> E.binary f (visit x) (visit y)
           | E.Ite { c; t; e; _ } -> E.ite (visit c) (visit t) (visit e)
           | _ -> node
         with Timeout_exception -> soft_stopped := true; node
     in
     ```
   - Inside the `if not !soft_stopped then (try ... with Timeout_exception -> soft_stopped := true)` block, guard each heavy pass with `if not (should_stop ()) then ...` (`dag-linear-mba`, `dag-gf2-masked-xor`, `dag-semilinear-mba`, `dag-minterm-ring-poly`, `dag-semantic-probe`, `dag-poly-mod2w`, `dag-ring-not-mod2w`, `dag-bitwise-ac`, `dag-ring-mod2w`) so a single node NEVER overruns `deadline`!
   - On `dag-bitwise-ac` (`normalization.ml:407-418`): **REMOVE** `(not zero_smt || cost !result <= 128)` (restoring `cost !result <= 256`!) and add `!bitwise_ac_calls < 32` (calling `incr bitwise_ac_calls` whenever `recursive_bitwise_ac_candidate` returns `Some _`)!

---

## Verification Gate for Round 58

1. **Regression Tests (`test/round58_test.ml`, plus warning-clean `make test`):**
   - `tigress_lvl_5__target_2266` (`162,571 -> < 500`, independent `mba_proof` replay — NO `in == out` timeout discard!)
   - `tigress_lvl_5__target_5334` (`5,525 -> <= 15`, recovering the `dag-bitwise-ac` `<= 256` win!)
   - `7a3c5b5205027e63_w64` (`mba-stress64-v1`: `3,066 ->` strict reduction, NO `in == out` discard!)
   - `2dda45799bcf74a9_w64` (`mba-frontier64-v1`: `2,025 ->` strict reduction, NO `in == out` discard!)
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r58-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r58-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r58-leeky-dev64/out.jsonl` — expect major strict-reduction jump on `mba-frontier64-v1` & `mba-stress64-v1`, pushing `dev_64` to a new record `< 1.80x`!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`170` shrunk cases -> `/tmp/r58-l5/out.jsonl` — expect `170/170` strict & `< 11.2x`!)
   - **`datasets/hard_cases/core_hard/`** (`328` refreshed cases -> `/tmp/r58-core/out.jsonl` — expect `~320+/328` strict & `< 5.0x`!)
3. Record concise Round-58 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
