# GreySynth Round-17 Final Spec: Round-16 Audit Fixes, Milestone 8 Whole-Expression Extraction, and Final 72/72 Gate

**Baseline commit:** `f834ee4` (71/72 items complete; 5/5 100-case MBA suites at `0.7595x–0.9966409x`, QSynth EA improved to `0.8315x`, 8-case Xyntia B2 adaptive CHS cut wall time by 34% with identical reductions)  
**Goal:** Fix 4 subtle soundness/config issues found during the Round-16 audit, close the **last unchecked item** in `docs/PLAN.md` (Milestone 8 line 287 — whole-expression extraction for non-monotonic alternatives), run the final verification gates, and reach **72/72 (100% of `docs/PLAN.md`)**.

---

## 1. Round-16 Audit Fixes (Must Fix Before Final Gate)

### 1.1 Incremental SMT Model Variable Name Isolation (`src/utils/utils.ml:547-549`)
In `create_solver_session`, counterexample model formatting currently checks:
```ocaml
if List.exists (fun (other, width) -> other = name && width <> size) !variable_list
then Printf.sprintf "%s<%d>" name size else name
```
Because `!variable_list` accumulates variables across **all previous queries** in the reused session, if Query 1 mentions `x<32>` and Query 2 returns `Sat` on `x<64>`, Query 2 mislabels the model entry as `"x<64>"` instead of `"x"` — breaking CEGIS model lookup (`List.assoc_opt var.name model`).
- **Fix:** Check `!active_variables` instead of `!variable_list` (and remove the unused `variable_list` ref).
- **Test (`test/proof_test.ml`):** Query a width-32 expression containing `x`, then query a non-equivalent width-64 expression containing `x` with `~show_counter_example:true`, and verify the returned model binds `"x"` (not `"x<64>"`).

### 1.2 Restore `Unix.alarm` Wall-Clock Backstop in `are_equivalent_seconds` (`src/utils/utils.ml:445-591`)
`f834ee4` moved the old implementation to dead `are_equivalent_seconds_fresh` and omitted the `Unix.alarm wall_timeout` / `Sys.sigalrm` -> `Equivalence_timeout` backstop in the new `are_equivalent_seconds` (leaving `| Equivalence_timeout -> ...` unreachable).
- **Fix:** Restore the exact `wall_timeout` / `Unix.alarm` / `Sys.sigalrm` backstop around `session.query` (preserving any shorter caller alarm and restoring on exit via `Fun.protect`), and remove dead `are_equivalent_seconds_fresh`.

### 1.3 Honest `synthesizer_portfolio` Config & Attempt Accounting (`src/greysynth/synthesis.ml:270-289`)
1. Currently `synthesis.ml:270` gates portfolio execution on `!c_chs_adaptive_schedule`, so setting `"synthesizer_portfolio": "xyntia,cvc5"` with `"chs_adaptive_schedule": false` silently does nothing (violating Milestone 2's honest-configuration contract).
   - **Fix:** Run the portfolio loop whenever `!c_synthesizer_portfolio_backends <> []`, independent of `!c_chs_adaptive_schedule`.
2. When all portfolio backends fail, `attempt` logs `record (name ^ ":" ^ status_of_outcome outcome) elapsed false` for each backend AND line 288 logs a duplicate `record (status_of_outcome outcome) time false`.
   - **Fix:** Avoid the duplicate summary failure `record` when portfolio mode already logged every backend's individual attempt.

### 1.4 Canonicalize Reloaded Learned Rules (`src/greysynth/synthesis.ml:209-219`)
In `load_learned_rules`, after parsing `lhs` and `rhs` and independently verifying the certificate via `Rewrite_proof.verify`, check `E.sizeof lhs = E.sizeof rhs` and canonicalize the pair via `canonical_rule_pair lhs (Some rhs)` before inserting into `universal_rules`, so externally serialized or differently alpha-named rule libraries always hit the canonical lookup cache.

---

## 2. Milestone 8 (Line 287) — Whole-Expression Extraction for Non-Monotonic Alternatives

> `- [ ] Use whole-expression extraction for alternatives rather than requiring every useful intermediate form to be locally cheaper.`

### 2.1 Multi-Pass Non-Monotonic Intermediate Alternatives (`src/greysynth/normalization.ml`, `src/greysynth/egraph.ml`)
1. In `Normalization.local_candidates`:
   - Keep `allow_equal_cost = true` (non-monotonic intermediate alternatives) for AC canonical forms, AND add bounded, cheap-to-verify non-monotonic intermediate forms useful for whole-expression extraction across cost models:
     - **Power-of-two mul <-> shift / add bridge** (small expressions):
       - `x * 2^k` (for `1 <= k < width`) -> `x << k` (and `x * 2` -> `x + x`), `allow_equal_cost:true` (enables `Instruction` cost model to pick `x << k` cost 3 over `x * 2^k` cost 4, and enables shift/mul cancellation with outer terms!).
       - `x << k` (for constant `1 <= k < width`) -> `x * 2^k`, `allow_equal_cost:true` (enables ring-polynomial / factor-group cancellation with outer linear/mul terms!).
     - **Bounded small distributive / negation expansions** (certified via `ring_mod2w`, only when `cost expression <= 9` so e-graph size stays tightly bounded!):
       - `a * (b + c) -> (a * b) + (a * c)`, `(b + c) * a -> (b * a) + (c * a)`, `a * (b - c) -> (a * b) - (a * c)`, `(b - c) * a -> (b * a) - (c * a)`,
       - `-(a + b) -> (-a) - b`, `-(a - b) -> b - a`.
       - Notice each expansion is **strictly larger locally** (`cost(a*b + a*c) = 7 > cost(a*(b+c)) = 5`), so greedy local normalization rejects it — yet inside an e-graph, whole-expression extraction retains both forms and only selects the expansion when it enables outer cancellation or a cheaper global expression under the active `!Utils.cost_model`!
2. In `Egraph.optimize` (`src/greysynth/egraph.ml:586-618`):
   - Replace the single global `equal_found : bool` cap with a bounded per-eclass pass-family cap for non-monotonic candidates (e.g., `accepted_nonmono_passes` hashtbl capped at `<= 3` distinct non-monotonic passes per e-class), so an AC candidate does not starve a shift/mul bridge or small distributive expansion on the same e-class!
   - Keep the existing `graph.limit` (2048), `c_egraph_max_iters` (4), `local_deadline`, `compute_best` lexicographic `(cost, ast_nodes, expr)` cycle-free extraction, `emit_minimal_proofs`, and `Rewrite_proof.is_connected` safety checks untouched!

### 2.2 Whole-Pipeline E-Graph Cleanup (`src/greysynth/greysynth.ml`)
Currently `Egraph.optimize` runs only in `run_preprocessing` (`greysynth.ml:181`), while post-CHS cleanup (`greysynth.ml:114-115`) and final cleanup (`greysynth.ml:451-465`) still call strictly greedy `run_normalization` + `oes_quiet`.
- Extract a clean helper `run_cleanup expression`:
  - When `!c_egraph_extraction && not !g_has_timedout`, run `Egraph.optimize expression`; if `Egraph.fell_back ()`, fall back cleanly to `run_normalization` + `oes_quiet` (when enabled).
  - Otherwise run the existing `run_normalization` + `oes_quiet` passes.
- Use `run_cleanup` in both post-CHS horizon cleanup and final cleanup in `Greysynth.run`.

### 2.3 Focused Unit Tests (`test/pipeline_test.ml`, `test/proof_test.ml`)
Add focused, deterministic tests verifying:
1. **Non-monotonic expansion -> whole-expression cancellation**: An expression where expanding a subterm is strictly more expensive locally (e.g., `((a * (b + c)) ^ d) - ((a * b) ^ d)` or `(a * (b + c)) + (-(a * b) + x)` or `((x << 2) + y) - (4 * x)` where the shift/mul bridge or distributive expansion is locally non-cheaper) extracts the strictly cheaper whole expression via `Egraph.optimize` AND independently replays as `proved_compositional`.
2. **Cost-model-sensitive whole-expression extraction**:
   - Under `Instruction` cost model, `x * 4` (cost 4) extracts `x << 2` (cost 3) and replays as `proved_compositional`;
   - Under `PaperAst` and `Readability`, cast-heavy forms (`uext`/`sext`/`restrict`) are penalized honestly vs. `Legacy` and cannot claim fake reductions.
3. **Post-CHS e-graph cleanup**: With `egraph_extraction = true`, a mock CHS rewrite that unlocks a non-monotonic cancellation is simplified by post-CHS `run_cleanup` and replays cleanly.
4. **Portfolio without adaptive schedule + single attempt accounting**: Setting `synthesizer_portfolio` with `chs_adaptive_schedule = false` still runs the fallback backend and records exact non-duplicated attempt entries.

---

## 3. Final 72/72 Verification Gate

1. Run `devcontainer exec --workspace-folder . make test` — 100% green.
2. Re-run the **5×100 MBA quality gate** (`PLDI Non-Poly`, `MBA-Obfuscator nonlinear`, `PLDI Poly`, `QSynth EA`, `msimba`) with `egraph_extraction = true` — verify 500/500 independently replayed by `mba_proof`, matching or beating Round-16 (`0.9290x / 0.7595x / 0.8789x / 0.8315x / 0.9966409x`).
3. Re-run the **1,000-case C-Full / Tigress L5 gate** (`egraph_extraction = true`) — verify 1,000/1,000 established, 0 timeouts/unknowns/errors, `>= 984` strict reductions.
4. Run the **57-case CHS regression set** (or full bundled Xyntia B2/conditional CHS comparison) comparing baseline vs. `chs_adaptive_schedule = true` to confirm Milestone 7's acceptance criterion ("accepted reductions are no worse and backend time/attempt counts fall") with 100% independent replay.
5. Mark Milestone 8 line 287 `[x]` in `docs/PLAN.md` (reaching **72/72 = 100%**!), update `docs/IMPLEMENTATION_RESULTS.md` with the final verified summary table, commit atomically, and leave `docs/neon-review*.md` untouched.
