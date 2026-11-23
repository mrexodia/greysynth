# GreySynth Round-16 Spec: Closing Milestones 4, 5, and 7 (7 of 8 Remaining PLAN Items)

**Baseline commit:** `a80b9c0` (64/72 items complete; Milestones 1, 2, 3, 4A, 6, 9 all `[x]`, 5/5 100-case MBA datasets beating/matching baseline at `0.7595x–0.9966x`)  
**Goal:** Cleanly implement and verify the **7 remaining items** in Milestones 4, 5, and 7 (leaving only Milestone 8 whole-pipeline extraction + expanded corpus audits for Round 17 to reach **72/72**!).

All new configuration knobs MUST be added to `Config.config_specs` in `src/greysynth/config.ml` so parsing, defaults, validation, reset, and `report_json` stay centralized.

---

## 1. Milestone 4 (Line 180) — Proof-Complexity-Aware OES Representative Ranking (`src/greysynth/oes.ml`)

Currently `compare_candidate` (`oes.ml:151-154`) ranks OES frontier candidates solely by `(size, E.compare)`.

**Deliverables:**
1. Add a deterministic `proof_complexity : Sexpr.Expr.t -> int` heuristic in `src/greysynth/oes.ml` that penalizes SMT-hard operators:
   - Constants/vars: `0`,
   - Pure bitwise (`Not`, `And`, `Or`, `Xor`) & `Plus`/`Minus`: `+1`,
   - Shifts/rotates/casts/extract/concat: `+2`,
   - Conditionals (`Ite`) & comparisons: `+3`,
   - Nonlinear `Mul` (both operands non-constant): `+8` (constant-scaled `Mul`: `+3`),
   - Division/remainder (`Udiv`, `Sdiv`, `Umod`, `Smod`): `+10`.
2. Rank OES frontier entries in `add_to_cache` by `(size candidate, proof_complexity candidate, E.compare)` so among equal-cost (and frontier) candidates, the easiest-to-prove representative is tried first!
3. Add a focused test in `test/pipeline_test.ml` verifying that `oes_candidate_limit > 1` ranks an easy-to-prove representative ahead of a nonlinear/division-heavy equal-cost alternative (and falls back cleanly from an unprovable smallest representative to a proved runner-up).

---

## 2. Milestone 4 (Line 190) — Incremental SMT Solver Context Reuse (`src/utils/utils.ml`, `src/proof/rewrite_proof.ml`)

`Libsolver.S` (`outside_tools/binsec_no_simplification/src/smt/api/common.ml:196-219`) already provides `push`, `pop`, and `check_sat_assuming : ?timeout:float -> Bl.t -> status`, yet `Utils.are_equivalent_seconds` currently creates and destroys a fresh `Factory ()` Bitwuzla instance on every single query.

**Deliverables:**
1. Add a managed incremental solver session in `src/utils/utils.ml` (behind a clean ref/pool with `Utils.reset_solver_session ()`):
   - Keep one reusable `Libsolver.S` instance + variable cache per session, querying each `(expr1, expr2)` via `Solver.check_sat_assuming ?timeout (Solver.Bv.diff bv1 bv2)` (zero formulas ever asserted permanently on the solver stack!).
   - **Fail-safe isolation:** Close and discard the cached solver instance immediately on any `Timeout`, `Unknown`, `Equivalence_timeout`, or unexpected exception (and after e.g. `256` queries to bound solver memory growth), creating a fresh instance on the next call.
   - Keep `Rewrite_proof.verify` semantically independent: call `Utils.reset_solver_session ()` at entry/exit of `Rewrite_proof.verify` (and on `Greysynth.run` entry/exit) so independent replay never inherits producer solver state!
2. Add a focused test in `test/proof_test.ml` running a mixed sequence of `Yes`, `No` (with concrete counterexample model extraction!), `Timeout`, and subsequent `Yes` checks through the reused solver session, verifying exact verdicts and zero cross-query contamination.

---

## 3. Milestone 5 (Line 228) — Persisted, Versioned Generalized Learned-Rule Proofs (`src/greysynth/synthesis.ml`, `src/greysynth/config.ml`)

**Deliverables:**
1. Add optional config knob `learned_rules_file` (string, default `""` = disabled) to `Config.config_specs`.
2. Define a versioned JSON format for persisted universal rules:
   ```json
   {
     "format": "greysynth.learned-rules.v1",
     "semantics": "smtlib-fixed-bitvectors-srem-v1",
     "rules": [
       { "width": 64, "lhs": "...", "rhs": "...", "certificate": { ... } }
     ]
   }
   ```
3. **Save:** When `learned_rules_file <> ""` and a new universal rule `(key, result)` is proved in `Synthesis.synthesize`, build its standalone `Rewrite_proof` certificate (`Rewrite_proof.create key` -> `record` -> `finish result`) and atomically write/update `learned_rules_file` (write temp + rename).
4. **Load (untrusted until re-verified!):** At `Greysynth.run` startup (or `Synthesis.load_learned_rules path`), parse `learned_rules_file`, validate `"format"` and `"semantics"`, and **independently re-verify every rule's `"certificate"` with `Rewrite_proof.verify ~original:lhs ~candidate:rhs`**! Discard/log any tampered, malformed, or unverified rule; insert only freshly re-verified canonical rules into `universal_rules`. (Concrete applications still get re-proved and recorded in the run's output certificate as usual!)
5. Add a focused test in `test/pipeline_test.ml`:
   - Run 1 synthesizes `(A|B)+(A&B) -> A+B` and persists it to a temp `learned_rules_file`;
   - Reset in-memory rule cache;
   - Run 2 loads from `learned_rules_file`, re-verifies the certificate, and reuses the rule on distinct variables with **zero backend calls**;
   - A tampered rule in `learned_rules_file` (e.g. `rhs` edited to a non-equivalent expression) is rejected on load!

---

## 4. Milestone 7 (Lines 263, 264, 266, 268) — Adaptive CHS Scheduling (`src/greysynth/synthesis.ml`, `src/greysynth/synth_backends.ml`, `src/greysynth/config.ml`)

Add clean centralized config knobs in `Config.config_specs`:
- `chs_adaptive_schedule` (bool, default `false` — keeps existing deterministic behavior unchanged unless enabled, or safe to enable once verified on the CHS suite!),
- `chs_probe_timeout` (int, default `1`, `> 0`),
- `synthesizer_portfolio` (string, comma-separated backend names e.g. `""` = disabled, `"xyntia,cvc5"` = primary + escalation fallback, validated against supported backend names).

Implement all 4 Milestone 7 capabilities cleanly in `src/greysynth/synthesis.ml` & `src/greysynth/synth_backends.ml`:

1. **Lower-bound target skipping (Line 266):**
   - For any CHS target `node` truncated to `(n', new_leafs)`:
     - Check whether `node` can possibly be improved under the configured cost model:
       - If `size_of_expr node <= 1`: skip (`"skipped_lower_bound"`).
       - If `!evaluator.is_node_constant node = None` (non-constant on samples, so cannot simplify to a single constant) AND `size_of_expr node <= 2` AND no single cut-leaf/variable agrees with `node` on samples (cannot simplify to a single variable/leaf either!): the minimum possible replacement cost is `>= 2` (or `>= 3` for 2-variable non-unary targets), so skip immediately and record `status = "skipped_lower_bound"` in `log_chs_synthesis_attempts`!
2. **Work ranking (Line 264):**
   - In `simplify_with_horizon`, collect candidate target subtrees at `depth >= horizon` along with:
     - `potential_gain = size_of_expr node`,
     - `leaf_count = Hashtbl.length new_leafs` (lower is better!),
     - `class_freq` = how many times `node`'s semantic `outhash` occurs in the expression (higher is better — one rewrite simplifies multiple sites via `chs_cache_per_horizon`!),
     - `has_constants` / operator complexity,
     - `history_bonus` = whether a child or adjacent horizon (`horizon - 1`) succeeded on this semantic class / parent.
   - Rank targets deterministically by priority score when `chs_adaptive_schedule = true`, processing the highest-value targets first so global timeout budgets spend time where reduction payoff is highest!
3. **Short-probe + escalation (Line 263):**
   - When `chs_adaptive_schedule = true` and `synthesis_timeout > !c_chs_probe_timeout` (or `synthesis_repeat > 1`):
     - First run a fast probe with `(!c_chs_probe_timeout, 1)`.
     - If the probe fails (`No_result` / `Backend_timed_out`) AND the target is promising (top-ranked / high `potential_gain` / low `leaf_count <= 4` / repeated semantic class / adjacent-horizon hit) AND sufficient global budget remains, escalate to the full `(synthesis_timeout, synthesis_repeat)`!
4. **Adaptive backend portfolio (Line 268):**
   - When `synthesizer_portfolio <> ""` (e.g. `"xyntia,cvc5"`), parse the ordered backend list via `Synth_backends.select`.
   - On a target where the primary backend returns `No_result` or `Backend_timed_out` (and global budget remains), automatically invoke the next backend in the portfolio, recording each backend attempt separately in `log_chs_synthesis_attempts` and validating every returned candidate through the shared proof-gated acceptance boundary!
5. **Focused unit tests (`test/pipeline_test.ml`):**
   - Lower-bound skip emits `"skipped_lower_bound"` with zero backend calls,
   - Priority ranking orders high-gain / repeated-class / low-leaf targets ahead of low-gain high-leaf targets,
   - Short-probe -> escalation invokes mock backend twice (short probe then full budget) only for promising targets and succeeds on escalation,
   - Adaptive portfolio falls back from a failing primary mock backend to a succeeding secondary mock backend and proves the accepted rewrite.

---

## 5. Acceptance Targets for Round 16

1. Implement all 7 items above cleanly with focused unit tests in `test/proof_test.ml` and `test/pipeline_test.ml`.
2. Run `devcontainer exec --workspace-folder . make test` — 100% green.
3. Run a quick regression check on the 5×100 MBA smoke sets (verify zero regressions from incremental solver reuse or OES ranking!) and verify the CHS adaptive scheduler on a focused CHS regression batch (comparing attempt counts / wall time / accepted reductions).
4. Mark all 7 completed items `[x]` in `docs/PLAN.md`, record concise validation results in `docs/IMPLEMENTATION_RESULTS.md`, and commit atomically (do not modify `docs/neon-review*.md`).
