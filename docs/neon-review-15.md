# GreySynth Round-15 Spec: Closing Milestones 2, 3 (Remaining), and 9

**Baseline commit:** `f4088c8` (Milestone 4A complete: 5/5 100-case MBA datasets matching/beating baseline at `0.7595x–0.9966x`, 1,000/1,000 C-Full with 0 timeouts)  
**Goal:** Close 5 of the remaining 13 unchecked items in [docs/PLAN.md](PLAN.md) cleanly in focused, atomic commits — leaving Rounds 16–17 to finish Milestone 7 (adaptive CHS), Milestone 4/5 polish, Milestone 8 whole-pipeline extraction, and expanded corpus audits (`Loki`/`Full-Loki`, etc.).

---

## 1. Milestone 2 (Line 92) — Centralize Configuration Parsing, Defaults, Validation & Reporting

Currently `src/greysynth/config.ml` manually parses ~40 keys with duplicated `match json |> member ...` blocks, `default.json` duplicates the defaults, and `src/greysynth/greysynth.ml:332-375` duplicates the same ~40 keys inside `report_json`.

**Deliverables (`src/greysynth/config.ml`, `src/greysynth/greysynth.ml`):**
1. Define a single declarative configuration specification table in `src/greysynth/config.ml` covering every option (`json_key`, `report_key`, default value, required vs optional, range/enum validator, and JSON serializer).
2. Add `Config.reset_defaults ()` so library invocations and tests can cleanly reset all knobs to canonical defaults.
3. Drive `Config.load_config_from_json` from that single table (preserving all existing validations, including rejecting renamed keys like `local_synthesis`, and warning/failing cleanly on invalid types or out-of-range numbers).
4. Expose `Config.report_fields () : (string * Yojson.Basic.t) list` and have `Greysynth.report_json` emit config fields directly from `Config.report_fields ()` (preserving existing JSON keys so `audit_dataset.py` and existing tests stay 100% backwards-compatible!).
5. Add a focused test in `test/pipeline_test.ml` verifying that `default.json` loads cleanly, invalid configs fail with descriptive errors, and toggling reported options changes both `Config.report_fields ()` and pipeline behavior.

---

## 2. Milestone 3 (Line 152) — General Null-Polynomial Reduction & Rivest/Hensel Permutation-Polynomial Inversion

Currently `normalization.ml:155-177` only handles a single quadratic product `c * x * (x - 1)` when `2^(w-1) | c`.

**Deliverables (`src/greysynth/normalization.ml`):**
1. **General falling-factorial null-polynomial reduction (`reduce_univariate_null_polynomial`):**
   - For a univariate polynomial $P(x) = \sum_{d=0}^D a_d x^d \pmod{2^w}$ ($2 \le D \le 8$), convert to the falling-factorial basis $P(x) = \sum_{k=0}^D b_k \cdot x^{\underline{k}}$ where $x^{\underline{k}} = x(x-1)\cdots(x-k+1)$.
   - By Kempner/Singmaster's theorem, $b_k \cdot x^{\underline{k}} \equiv 0 \pmod{2^w}$ whenever $2^{w - v_2(k!)} \mid b_k$ (where $v_2(k!) = \sum_{j \ge 1} \lfloor k / 2^j \rfloor$).
   - Drop every null falling-factorial term and emit a **compositional proof**:
     - One local `"smt"` lemma per dropped null term `(c_k * x*(x-1)*...*(x-k+1), 0)` (note: for 64-bit higher degrees, if monolithic `c_k * x*(x-1)*... == 0` is slow in Bitwuzla, factor into `((x*(x-1)*...*(x-k+1)) & ((1 << v_2(k!)) - 1)) == 0` or `((x*(x-1)*...*(x-k+1)) << (w - v_2(k!))) == 0` — pure low-bit / shift proof — plus `ring_mod2w`!),
     - One `"ring_mod2w"` edge connecting `P(x)` to `reduced(x) + sum dropped_terms`!
   - Wire into both `Normalization.run` and `Normalization.local_candidates`.
2. **Explicit Rivest/Hensel univariate permutation-polynomial inversion:**
   - Implement `is_permutation_poly ~width coeffs` using Rivest's exact necessary-and-sufficient criterion mod $2^w$ ($w \ge 2$): $a_1$ odd, $\sum_{d \ge 2 \text{ even}} a_d$ even, and $\sum_{d \ge 3 \text{ odd}} a_d$ even.
   - Implement `invert_permutation_poly ~width ~max_degree coeffs` computing the inverse polynomial $P^{-1}(y) \pmod{2^w}$ via Hensel/Newton lifting (when $P(x) = a_0 + a_1 x + 2^s Q(x)$ admits a low-degree inverse of degree $\le \text{max\_degree}$, e.g. $D \le 8$).
   - Recognize nested univariate compositions $Q(P(x))$ (and detect when expanding + falling-factorial null reduction collapses `P^{-1}(P(x)) -> x` or simplifies $Q(P(x))$ to a lower-degree polynomial, such as `perm_poly_quad` and 8/16/32/64-bit quadratic/cubic permutation-polynomial inverses!), certified via `ring_mod2w` + falling-factorial null lemmas.
3. **Focused unit tests (`test/normalization_test.ml`):**
   - Higher-order null polynomials (`k = 2, 3, 4` at 8/16/32/64 bits) with independent `mba_proof` replay,
   - Rivest criterion + Hensel inversion round-trip (`P^{-1}(P(x)) == x`) at 8/16/32/64 bits including `perm_poly_quad`, with `mba_proof` replay.

---

## 3. Milestone 3 (Line 114) & Milestone 9 (Lines 294–295) — Mixed-Width Identities, Predicate Extraction, Select/Min/Max Idioms & Explicit `E.Load` Boundary

**Deliverables (`src/greysynth/normalization.ml`, `src/greysynth/greysynth.ml`, `src/proof/rewrite_proof.ml`):**
1. **Mixed-width-safe & mask composition identities (`normalization.ml` `peepholes`):**
   - Mask absorption/composition: `(x & m1) & m2 -> x & (m1 & m2)`, `(x | m1) | m2 -> x | (m1 | m2)`, `(x ^ c1) ^ c2 -> x ^ (c1 ^ c2)`, `(x & m) | (x & ~m) -> x`, `(x & m) ^ (x & ~m) -> x`.
   - Extension/restriction composition: `uext_a (uext_b x) -> uext_(a+b) x`, `sext_a (sext_b x) -> sext_(a+b) x`, `restrict(0, hi) (uext x)` / `restrict(0, hi) (sext x)` when `hi < width(x)` -> `restrict(0, hi) x` (or `x` when `hi = width(x) - 1`), and `(x >>u k) << k -> x & (~((1 << k) - 1))` for constant `0 < k < width`.
   - All proof-gated by the shared acceptance policy (never assuming mixed-width identities without SMT proof!).
2. **Predicate extraction & proved select/min/max/abs idioms (`normalization.ml` `peepholes`):**
   - Condition canonicalization: `(!c) ? t : e -> c ? e : t`, `(a != b) ? t : e -> (a == b) ? e : t`.
   - Same-condition nested ITE collapse: `c ? (c ? a : b) : d -> c ? a : d` and `c ? a : (c ? b : d) -> c ? a : d`.
   - **Equality predicate propagation:** in `(x == k) ? t : e`, substitute `x -> k` inside `t` (when it strictly lowers cost after constant folding, e.g. `(x == 0) ? (x + y) : z -> (x == 0) ? y : z`); dually for `(x != k) ? t : e`, substitute `x -> k` inside `e`.
   - **Branchless select / min / max idiom recovery:**
     - `((a ^ b) & sext(c)) ^ b -> c ? a : b` (and commuted forms),
     - `(a & sext(c)) | (b & ~sext(c)) -> c ? a : b`,
     - `a + ((b - a) & sext(c)) -> c ? b : a`,
     - Unsigned/signed min/max boundary simplifications: `(a <u 0) ? ...` (already folded by comparison bounds), `(a <u b ? a : b)` when `a = b -> a`, `min_u(a, 0) -> 0`, `max_u(a, 0) -> a`, `min_u(a, -1) -> a`, `max_u(a, -1) -> -1`, `min_s(a, min_sbv) -> min_sbv`, `max_s(a, max_sbv) -> max_sbv`.
   - Every candidate respects `!cost_model` (only accepted when strictly cheaper under the configured cost model and SMT-proved!).
3. **Explicit `E.Load` / memory-load boundary (`Milestone 9 line 295`):**
   - Ensure `Greysynth.run` checks `contains_load obf` (or catches the explicit load-boundary check) cleanly: memory loads are **never** silently treated as proved pure-bitvector expressions (`equiv` stays `"ukn"` / explicit `"outside_proof_semantics"` reason, no bogus certificate emitted).
   - Add dedicated tests in `test/proof_test.ml` and `test/pipeline_test.ml` confirming `E.Load` fails closed in `Rewrite_proof` and never claims a pure-expression proof in `Greysynth`.

---

## 4. Acceptance Targets for Round 15

1. All 5 items above implemented with focused unit tests (`config` centralization + validation, higher-order null polynomials + Rivest/Hensel permutation-polynomial inversion, mixed-width mask/cast compositions, predicate extraction + select/min/max idioms, explicit `E.Load` boundary tests).
2. `devcontainer exec --workspace-folder . make test` passes 100% green.
3. Verify zero regression on the 5×100 MBA smoke suites (and check `PLDI Poly` / `C-Full` if touched).
4. Mark the 5 completed items `[x]` in `docs/PLAN.md`, record concise results in `docs/IMPLEMENTATION_RESULTS.md`, and commit atomically (do not modify `docs/neon-review*.md`).
