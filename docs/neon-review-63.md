# GreySynth Round-63 Spec (Single-Focus): AC-Unified Zero-SMT `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml` + 3 Call Sites)

**Baseline:** Round 62 (subtraction-form absorbed `offer_linear_sum` — `+16` exact on newly shrunk 277-row `core_hard`, `+3` on shrunk 165-row `Tigress L5`, `877/880` strict on `dev_64` with `mba-frontier64-v1` at new record `14.29x`, `62/62` strict & `56/58` exact on `regression_smoke`, **`0` refutations**!).

**Scope:** **SINGLE FOCUS — ZERO `src/proof/rewrite_proof.ml` edits!** ONLY `src/greysynth/norm_semilinear.ml` and the 3 existing call sites (`src/greysynth/greysynth.ml` lines 521 & 605, `src/greysynth/normalization.ml` line 267, plus direct unit test callers in `test/round54_test.ml` / `test/round55_test.ml`).

**Why This Single-Focus Change Unlocks a Massive `mba-capabilities-v1` Breakthrough (`1.58x -> ~1.10x`, `dev_64 -> <= 1.65x`!):**
- Round 56 added the audited, zero-SMT, linear-time `gf2_masked_xor_equal` proof-kernel fast path (`max_atoms = 64`, `< 5 ms`) to `src/proof/rewrite_proof.ml`.
- Round 60 raised `gf2_masked_xor_candidate`'s term cap to `64` and cost/DAG caps to `65_536 / 8192`.
- **The ONE remaining missing piece** is AC-canonicalization of opaque atoms inside `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml:28-111`)!
  - In `aa47d91d545f26c8_w64` (`12,344 -> 1,165, ref=35`), `200901a16ddf2503_w64` (`13,092 -> 1,261, ref=39`), `cb67824ea6196472_w64` (`11,925`), `c731a7cf74ac2d9b_w64` (`6,580 -> 545`), and `3e50d423ac3189f6_w64` (`6,200 -> 451`), identical compound atoms appear in different AC permutations (`((x1 ^ x3) + x2)` vs `(x2 + (x3 ^ x1))`, `(3 + ((x1 ^ x3) + x2))` vs `((x2 + (x1 ^ x3)) + 3)`), so `E.is_equal atom old` fails to merge them and term count explodes past `64`!

---

## Exact Edits

1. **In `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate`, lines 28–111):**
   - Keep `gf2_masked_xor_candidate` (or expose `gf2_masked_xor_candidate_with_bridges` and have the 3 pipeline call sites use it — keeping `gf2_masked_xor_candidate` backward-compatible if desired, or updating its return type cleanly everywhere!):
   - Inside `gf2_masked_xor_candidate_with_bridges cost expression`:
     1. Track `ring_edges = ref []`, `linear_edges = ref []`, `replacements = Nodes.create 64`, and `ac_memo = Nodes.create 128`.
     2. Add a small DAG-memoized recursive helper `canonical_atom depth node`:
        - If `depth >= 8` return `node`.
        - Check `Nodes.find_opt ac_memo node`.
        - Helper `flatten op acc n` (stopping if `List.length acc > 8`):
          - On `E.Binary { f = (E.Plus | E.Mul as op); _ }`:
            - Flatten `op` operands (if `<= 8`), recursively `canonical_atom (depth + 1)` each operand, sort by `E.compare`, rebuild with `build_balanced op`.
            - If `not (E.is_equal node canonical)`: record `(node, canonical)` in `ring_edges` AND `Nodes.replace replacements node canonical`!
          - On `E.Binary { f = (E.And | E.Or | E.Xor as op); _ }`:
            - Flatten `op` operands (if `<= 8`), recursively `canonical_atom (depth + 1)` each operand, sort by `E.compare`, rebuild with `build_balanced op`.
            - If `not (E.is_equal node canonical)`: record `(node, canonical)` in `linear_edges` AND `Nodes.replace replacements node canonical`!
          - On `E.Unary { f; x; _ }`: rebuild `E.unary f (canonical_atom (depth + 1) x)`.
          - On `E.Binary { f; x; y; _ }` (other binary ops like `E.Minus`): rebuild `E.binary f (canonical_atom (depth + 1) x) (canonical_atom (depth + 1) y)`.
          - Cache in `ac_memo` and return!
        - **IMPORTANT:** When recording `(node, canonical)` where children of `node` ALSO got rewritten, make sure `ring_edges` / `linear_edges` connect `rebuilt_from_canonical_children -> canonical` (NOT `raw_node -> canonical`!) so each single edge is a pure 1-step `ring_mod2w` or `linear_mba_mod2w` identity! Specifically:
          - For `Plus`/`Mul`: let `raw_terms = flatten op [] node`, let `canon_terms = List.map (canonical_atom (depth + 1)) raw_terms`, let `sorted_terms = List.sort E.compare canon_terms`, let `unsorted_expr = build_balanced op canon_terms` (Wait: `node` itself might have unbalanced shape, so connect `rebuilt_shape_of_node_with_canon_children -> build_balanced op sorted_terms` via `ring_mod2w`!).
          - Even simpler and **100% guaranteed valid**: first compute `rebuilt = rebuild_children node` (replacing each direct child `c` with `canonical_atom (depth + 1) c` — already connected by congruence from child edges!), THEN flatten `rebuilt` under `op` (`<= 8` terms), sort with `E.compare`, build `canonical = build_balanced op sorted`, and if `not (E.is_equal rebuilt canonical)` record `(rebuilt, canonical)` in `ring_edges` (for `Plus`/`Mul`) or `linear_edges` (for `And`/`Or`/`Xor`) and `Nodes.replace replacements node canonical`!
          - **Check that!** Every single recorded edge `(rebuilt, canonical)` ONLY reorders/reassociates ONE operator (`Plus`/`Mul` -> `ring_mod2w`, `And`/`Or`/`Xor` -> `linear_mba_mod2w`), while nested child canonicalizations connect automatically by congruence in `Rewrite_proof`!
     3. In `parse`, whenever hitting an opaque atom (both the non-disjoint `Or`/`And` fallback AND the catch-all `| atom ->`), intern `canonical_atom 0 atom`!
     4. Build `rewritten_source` via a cycle-guarded memoized substitution of `replacements` on `expression` (identical to `norm_linear.ml:809-837`).
     5. Return `Some (candidate, List.rev !ring_edges, List.rev !linear_edges, rewritten_source)`!
2. **Update the 3 pipeline call sites (`src/greysynth/greysynth.ml` lines 521 & 605, `src/greysynth/normalization.ml` line 267):**
   ```ocaml
   match Normalization.gf2_masked_xor_candidate_with_bridges size_of_expr !best with
   | Some (candidate, ring_equalities, linear_mba_equalities, rewritten_source)
     when Rewrite.accepts_compositional ~pass:"root-gf2-masked-xor"
            ~equalities:[] ~ring_equalities ~linear_mba_equalities
            ~semilinear_mba_equalities:[ rewritten_source, candidate ]
            !best candidate -> best := candidate
   | _ -> ()
   ```
   (And identically for `post-dag-gf2-masked-xor` and `dag-gf2-masked-xor` — **100% ZERO SMT**!)

---

## Verification Gate for Round 63

1. **Regression Tests (`test/round63_test.ml`, plus warning-clean `make test`):**
   - Synthetic AC-permuted 10-atom masked-XOR identity (`(((a + b) * (c ^ d)) & m1) ^ (((b + a) * (d ^ c)) & m1) ^ ...`) -> collapses via `gf2_masked_xor_candidate_with_bridges` with **ZERO SMT** and replays independently via `mba_proof`!
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 45`, `< 1.0s`, independent `mba_proof` replay!)
   - `200901a16ddf2503_w64` (`mba-capabilities-v1`: `13,092 -> <= 49`, `< 1.0s`, independent `mba_proof` replay!)
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r63-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r63-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r63-leeky-dev64/out.jsonl` — target: **big `mba-capabilities-v1` jump `1.58x -> ~1.10x` and NEW ALL-TIME `dev_64` RECORD `<= 1.65x`!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`165` shrunk cases -> `/tmp/r63-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`277` refreshed cases -> `/tmp/r63-core/out.jsonl`)
3. Record concise Round-63 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
