# GreySynth Round-62 Spec: Subtraction-Form Absorbed `offer_linear_sum` (`norm_linear.ml`) + AC-Unified Zero-SMT `gf2_masked_xor_candidate` (`norm_semilinear.ml`)

**Baseline:** Round 61 (cost-minimizing `demorgan_not` with `Xor` pushdown + zero-SMT `dag-not-pushdown` — **NEW ALL-TIME `dev_64` RECORD `529/880` exact & `1.7675x` geomean**; `+15` brand-new exacts on the newly shrunk 277-row `core_hard` including `mba_flatten +5`, `pldi_nonpoly +5`, `mba_obf_nonlinear +1` -> only 4 left!; `+1` on shrunk `L5`; `regression_smoke` `62/62` strict & `56/58` exact; **`0` refutations**!).

**Scope:** Producer-side ONLY (ZERO `src/proof/rewrite_proof.ml` edits!). Two super clean, surgical upgrades:

---

## 1. 3-Line Subtraction-Form Fix in the Absorbed Branch of `offer_linear_sum` (`src/greysynth/norm_linear.ml:336-380`)

- In Round 61, `build values` in `offer_linear_sum` (`norm_linear.ml:339-362`) was upgraded to fold `-1` coefficients via `E.Minus`, **but the absorbed branch (lines 367–378)** still built `absorbed = scale (normalize (Z.neg offset)) (demorgan_not body)` and combined it with `remaining` using `build_balanced E.Plus (absorbed :: values)`!
- Because of that, `1 + 3*x + (x & y)` STILL emitted `(-( ~(x & y))) + (3 * x)` (cost **9**) instead of **`(3 * x) - (~(x & y))` (cost 8 = EXACT GT)**!
- **Exact fix (`src/greysynth/norm_linear.ml:336-380`):**
  Parameterize `build const_offset values` and call `build Z.zero` in the absorbed branch:
  ```ocaml
    let offer_linear_sum offset terms =
      let terms = List.filter (fun (coefficient, _) ->
          not (Z.equal (normalize coefficient) Z.zero)) terms in
      let build const_offset values =
        let negative, positive =
          List.partition (fun (coefficient, _) ->
              Z.equal (normalize coefficient) mask) values
        in
        let positive =
          (if Z.equal (normalize const_offset) Z.zero then []
           else [ constant width (normalize const_offset) ])
          @ List.map (fun (coefficient, body) ->
                scale (normalize coefficient) body) positive
        in
        let base = match positive with
          | [] -> None | [ value ] -> Some value
          | values -> Some (build_balanced E.Plus values)
        in
        match base, List.map snd negative with
        | None, [] -> zeros width
        | None, head :: tail ->
            List.fold_left (fun total body -> E.binary E.Minus total body)
              (E.unary E.Minus head) tail
        | Some value, negatives ->
            List.fold_left (fun total body -> E.binary E.Minus total body)
              value negatives
      in
      offer (build offset terms);
      if not (Z.equal (normalize offset) Z.zero) then
        List.iteri (fun index (coefficient, body) ->
            if Z.equal (normalize coefficient) (normalize offset) then
              let remaining =
                terms |> List.mapi (fun i term -> i, term)
                |> List.filter_map (fun (i, term) ->
                       if i = index then None else Some term)
              in
              offer (build Z.zero
                ((normalize (Z.neg offset), demorgan_not body) :: remaining)))
          terms
    in
  ```
  - Immediately turns `1 + 3*x + (x & y)` -> **`(3 * x) - (~(x & y))` (cost 8)**, `1 + 2*y + (a & y)` -> **`(2 * y) - (~(a & y))` (cost 8)**, and `1 + b + 2*(x & ~b)` -> **`(2 * (x & (~b))) - (~b)` (cost 9)** — 100% zero-SMT `linear_mba_mod2w`!

---

## 2. AC-Unified Zero-SMT `gf2_masked_xor_candidate` (`src/greysynth/norm_semilinear.ml` + 3 Call Sites in `greysynth.ml` & `normalization.ml`)

- In Round 60, raising the term cap to `64` was landed, **but AC-canonicalization of opaque atoms inside `gf2_masked_xor_candidate` was not yet added**, leaving `aa47d91d545f26c8_w64`, `200901a16ddf2503_w64`, `cb67824ea6196472_w64`, `c731a7cf74ac2d9b_w64`, and `3e50d423ac3189f6_w64` (`mba-capabilities-v1`) uncancelled when identical compound atoms appear in different AC orders (`((x1 ^ x3) + x2)` vs `(x2 + (x3 ^ x1))`, `(3 + (A + B))` vs `((B + 3) + A)`).
- **Exact fix in `src/greysynth/norm_semilinear.ml` (`gf2_masked_xor_candidate`):**
  1. Add a small DAG-memoized AC canonicalizer `canonical_atom` inside `gf2_masked_xor_candidate` (depth `<= 8`, flattened arity `<= 8`):
     - Track `ring_edges = ref []`, `linear_edges = ref []`, `replacements = Nodes.create 64`, `ac_memo = Nodes.create 128`.
     - Recursively canonicalize operands of `Plus` / `Mul` (flatten + sort with `E.compare` + rebuild with `build_balanced`, recording `(original, canonical)` in `ring_edges` & `replacements` whenever `not (E.is_equal original canonical)`).
     - Recursively canonicalize operands of `And` / `Or` / `Xor` (flatten + sort with `E.compare` + rebuild with `build_balanced`, recording `(original, canonical)` in `linear_edges` & `replacements` whenever `not (E.is_equal original canonical)`).
     - In `parse`, apply `canonical_atom` to every opaque atom BEFORE returning `(Z.zero, [ atom, mask ])`!
  2. Build `rewritten_source` via a cycle-guarded memoized substitution of `replacements` on `expression` (identical to `norm_linear.ml:809-837`).
  3. Return `Some (candidate, List.rev !ring_edges, List.rev !linear_edges, rewritten_source)`!
  4. Update the 3 call sites (`root-gf2-masked-xor` & `post-dag-gf2-masked-xor` in `src/greysynth/greysynth.ml`, `dag-gf2-masked-xor` in `src/greysynth/normalization.ml`, plus `test/round54_test.ml` / `test/round55_test.ml` if they call `gf2_masked_xor_candidate` directly) to certify **100% ZERO-SMT** via:
     ```ocaml
     Rewrite.accepts_compositional ~pass:...
       ~equalities:[] ~ring_equalities ~linear_mba_equalities
       ~semilinear_mba_equalities:[ rewritten_source, candidate ]
       source candidate
     ```

---

## Verification Gate for Round 62

1. **Regression Tests (`test/round62_test.ml`, plus warning-clean `make test`):**
   - `1 + 3*x + (x & y)` -> cost **`8`** (`(3 * x) - (~(x & y))`), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `1 + 2*y + (a & y)` -> cost **`8`**, zero-SMT `linear_mba_mod2w`!
   - Synthetic AC-permuted 10-atom masked-XOR identity (`((a + b) & m1) ^ ((b + a) & m1) ^ ...`) -> collapses via `gf2_masked_xor_candidate` with ZERO SMT and replays independently via `mba_proof`!
   - `aa47d91d545f26c8_w64` (`mba-capabilities-v1`: `12,344 -> <= 45`, `< 1.0s`, independent `mba_proof` replay!)
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r62-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r62-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r62-leeky-dev64/out.jsonl` — target: **big `mba-capabilities-v1` jump & new `dev_64` record `<= 1.65x`!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`165` shrunk cases -> `/tmp/r62-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`277` refreshed cases -> `/tmp/r62-core/out.jsonl` — target: `>= 25` exact on the refreshed 277-row frontier!)
3. Record concise Round-62 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
