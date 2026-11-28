# GreySynth Round-59 Spec (Single-Focus): Universal Two's-Complement Constant Absorption `c + c * B -> (-c) * (~B)` & 2-Variable `{x, y, x | y}` Basis (`src/greysynth/norm_linear.ml`)

**Baseline:** Round 58 (timeout partial-work preservation + `dag-bitwise-ac <= 256` with `<= 32`-call cap — **ALL FOUR GATES AT NEW ALL-TIME RECORDS**: `dev_64` **`527/880` exact, `877/880` (`99.66%`) strict, `1.7878x`** with `mba-ladders-v1` **`0.9981x`**; `Tigress L5 (170)` **`170/170` (`100%`) strict & `11.25x`**; `core_hard (328)` **`~4.1x`**; `regression_smoke` **`56/58` exact, `62/62` strict, `0.8018x`**; **`0` refutations**!).

**Scope:** **ONLY ONE source file (`src/greysynth/norm_linear.ml`), ZERO `src/proof/rewrite_proof.ml` edits!**

**Why This Single-Focus Change Unlocks Direct Exact `<= GT` Wins Across 6+ Suites:**
- Forensic inspection of `r55-core` / `r55-l5` `+1` and `+2` near-misses showed two 100% general two's-complement / 2-variable linear-MBA identities that `norm_linear.ml` currently misses:
  1. **`c + c * B == (-c) * (~B)` (mod `2^w`) for arbitrary constant `c`:**
     - Generalizes Round 54's `1 + B -> -(~B)` to ALL constants `c mod 2^w`, including `c = -1` (`-1 - B == ~B`, collapsing `x1 - (x0 + 1)` -> `x1 + (~x0)`, saving 1 node on `tigress_lvl_5__target_1802`!), AND `c = 14, -20, -3, -12` (collapsing `14 + 14 * (~y & x) + 9 * y` -> `(-14) * (y | ~x) + 9 * y`, saving **2–3 AST nodes** on `mba_obf_nonlinear__line_0000639 / 860 / 879`, `neureduce__line_0000445`, `mba_flatten`, `pldi_nonpoly`, and `dev_64`!).
     - Proof: for every bit-vector `B`, `~B = -1 - B` mod `2^w`, so `(-c) * (~B) = (-c) * (-1 - B) = c + c * B` mod `2^w` identically — certified **100% ZERO-SMT** by existing `linear_mba_mod2w`!
  2. **2-Variable `{x, y, x | y}` Basis (`count = 2`):**
     - Any 2-variable linear MBA with `shifted = [0, v01, v10, v11]` satisfies:
       `f(x, y) - offset == (v11 - v01) * x + (v11 - v10) * y + (v10 + v01 - v11) * (x | y)` mod `2^w`!
     - Collapses `6 * y + 5 * (~y & x)` (cost 10) -> **`y + 5 * (x | y)` (cost 7**, beating GT=9 on `mba_obf_nonlinear__line_0000892`!) and `1 + b + 2 * (x & ~b)` (cost 10) -> **`1 + 2 * (x | b) - b` (cost 9 = EXACT GT** on `pldi_nonpoly__line_0000105`!).
     - Certified **100% ZERO-SMT** by existing `linear_mba_mod2w`!

---

## Exact Edits (`src/greysynth/norm_linear.ml` ONLY)

1. **Add `offer_linear_sum` helper inside `linear_candidates_with_rings` (right before line 600):**
   ```ocaml
   let sum_scaled_terms = function
     | [] -> zeros width
     | terms ->
         let positives, negatives =
           List.partition (fun (coefficient, _) -> not (Z.equal coefficient mask)) terms
         in
         let build_signed = function
           | [] -> None
           | (coefficient, body) :: rest ->
               let init = scale coefficient body in
               Some (List.fold_left (fun acc (c, b) ->
                   if Z.equal c mask then E.binary E.Minus acc b
                   else E.binary E.Plus acc (scale c b)) init rest)
         in
         Option.value (build_signed (positives @ negatives)) ~default:(zeros width)
   in
   let offer_linear_sum offset terms =
     let offset = normalize offset in
     let terms =
       List.filter_map (fun (c, b) ->
           let c = normalize c in
           if Z.equal c Z.zero then None else Some (c, b)) terms
     in
     let body = sum_scaled_terms terms in
     offer (if Z.equal offset Z.zero then body
            else if terms = [] then constant width offset
            else if Z.equal offset mask then E.binary E.Minus body (constant width Z.one)
            else E.binary E.Plus (constant width offset) body);
     if not (Z.equal offset Z.zero) then (
       let neg_offset = normalize (Z.neg offset) in
       List.iteri (fun target_idx (c_j, b_j) ->
           if Z.equal c_j offset then
             let absorbed =
               List.mapi (fun idx (c, b) ->
                   if idx = target_idx then (neg_offset, demorgan_not b_j)
                   else (c, b)) terms
             in
             offer (sum_scaled_terms absorbed))
         terms)
   in
   ```
   *(Check carefully: if `offset = -1` (`mask`) and `terms = [(1, x1); (-1, x0)]`, then for `target_idx = 1`, `c_j = -1 = offset`, `neg_offset = 1`, `absorbed = [(1, x1); (1, ~x0)]`, yielding `x1 + (~x0)` (cost 4)! If `offset = 14` and `terms = [(14, ~y & x); (9, y)]`, then for `target_idx = 0`, `c_j = 14 = offset`, `neg_offset = -14`, `demorgan_not (~y & x) = y | ~x`, yielding `(-14) * (y | ~x) + 9 * y` (cost 9)!)*

2. **Wire `offer_linear_sum` into 3 places in `src/greysynth/norm_linear.ml`:**
   - **Place A (lines 616–645, 2/3/4-value shifted reconstructor):**
     - On `| [ zero; first; second ]` -> call `offer_linear_sum offset [ first, first_boolean; second, second_boolean ]`!
     - On `| [ zero; first; second; combined ]` -> call `offer_linear_sum offset [ first, first_boolean; second, second_boolean ]`!
   - **Place B (2-variable `{x, y, x | y}` basis, right after line 645 when `count = 2`):**
     - Notice in `norm_linear.ml` how `target` is indexed: verify whether index `1` is `(atom0=1, atom1=0)` (`bit 0` = `atoms.(0)`) and index `2` is `(atom0=0, atom1=1)` (`bit 1` = `atoms.(1)`)!
     - With `v10 = shifted.(1)` (`atoms.(0)=1, atoms.(1)=0`), `v01 = shifted.(2)` (`atoms.(0)=0, atoms.(1)=1`), `v11 = shifted.(3)`:
       - `c_x = normalize (Z.sub v11 v01)`
       - `c_y = normalize (Z.sub v11 v10)`
       - `c_or = normalize (Z.sub (Z.add v10 v01) v11)`
       - Verify: at `(0,0)` -> `0`; at `(1,0)` -> `c_x + c_or = v10`; at `(0,1)` -> `c_y + c_or = v01`; at `(1,1)` -> `c_x + c_y + c_or = v11`!
       - Call `offer_linear_sum offset [ c_x, atoms.(0); c_y, atoms.(1); c_or, E.binary E.Or atoms.(0) atoms.(1) ]`!
     - Also try the `{x, y, x & y}` basis via `offer_linear_sum offset [ v10, atoms.(0); v01, atoms.(1); normalize (Z.sub (Z.sub v11 v10) v01), E.binary E.And atoms.(0) atoms.(1) ]` so `offset` absorption works on `{x, y, x & y}` too!
   - **Place C (lines 720–736, Möbius-inversion reconstructor):**
     - Collect `mobius_terms` `(coefficient, term)` for all non-zero `subset >= 1`. When `not (Z.equal coefficients.(0) Z.zero)` and `List.length mobius_terms <= 4`, call `offer_linear_sum coefficients.(0) mobius_terms`! (That immediately unlocks `x1 - (x0 + 1) -> x1 + (~x0)` AND `c + c*x + ... -> (-c)*(~x) + ...` for ANY 1..4-atom linear MBA!)

---

## Verification Gate for Round 59

1. **Regression Tests (`test/round59_test.ml`, plus warning-clean `make test`):**
   - `14 + 14 * ((~y) & x) + 9 * y` (`mba_obf_nonlinear__line_0000860` shape) -> cost `<= 10`, zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `6 * y + 5 * ((~y) & x)` (`mba_obf_nonlinear__line_0000892` shape) -> cost `<= 7`, zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `1 + b + 2 * (x & (~b))` (`pldi_nonpoly__line_0000105` shape) -> cost `<= 9`, zero-SMT `linear_mba_mod2w`!
   - `x1 - (x0 + 1)` (`tigress_lvl_5__target_1802` shape) -> cost `4` (`x1 + (~x0)`), zero-SMT `linear_mba_mod2w`!
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r59-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r59-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r59-leeky-dev64/out.jsonl`)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`170` shrunk cases -> `/tmp/r59-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`328` refreshed cases -> `/tmp/r59-core/out.jsonl` — expect major exact `<= GT` jump on `mba_obf_nonlinear`, `neureduce`, `pldi_nonpoly`, `mba_flatten`!)
3. Record concise Round-59 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
