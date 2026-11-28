# GreySynth Round-65 Spec (Single-Focus): 3-Var Shannon XOR/OR-MUX + 4-Var 2+2 Separable Boolean Decomposition + `~((~A)+B) -> A-B` / `(~A)-((~B)+C) -> (B-A)-C` (`src/greysynth/norm_linear.ml`)

**Baseline:** Round 64 (`e42f3e09` — lazy opaque-atom AC canonicalization in `norm_semilinear.ml`: new panel records on `mba-ladders-v1` `54/72 @ 0.9957x`, `mba-extra-floor-v1` `28/54 @ 1.2200x`, `mba-frontier64-v1` `2/96 @ 14.25x`; `r64-core` `+16` exact on shrunk 277-row frontier; `r64-smoke` `62/62` strict & `56/58` exact; **`0` refutations**!).

**Scope:** **ONLY ONE source file (`src/greysynth/norm_linear.ml`), ZERO `src/proof/rewrite_proof.ml` edits!** Every candidate is certified **100% ZERO-SMT** by existing `linear_mba_mod2w`.

---

## Exact Edits (`src/greysynth/norm_linear.ml` ONLY)

1. **General 3-Variable Shannon XOR-MUX & OR-MUX (`norm_linear.ml:554-594` AND inside `boolean_candidates`!):**
   - Lift `synth2 u v bits` so BOTH `boolean_candidates` AND the 2-value block (`lines 554-593`) can use it!
   - Inside the `for pivot = 0 to 2 do` loop (`lines 569-593`), right after `let s0 = synth2 u v f0 and s1 = synth2 u v f1 in`, compute `let s_xor = synth2 u v (f0 lxor f1) in` and add:
     ```ocaml
     booleans := E.binary E.Xor (E.binary E.And p s_xor) s0 :: !booleans;
     booleans := E.binary E.Xor (E.binary E.And (demorgan_not p) s_xor) s1 :: !booleans;
     if (f0 land f1) = f0 then
       booleans := E.binary E.Or s0 (E.binary E.And p s1) :: !booleans;
     if (f0 land f1) = f1 then
       booleans := E.binary E.Or s1 (E.binary E.And (demorgan_not p) s0) :: !booleans;
     ```
     - **Algebraic verification:**
       - `(p & (f0 ^ f1)) ^ f0`: at `p=0` -> `f0`; at `p=1` -> `f0 ^ f1 ^ f0 = f1`! Synthesizes MUX (`(p & (u ^ v)) ^ u`, cost **7** — closes `c_mba_obfuscator__target_4300`, `target_3778`, `tigress_lvl_5__target_3778`), Majority (`(u & v) | (p & (u | v))` and `(p & (u ^ v)) ^ (u & v)`, cost **9** — boosts `mba-majority-v1`), and compact 3-var Boolean terms across `mba_flatten`, `pldi_poly`, `omvll`, and `dev_64`!
   - Also apply this same 3-var Shannon `pivot = 0..2` synthesis inside `boolean_candidates truth` whenever `active_count = 3` (or `Array.length atoms = 3`) so weighted sums `c1 * B1 + c2 * B2` get compact 7–9 node Boolean factors too!

2. **Exact 4-Variable 2+2 Separable Boolean Decomposition (`active_count = 4`, `cost expression <= 128`, right after line 593):**
   - For the 3 disjoint pairings `((0, 1), (2, 3))`, `((0, 2), (1, 3))`, `((0, 3), (1, 2))` of `{0, 1, 2, 3}`:
     - Let `u0 = atoms.(active.(i0))`, `u1 = atoms.(active.(i1))`, `v0 = atoms.(active.(j0))`, `v1 = atoms.(active.(j1))`.
     - Build the 4-row bitmask array `rows.(a)` (`a = 0..3`, 4-bit row mask over `b = 0..3`):
       `bit b` of `rows.(a)` is `1` iff `truth.( (bit0(a) lsl i0) lor (bit1(a) lsl i1) lor (bit0(b) lsl j0) lor (bit1(b) lsl j1) )`.
     - **Check `Or` (`g(u0, u1) | h(v0, v1)`):**
       - Find any row `r <> 15`; if all non-`15` rows equal `r`:
         `g_bits` = 4-bit mask of rows `a` where `rows.(a) = 15`, `h_bits = r` -> emit `E.binary E.Or (synth2 u0 u1 g_bits) (synth2 v0 v1 h_bits)`!
     - **Check `And` (`g(u0, u1) & h(v0, v1)`):**
       - Find any row `r <> 0`; if all non-`0` rows equal `r`:
         `g_bits` = 4-bit mask of rows `a` where `rows.(a) <> 0`, `h_bits = r` -> emit `E.binary E.And (synth2 u0 u1 g_bits) (synth2 v0 v1 h_bits)`!
     - **Check `Xor` (`g(u0, u1) ^ h(v0, v1)`):**
       - Let `r0 = rows.(0)`; if every row `a` has `rows.(a) = r0 || rows.(a) = (15 lxor r0)`:
         `g_bits` = 4-bit mask of rows `a` where `rows.(a) <> r0`, `h_bits = r0` -> emit `E.binary E.Xor (synth2 u0 u1 g_bits) (synth2 v0 v1 h_bits)`!
     - **Example:** `((x1 & x2) + (x0 & x3)) - ((x0 & x1) & (x2 & x3))` (cost **15**) -> **`(x1 & x2) | (x0 & x3)` (cost 7 = EXACT GT** on `c_mba_obfuscator__target_233` & `omvll__target_233`!)!

3. **Two's-Complement Negated-Sum Cancellation in `not_pushdown_candidate` (`src/greysynth/norm_linear.ml:48-63`):**
   - Extend `not_pushdown_candidate cost expression` (still `cost <= 64`, still certified **100% ZERO-SMT** via `dag-not-pushdown` `linear_mba_mod2w`!):
     - On `E.Unary { f = E.Not; x = E.Binary { f = E.Plus; x = E.Unary { f = E.Not; x = a; _ }; y = b; _ }; _ }` (and symmetric `b + (~a)`):
       offer **`E.binary E.Minus a b`**! (Exact identity: `~((~a) + b) == -1 - ((-1 - a) + b) == a - b`!)
     - On `E.Binary { f = E.Minus; x = E.Unary { f = E.Not; x = a; _ }; y = E.Binary { f = E.Plus; x = E.Unary { f = E.Not; x = b; _ }; y = c; _ }; _ }` (and symmetric `c + (~b)`):
       offer **`E.binary E.Minus (E.binary E.Minus b a) c`**! (Exact identity: `(~a) - ((~b) + c) == (-1 - a) - (-1 - b + c) == (b - a) - c`!)
     - On `E.Binary { f = E.Minus; x = E.Unary { f = E.Not; x = a; _ }; y = E.Unary { f = E.Not; x = b; _ }; _ }`:
       offer **`E.binary E.Minus b a`**!
     - Closes **4 of the last 5 `neureduce` cases** (`lines 798, 468, 743, 685`) in `< 1 ms`!

---

## Verification Gate for Round 65

1. **Regression Tests (`test/round65_test.ml`, plus warning-clean `make test`):**
   - `((x2 & x1) + x0) - (x1 & x0)` -> cost **`7`** (3-var MUX), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `((x1 & x2) + (x0 & x3)) - ((x0 & x1) & (x2 & x3))` -> cost **`7`** (`(x1 & x2) | (x0 & x3)`), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - `~((~(v3 | v4)) + ((~v0) & (v1 ^ v2)))` -> cost **`10`** (`(v3 | v4) - ((~v0) & (v1 ^ v2))`), zero-SMT `linear_mba_mod2w`!
   - `(~a) - ((~b) + c)` -> `(b - a) - c` (strict decrease by 2 nodes), zero-SMT `linear_mba_mod2w`!
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r65-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r65-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r65-leeky-dev64/out.jsonl` — expect big jump on `mba-majority-v1` + new overall `dev_64` record!)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`165` shrunk cases -> `/tmp/r65-l5/out.jsonl` — expect `target_3778` + more exacts!)
   - **`datasets/hard_cases/core_hard/`** (`277` refreshed cases -> `/tmp/r65-core/out.jsonl` — expect `neureduce` 4/5 exact, `c_mba_obfuscator` +3, `omvll` +1, `mba_flatten` & `pldi_poly` jumps -> **`>= 25` exact**!)
3. Record concise Round-65 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
