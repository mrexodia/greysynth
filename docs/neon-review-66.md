# GreySynth Round-66 Spec (Single-Focus): O(1) 4-Var Separable Boolean Factorization + `synth2 (f0 lxor f1)` Shannon XOR-MUX + Top-Level `(~a) - ((~b) + c) -> (b - a) - c` (`src/greysynth/norm_linear.ml`)

**Baseline:** Round 65 (`9c0f13dd` — **MASSIVE BREAKTHROUGH**: `dev_64` jumped **`527 -> 573 / 880` (`+46` exacts, `65.1%` hit rate!!)** with `mba-proof-context-v1` **`36/36 (100% @ 1.0000x)`**, `mba-extra-floor-v1` **`45/54` (`+17`)**, `mba-majority-v1` **`44/54` (`+8`)**, `mba-ladders-v1` **`57/72 @ 0.9699x`**; refreshed `core_hard (277)` jumped **`16 -> 27 / 276` exact & `7.446x`**; shrunk `L5 (165)` jumped **`2 -> 6 / 165` exact**; **`0` refutations**!).

**Scope:** **ONLY ONE source file (`src/greysynth/norm_linear.ml`), ZERO `src/proof/rewrite_proof.ml` edits!** Three tiny surgical fixes caught by inspecting the Round-65 diff:

---

## Exact Edits (`src/greysynth/norm_linear.ml` ONLY)

1. **Move `(~a) - (~b)` and `(~a) - ((~b) + c)` to the Top Level of `not_pushdown_candidate` (`norm_linear.ml:48-75`):**
   - In Round 65, those arms were accidentally placed INSIDE `| E.Unary { f = E.Not; x; _ } ->` (matching `~((~a) - (~b))` instead of `(~a) - (~b)` directly!), so `neureduce` stayed `0/5`!
   - Place them at the **top level** of `match expression with` in `not_pushdown_candidate`:
     ```ocaml
     let not_pushdown_candidate cost expression =
       if cost expression > 64 then None
       else
         let candidates =
           match expression with
           | E.Unary { f = E.Not; x; _ } ->
               demorgan_not x ::
               (match x with
               | E.Binary { f = E.Plus; x = E.Unary { f = E.Not; x = a; _ }; y = b; _ }
               | E.Binary { f = E.Plus; x = b; y = E.Unary { f = E.Not; x = a; _ }; _ } ->
                   [ E.binary E.Minus a b ]
               | E.Binary { f = E.Minus; x = left; y = right; _ } ->
                   [ E.binary E.Plus right (demorgan_not left) ]
               | _ -> [])
           | E.Binary { f = E.Minus;
                        x = E.Unary { f = E.Not; x = a; _ };
                        y = E.Unary { f = E.Not; x = b; _ }; _ } ->
               [ E.binary E.Minus b a ]
           | E.Binary { f = E.Minus;
                        x = E.Unary { f = E.Not; x = a; _ };
                        y = E.Binary { f = E.Plus;
                              x = E.Unary { f = E.Not; x = b; _ }; y = c; _ }; _ }
           | E.Binary { f = E.Minus;
                        x = E.Unary { f = E.Not; x = a; _ };
                        y = E.Binary { f = E.Plus;
                              x = c; y = E.Unary { f = E.Not; x = b; _ }; _ }; _ } ->
               [ E.binary E.Minus (E.binary E.Minus b a) c ]
           | _ -> []
         in
         candidates
         |> List.filter (fun candidate -> cost candidate < cost expression)
         |> List.sort (fun left right -> Int.compare (cost left) (cost right))
         |> function candidate :: _ -> Some candidate | [] -> None
     ```
   - Immediately closes **4 of the last 5 `neureduce` cases** (`lines 798, 468, 743, 685`) with ZERO SMT!

2. **Use `synth2 u v (f0 lxor f1)` for 3-Var Shannon XOR-MUX (both `lines 484-489` AND `lines 650-656`):**
   - Replace `E.binary E.Xor s0 s1` with `let s_xor = synth2 u v (f0 lxor f1) in` (so e.g. `s0 = u & v, s1 = u | v` synthesizes `u ^ v` cost 3 instead of `(u & v) ^ (u | v)` cost 7 -> **4 nodes smaller**!) and also add the symmetric `p`-negated forms:
     ```ocaml
     let s_xor = synth2 u v (f0 lxor f1) in
     shannon := E.binary E.Xor (E.binary E.And pivot_atom s_xor) s0 :: !shannon;
     shannon := E.binary E.Xor (E.binary E.And (demorgan_not pivot_atom) s_xor) s1 :: !shannon;
     if f0 land (15 lxor f1) = 0 then
       shannon := E.binary E.Or s0 (E.binary E.And pivot_atom s1) :: !shannon;
     if f1 land (15 lxor f0) = 0 then
       shannon := E.binary E.Or s1 (E.binary E.And (demorgan_not pivot_atom) s0) :: !shannon
     ```
     (and identically in the `active_count = 3` block on `lines 650-656`!).

3. **Replace the `36,864`-Iteration 4-Var Nested Loop (`lines 490-528`) with O(1) 4-Row Factorization (3,000x Faster!) AND Call It in BOTH `boolean_candidates` AND `active_count = 4` (`line 656`)!**
   - Lift ONE shared helper `separable4_candidates synth2 get_atom truth` (~25 lines, ONLY **3 pairings × 4 rows = 12 ops**, ZERO `16×16×16` brute force!):
     ```ocaml
     let separable4_candidates synth2 get_atom truth =
       let found = ref [] in
       List.iter (fun (u0, u1, v0, v1) ->
         let rows = Array.init 4 (fun a ->
           let mask = ref 0 in
           for b = 0 to 3 do
             let idx =
               (if a land 1 <> 0 then 1 lsl u0 else 0)
               lor (if a land 2 <> 0 then 1 lsl u1 else 0)
               lor (if b land 1 <> 0 then 1 lsl v0 else 0)
               lor (if b land 2 <> 0 then 1 lsl v1 else 0)
             in
             if truth.(idx) then mask := !mask lor (1 lsl b)
           done;
           !mask)
         in
         let a0 = get_atom u0 and a1 = get_atom u1
         and b0 = get_atom v0 and b1 = get_atom v1 in
         (* Or: all rows <> 15 are equal to some h *)
         (match Array.find_opt (fun r -> r <> 15) rows with
         | Some h when Array.for_all (fun r -> r = 15 || r = h) rows ->
             let g = ref 0 in
             for a = 0 to 3 do if rows.(a) = 15 then g := !g lor (1 lsl a) done;
             found := E.binary E.Or (synth2 a0 a1 !g) (synth2 b0 b1 h) :: !found
         | _ -> ());
         (* And: all rows <> 0 are equal to some h *)
         (match Array.find_opt (fun r -> r <> 0) rows with
         | Some h when Array.for_all (fun r -> r = 0 || r = h) rows ->
             let g = ref 0 in
             for a = 0 to 3 do if rows.(a) <> 0 then g := !g lor (1 lsl a) done;
             found := E.binary E.And (synth2 a0 a1 !g) (synth2 b0 b1 h) :: !found
         | _ -> ());
         (* Xor: every row is r0 or (15 lxor r0) *)
         let r0 = rows.(0) in
         if Array.for_all (fun r -> r = r0 || r = (15 lxor r0)) rows then (
           let g = ref 0 in
           for a = 0 to 3 do if rows.(a) <> r0 then g := !g lor (1 lsl a) done;
           found := E.binary E.Xor (synth2 a0 a1 !g) (synth2 b0 b1 r0) :: !found))
         [ 0, 1, 2, 3; 0, 2, 1, 3; 0, 3, 1, 2 ];
       !found
     ```
   - Call `separable4_candidates` in BOTH:
     - `boolean_candidates` when `count = 4 && cost expression <= 128`, AND
     - the 2-value block (`line 656`) when `active_count = 4 && cost expression <= 128`!
   - **Impact:** Eliminates the `14.25x -> 15.77x` `mba-frontier64-v1` speed drag from R65's 36,864-iteration loop (pushing `dev_64` to a **NEW ALL-TIME RECORD `~575+/880` exact & `~1.72x` geomean!!**) AND unlocks 4-var separable Boolean exacts (`c_mba_obfuscator__target_233`, `omvll__target_233`, `mba_flatten`, `pldi_poly`)!

---

## Verification Gate for Round 66

1. **Regression Tests (`test/round66_test.ml`, plus warning-clean `make test`):**
   - `(~a) - ((~b) + c)` -> `(b - a) - c` (top-level `not_pushdown_candidate` -> `neureduce__line_0000468 / 743` shape!), zero-SMT `linear_mba_mod2w`, independent `mba_proof` replay!
   - Majority `Maj(p, u, v)` -> cost **`9`** (`(p & (u ^ v)) ^ (u & v)` or `(u & v) | (p & (u | v))`), zero-SMT `linear_mba_mod2w`!
   - `((x1 & x2) + (x0 & x3)) - ((x0 & x1) & (x2 & x3))` -> cost **`7`** (`(x1 & x2) | (x0 & x3)`), zero-SMT `linear_mba_mod2w`!
2. **Curated Benchmark Gate (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM < 30 GB, retain `/tmp/r66-*/out.jsonl`, NEVER run `heldout_balanced64`!):**
   - **RUN `regression_smoke` FIRST** (`62` cases -> `/tmp/r66-smoke/out.jsonl`): **MUST PASS `62/62` strict, `>= 56/58` exact, `<= 0.805x`, `0` refutations!**
   - **`datasets/leeky/adapted/dev_64/`** (`884` cases -> `/tmp/r66-leeky-dev64/out.jsonl` — target: **NEW ALL-TIME RECORD `>= 575/880` exact & `<= 1.74x` geomean!**)
   - **`datasets/hard_cases/all_non_exact/tigress_l5/`** (`165` shrunk cases -> `/tmp/r66-l5/out.jsonl`)
   - **`datasets/hard_cases/core_hard/`** (`277` refreshed cases -> `/tmp/r66-core/out.jsonl` — expect `neureduce` `3..4/5` exact & `>= 30` total exact!)
3. Record concise Round-66 results in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
