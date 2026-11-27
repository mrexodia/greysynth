# GreySynth Round-35 Spec: Modular Refactor of `src/greysynth/normalization.ml` & Generality Audit

**Baseline:** Round 34 (`039ed2a` / `a161695` — `94.12%` exact `<= GT` across all 52,645 expressions with GT, `0` refutations, `all_non_exact/` shrunk to `3,100`, `core_hard/` at `353`, `regression_smoke/` at `62/62`).

**Motivation:**
Across Rounds 1–34, `src/greysynth/normalization.ml` grew into a **5,235-line / 230 KB monolith** containing six distinct algebraic engines, making it harder to read, audit for generality (verifying zero dataset overfitting), and maintain. This round is a **pure architectural modularization & hygiene pass** — split `normalization.ml` cleanly into cohesive, well-named modules with clear mathematical scope, remove any dead/redundant code, and preserve 100% proof-gated behavioral parity.

---

## 1. Clean Module Decomposition (`src/greysynth/`)

Split `src/greysynth/normalization.ml` into **eight cohesive modules** (and update `src/greysynth/dune` `(modules ...)` accordingly; keep `Normalization` as a clean top-level facade so zero external callers or tests break):

1. **`norm_common.ml`** (~150–250 lines):
   - Shared AST/bitvector/Zarith helpers: `Nodes` hashtbl, `constant`, `zeros`, `integer`, `constant_value`, `is_number`, `bounded_count`, `build_balanced`, `check_timeout`, `canonical_bitwise_atom`, `demorgan_not`, shared candidate record type (`candidate`), etc.
2. **`norm_peepholes.ml`** (~550–700 lines):
   - Standard compiler/bitwise algebraic peepholes (`peepholes`), `Known_bits` consumer (`known_bits_candidate`), slice/mask normalization (`mask_lift_candidate`, `complementary_slice_candidate`), power-of-two pullout & demand-bit narrowing (`power2_pullout_candidate`, `demand_bits_candidate`), and bitsliced equivalence (`bitsliced_candidate`, `bitsliced_ring_proof`).
3. **`norm_linear.ml`** (~700–850 lines):
   - Linear MBA & Boolean synthesis over $\mathbb{Z}_{2^w}$ (SiMBA/GAMBA truth-table reconstruction, exact signed bitvector 2-value offset theorem, 2-var lookup & 1-var Shannon factoring, `linear_candidates`, `linear_mba_compatible`, `disjoint_component_candidate`, `component_linear_candidates`, `partial_linear_sum_candidate`).
4. **`norm_semilinear.ml`** (~250–300 lines):
   - Decidable semi-linear MBA engine (MSiMBA Theorem 1.1 bit-mask basis): `semilinear_mba_candidate`, `has_nonuniform_bitwise_constant`, `xor_affine_mask_candidate`.
5. **`norm_poly.ml`** (~800–950 lines):
   - Modular polynomials & quotient rings $\mathbb{Z}_{2^w}[\vec{x}] / \mathcal{Z}^{w,k}$ (BAR '24): `is_permutation_poly`, `invert_permutation_poly_newton`, `invert_permutation_poly`, `canonical_candidates`, `ring_polynomial_candidate`, `complementary_slice_refine_candidate`, `reduce_univariate_null_polynomial`, `reduce_modular_polynomial`, `reduce_quotient_polynomial_dag`, `polysim_poly_mod2w`.
6. **`norm_nonlinear.ml`** (~800–950 lines):
   - Nonlinear MBA, sparse multilinear `BitTrans` (`PolySim`), complementary-atom pairing, RUMBA null-vector injection & GAMBA factor grouping: `minterm_ring_expansion`, `minterm_ring_poly_candidate`, `polysim_candidate`, `nonlinear_poly_candidate`, `pair_complementary_atoms`, `correlated_null_candidate`, `factor_group_steps`, `factor_group_candidate`, `product_partition_candidate`, `nonlinear_product_identity_candidate`, `complement_product_steps`, `complement_linear_candidate`.
7. **`norm_probes.ml`** (~180–220 lines):
   - Bounded black-box semantic interpolation probes (strictly untrusted candidate generators): `probe_semantic_linear_mba`, `probe_low_width_exact`, `probe_semantic_poly`.
8. **`normalization.ml`** (~400–550 lines):
   - Thin, readable orchestration facade containing ONLY:
     - Clean re-exports of the public `Normalization` functions used by `greysynth.ml`, `egraph.ml`, `synthesis.ml`, and `test/*.ml`
     - `local_candidates`
     - `dag_bottom_up_simplify`
     - `oracle_candidate`
     - `run`

---

## 2. Generality & Hygiene Audit (While Splitting)

- Add a brief 2–4 line module header comment at the top of each new `norm_*.ml` file stating **which general algebraic theory / domain** it implements and confirming that all outputs are untrusted candidates checked by `Rewrite` / `Rewrite_proof`.
- Remove any genuinely unused/dead helper functions surfaced by OCaml compiler warnings (do NOT silence unused-value warnings; keep builds warning-clean!).
- Keep the dependency DAG strictly acyclic (`norm_common` $\to$ `norm_peepholes` / `norm_linear` / `norm_semilinear` / `norm_poly` / `norm_nonlinear` / `norm_probes` $\to$ `normalization`), with **no** duplicate copies of logic across files.
- Do **NOT** weaken any proof gate, parser check, or timeout guard, and do **NOT** change algorithm behavior except removing dead code.

---

## 3. Fast Verification Gate (Target Wall Time: ~4–5 min)

1. **Build & Test (`make test`):**
   - Must compile cleanly (0 new warnings) and pass **100% of all unit & regression tests** (`normalization_test`, `proof_test`, `round23_test` through `round32_test`, etc.).
2. **Parity Check (`--workers 8`, exact R18 config + `mba_equiv` + `mba_proof`, RAM well under 30 GB):**
   - **`datasets/hard_cases/regression_smoke/`** (`62` cases): must match Round 34 (`62/62` established, `0` refuted, `52` exact GT, geomean `<= 0.95x`).
   - **`datasets/hard_cases/core_hard/`** (refreshed `353` non-GB cases): verify `0` refutations, `0` errors, clean execution across all split modules!
3. Record a brief Round-35 modularization note (module line counts + verification results) in `docs/IMPLEMENTATION_RESULTS.md` and commit cleanly (do NOT edit `docs/neon-review*.md`, `docs/LITERATURE_ANALYSIS.md`, or `docs/EXTENDED_AUDIT_WAVE*.md`).
