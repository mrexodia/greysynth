# Native MBA integration direction

The optional Rumba/CoBRA CLI adapters validated candidate quality, but they are
not the intended primary architecture. GreySynth will implement the relevant
algorithms natively in OCaml and retain external tools only as optional
comparison/differential-testing oracles.

## Why native integration

- Native candidates use GreySynth's typed mixed-width AST directly.
- Candidate generation participates in configured cost models and CHS/OES.
- Every transformation can emit small obligations into `Rewrite_proof` and be
  replayed independently by `mba_proof`.
- There is no subprocess/parser overhead or separate runtime dependency.
- Contextual cut-leaf relationships remain available.
- Ideas and published algorithms can be reimplemented independently; source
  code must not be copied without preserving and reviewing its license and
  attribution requirements. Rumba is MIT and CoBRA is Apache-2.0, but the
  safest project policy is an original implementation informed by papers,
  public behavior, and differential tests.

## Immediate high-impact native passes

### 1. Compositional disjoint-minterm linear-MBA proofs

`linear_candidates` already discovers compact candidates, but wide expressions
with several constant multipliers still reach a monolithic SMT query. Add a
proof builder that:

1. Normalizes subtraction and unary negation into signed additive terms.
2. Expands each bitwise term over the shared atoms into a sum of disjoint
   Boolean minterms.
3. Emits each bitwise-to-minterm equality as a small local obligation.
4. Applies distributivity one binary step at a time.
5. Regroups terms by minterm using additive AC obligations.
6. Accumulates two coefficients at a time, constant-folding between steps.
7. Expands the compact candidate to the same canonical minterm sum.

No n-ary factoring obligation should be emitted. Every local step must fit the
short proof budget and replay through existing congruence closure.

Primary acceptance targets:

- `nonpoly_L2_inner` and `nonpoly_L58_inner` reduce to their one-node targets.
- The corresponding outer PLDI Non-Poly cases expose and collapse the existing
  product-partition identity.
- Fresh `mba_proof` replay succeeds with a one-second per-edge schedule.
- Re-audit the first 100 PLDI Non-Poly cases and report ground-truth quality.

### 2. Binary multiplicative factor grouping

For additive sums of products:

1. Flatten signed additive terms.
2. Normalize multiplication association and commutative order.
3. Select a repeated nonconstant factor appearing in at least two terms.
4. Move matching terms adjacent with one additive AC obligation.
5. Factor exactly two terms at a time:
   `(a*f) + (b*f) = (a+b)*f`.
6. Recursively simplify the cofactor through the compositional linear-MBA pass.
7. Repeat while extraction cost decreases.

Primary acceptance targets:

- `poly_mba_cancel` reaches its size-11 target family.
- MBA-Obfuscator nonlinear quality improves materially from 11.47x.
- Every accepted result remains proved against the original input; supplied
  ground truths are used only for quality measurement.

## Later native techniques inspired by the frameworks

- Coefficient-basis butterfly transforms and sparse ANF/ESOP reconstruction.
- Connected-component decomposition and auxiliary-variable elimination.
- Bit-partitioned semilinear mask reconstruction.
- Sparse modular polynomial normalization and permutation-polynomial inversion.
- A bounded worklist/competition-group extractor rather than greedy local
  commitment.

These should be introduced only with focused regressions and corpus-level
quality measurements. The external adapters remain disabled by default and may
be removed from production configuration after native parity is demonstrated.
