# MBA simplification improvement plan

This plan turns the post-correctness review into independently testable changes.
The existing rule remains non-negotiable: generated candidates are untrusted and
must pass the shared width, cost, independent-sample, and SMT acceptance policy.
Independent certificate replay remains the final corpus gate.

## Revised execution order

The thematic milestone descriptions below are retained for traceability, but
implementation order has pivoted to avoid a local optimum of ad-hoc Bitwuzla
micro-steps, destructive greedy peepholes, and saturated C-Full/CHS tuning
(see [neon-review-5.md](neon-review-5.md)):

1. **Completed foundation:** backend correctness (Milestone 1), observability
   and quality metrics (Milestone 2), explicit cost models (Milestone 8),
   diversified/one-hot/CEGIS/branch-covering sampling (Milestone 6), reusable
   canonicalized CHS rules (Milestone 5), and shared-subterm proof abstraction.
2. **Completed — Decidable ring proof kernel (Milestone 3A):** a small,
   auditable, formal commutative-ring equality rule (`ring_mod2w`, exact sparse
   polynomial normal form mod $2^w$ over opaque non-ring atoms, with strict
   degree/monomial replay caps) alongside Bitwuzla `"smt"` edges and congruence
   closure in `Rewrite_proof`. Pair it with pure-bitwise minterm expansion so
   64-bit linear, factored, polynomial, and oracle candidates certify in
   milliseconds without monolithic bit-blasting or 50-edge micro-step chains.
3. **Completed core algebraic solvers (Milestone 3B):** native disjoint-minterm
   linear normalization, sparse modular-ring normalization, multiplicative
   factor grouping with recursive cofactor reduction, quadratic null-polynomial
   cleanup, constant-complement canonicalization, scaled-mask merging, and
   bit-sliced recovery now establish all five 100-case MBA suites; baseline
   geometric quality is below 1.00x on each.
4. **Completed — Bounded e-graph unification (Milestone 4A):** unified
   normalization, AC/factoring/polynomial rewrites, OES semantic classes, and
   `Rewrite_proof`'s hash-consed DAG + union-find into a bounded e-graph with
   global cost-model extraction, non-monotonic intermediate alternatives, and
   minimal BFS certificate emission.
5. **Completed — Remaining polish and whole-expression extraction:** completed
   centralized config validation (Milestone 2), generalized null-polynomial &
   Rivest/Hensel inversion (Milestone 3), proof-aware OES & incremental SMT
   reuse (Milestone 4), persisted versioned learned rules (Milestone 5),
   adaptive CHS scheduling & portfolios (Milestone 7), whole-pipeline
   non-monotonic extraction (Milestone 8), and conditional/select/load
   boundaries (Milestone 9). All 72/72 checklist items are complete.

## Baselines and success criteria

The 1,000 C-Full/Tigress-level-5 corpus is a correctness/regression gate, not the
sole quality benchmark: 985 inputs already shrink, seven of the remaining 15 are
minimal under the legacy cost, seven more have cost three, and only one has cost
five. New simplification work must also cover:

- the ProMBA Poly, Non-Poly, QSynth, Loki, and Full-Loki exports;
- C-MBA and C-BeyondMBA under Tigress levels 1 through 8;
- C-MBA under MBA-Obfuscator and OMVLL;
- Xyntia B1, B2, B2-with-constants, complex handlers, and conditionals;
- mixed-width, division/remainder, shift/rotate, polynomial, masked semilinear,
  and sparse-conditional regression suites.

Every benchmark report separates proved, refuted, inconclusive, timeout, and
error outcomes and now computes geometric/arithmetic quality and compression
under all cost models when `--check-ground-truth` is used. Quality runs record
input/output/ground-truth costs, wall time, synthesis
attempts, backend result classes, proof outcomes, and certificate replay.
Dataset-derived output is not committed unless it is a compact summary with
provenance and exact commands.

## Milestone 1: backend contract and operator coverage

- [x] Make the Xyntia grammar configurable and support its `full` grammar.
- [x] Decode every result node the selected Xyntia grammar can emit, including
  width modifiers, shifts, ternary division/remainder, and conditionals.
- [x] Preserve Xyntia's concatenated high/low numerator semantics exactly.
- [x] Remove the duplicate unsound legacy Xyntia converter.
- [x] Add conversion tests for every operator and mixed width.
- [x] Select `mba`, `mba_shift`, `mba_ite`, or `full` dynamically from each
  target's operators instead of paying the full-grammar branching factor universally.
- [x] Make Xyntia use wall-clock deadlines without clobbering `SIGALRM`.
- [x] Align vendored arithmetic shifts and signed remainder-by-zero with the
  total bitvector semantics used by GreySynth.
- [x] Make cvc5's grammar include conditionals and comparisons.
- [x] Add cvc5 division, remainder, and discovered constants.
- [x] Bound backend-requested time by the remaining global budget.
- [x] Enforce process-group deadlines for external tools and classify no-result,
  hard-timeout, process-error, ill-formed, and rejected outcomes separately.

Acceptance: no supported backend result is rejected as an unsupported AST node;
all operator fixtures replay as equivalent; the retained 57-case CHS set has no
conversion errors.

## Milestone 2: honest configuration and observability

- [x] Centralize configuration parsing, defaults, validation, and reporting.
- [x] Implement `balanced_tree` and `sampling_strategy`.
- [x] Include normalization and the selected cost model in pipeline summaries and
  emit all cost models in simplifier/checker/audit reports.
- [x] Reset all metric state for each library/API invocation.
- [x] Populate before/after semantic-class metrics correctly.
- [x] Record backend no-result, timeout, process error, ill-formed result, and
  post-validation rejection separately.
- [x] Split post-validation rejection into width mismatch, not-smaller,
  sample-refuted, SMT-refuted, and SMT-inconclusive outcomes.
- [x] Memoize repeated structural nodes in cost/depth and OES traversals.

Acceptance: changing a reported option changes behavior in a targeted test; two
runs in one process have isolated metrics; reports account for every attempt.

## Milestone 3: deterministic canonicalization and tractable proofs

- [x] Add proof-gated associative/commutative flattening, ordering, balancing,
  constant folding, duplicate elimination, and coefficient collection behind
  `ac_normalization`; keep direct greedy mode opt-in. `normalization_portfolio`
  now races baseline and AC branches from the same input and retains the cheaper
  locally proved result, subject to the shared total budget.
- [x] Complete the mixed-width-safe identity set. Complement, additive inverse,
  disjoint masks, extraction/extension, concat, constant-shift rules, composed
  masks/casts, predicate propagation, and proof-gated branchless select/min/max
  boundary idioms are included.
- [x] Raise the configurable linear-MBA truth-table ceiling from four to six
  atoms by default (up to ten), extend two-value recovery through six atoms,
  and raise the guarded traversal budget; connected-component decomposition remains.
- [x] **Milestone 3A — Decidable `ring_mod2w` proof kernel rule:** add an
  optional `"rule": "ring_mod2w"` justification (defaulting to `"smt"` for full
  v1 compatibility) to `Rewrite_proof` and `mba_proof` that checks exact formal
  commutative-ring equality (`bvadd`, `bvsub`, `bvneg`, `bvmul`, `const`)
  modulo $2^w$ over opaque interned subterms, with strict replay caps
  (`max_degree`, `max_monomials`) and randomized property cross-tests against
  Bitwuzla across 8/16/32/64-bit widths. (Supersedes brittle 50-edge Bitwuzla
  micro-step chains for modular ring arithmetic.)
- [x] Seed at most 12 zero/one/two/fill, negated, complemented, and pairwise-derived
  constants; Xyntia now chooses variable-vs-constant classes 70/30 so added
  terminals do not starve variable mutations.
- [x] Add compositional disjoint-partition polynomial identities, including
  commuted operands/sums and common constant scaling; independently replayed
  Boolean/ring micro-steps raise the audited
  100-case PLDI Poly sample from 31 to 100 strict reductions.
- [x] Decompose constant-scaled complement terms into replayable local algebra
  steps, making the 16-bit constant-offset case reliable at a one-second budget.
- [x] **Milestone 3B.1 — Native linear normalization with disjoint-minterm +
  `ring_mod2w` certification:** supports variable, constant, compound-atom, and
  general `linear_candidates` targets, nonzero offsets, and constant shifts.
  The 100-case PLDI Non-Poly geometric quality moved from **19.2494x to 0.9394x**
  with 100/100 established outputs. Constant-complement canonicalization,
  scaled disjoint-mask merging, and one-variable bit-sliced affine/XOR recovery
  bring the first 100 msimba cases to **0.9966x** quality with 100/100 replay.
  Connected-component scaling and multivariable bit slicing remain follow-up work.
- [x] **Milestone 3B.2 — Native factor grouping and sparse polynomial
  normalization:** combines formal monomials, factors repeated opaque terms,
  recursively reduces linear cofactors, and certifies results with ring edges.
  MBA-Obfuscator nonlinear moved from **11.4734x to 0.8693x** with 100/100
  compositional proofs. A quadratic falling-factorial null rule and formal
  polynomial-composition regressions are included.
- [x] Generalize degree-2..8 univariate null-polynomial recognition through the
  falling-factorial basis and add explicit Rivest classification plus bounded
  Hensel/Newton inverse construction. Candidates are retained only when the
  bounded inverse validates on deterministic modular probes; composition cleanup
  then crosses the same ring/null proof boundary.
- [x] Add two-value affine-Boolean extraction with compact DNF/CNF/ANF recovery
  before falling back to a dense AND-monomial basis. NPN/ESOP tables remain a
  possible performance refinement.
- [x] Normalize after every CHS horizon and before the final OES cleanup.
- [x] Add optional `rumba` and `cobra` CLI adapters for differential testing and
  bounded candidate experiments. They remain disabled by default.
- [x] **Milestone 3B.3 — Certified differential oracles:** propagate oracle
  suppression through recursion, target maximal compatible subtrees top-down,
  clamp deadlines, and certify compatible answers through minterm/ring proofs.
  Native OCaml minterm, sparse-ring, and factor solvers remain primary; external
  implementations are optional comparison tools only.

Acceptance achieved: randomized tests verify `ring_mod2w` against Bitwuzla;
PLDI Non-Poly and MBA-Obfuscator nonlinear reach **0.9394x / 0.8693x** geometric
quality with 100% independent replay. PLDI Poly and QSynth EA remain at
0.8812x / 0.9673x, and C-Full remains 1,000/1,000 established with 984 strict
reductions and 16 unchanged.

## Milestone 4: proof-aware OES and equality search

- [x] Keep a bounded Pareto frontier per sampled semantic class instead of only
  the single smallest representative, retaining speculative constants alongside
  real AST representatives.
- [x] Rank representatives by extraction cost and expected proof complexity.
  Equal-cost OES frontier entries prefer bitwise/additive proofs over nonlinear,
  conditional, and division-heavy candidates.
- [x] Canonicalize proof-cache keys symmetrically across equality direction.
- [x] Retry inconclusive obligations only when a larger budget is available.
- [x] Reuse successful and budget-tagged inconclusive producer-side
  compositional endpoint proofs and honor timeout/non-strict policy; independent
  replay deliberately remains cache-free.
- [x] Strengthen proof abstraction to replace maximal cost-2/3 subterms and
  nontrivial constants shared across both sides, while retaining concrete
  fallback when the stronger abstraction is satisfiable.
- [x] Reuse incremental solver contexts where the solver API permits. Managed
  `check_sat_assuming` sessions reset on inconclusive/error outcomes, after a
  bounded eight-query window, and at independent replay and pipeline boundaries.
- [x] Add baseline-vs-AC whole-normalizer portfolio extraction and retain only
  the winning branch's proof obligations (measured 217 improved / 218 regressed
  under shared wall budget; superseded by Milestone 4A e-graph unification).
- [x] **Milestone 4A — Bounded e-graph unifying normalization, OES, and proof
  extraction:** the branch worklist is deleted. The implementation now has
  hash-consed per-eclass enodes, union-find, direct semantic OES merges,
  congruence rebuild, journal-free proof justifications, bounded local-candidate
  saturation, and global bottom-up configured-cost extraction. The 2048-enode /
  4-iteration limits are enforced and large/stalled inputs fall back safely.
  Raw-child-aware congruence nodes, recursive BFS proof-path emission, rebuild
  correctness, fixed-point incremental extraction, materialized parent
  representatives, semantic-failure memoization, bottom-up scheduling,
  cheapest-first candidate verification, and partial-progress extraction are
  implemented; all focused child-class certificates replay. Lexicographic
  `(cost, AST nodes, expression)` extraction eliminates zero-cost Legacy cast
  cycles, and long additive spines skip heavyweight interior-prefix work. The
  2048/4 C-Full gate passes: 1,000/1,000 established, zero process timeouts,
  and 984 strict reductions / 16 unchanged. Bounded repeated-factor exploration,
  pass-family candidate retention, and disjoint-mask bit-sliced proofs close the
  final quality deltas: all five 100-case suites establish every output and
  match or beat baseline (0.9290x Non-Poly, 0.7595x nonlinear, 0.8789x Poly,
  0.8443x QSynth EA, and 0.9966409x msimba). The mode remains explicitly opt-in
  to avoid silently changing existing deployments.

Acceptance: a targeted test demonstrates fallback from an unprovable smallest
representative to a proved runner-up and non-monotonic expansion->cancellation
without local regressions; C-Full achieves >= 984/1,000 strict reductions with
AC enabled and zero destructive phase-ordering regressions.

## Milestone 5: reusable CHS rules

- [x] After contextual synthesis, prove the Greek-variable template with
  independent typed variables under a bounded budget.
- [x] Store proved universal templates in a per-run structural rule cache and
  apply them across concrete contexts without another backend call.
- [x] Keep dependency-specific templates local when generalization is refuted or
  inconclusive.
- [x] Persist/version generalized learned-rule proofs independently; every
  loaded `greysynth.learned-rules.v1` certificate is independently re-verified,
  and every concrete application remains re-proved and recorded for replay.
- [x] Canonicalize learned templates across alpha-renaming, commutative order,
  and associative balancing; mixed operator profiles use bounded generic proofs.
  Persisted cross-run rule libraries are supported via `learned_rules_file`
  with independent certificate re-verification on load.

Acceptance: a synthesized rule such as `(A|B)+(A&B) -> A+B` is synthesized and
proved once, then reused for distinct operands with no additional synthesis.

## Milestone 6: samples and counterexample-guided refinement

- [x] Represent retained SMT counterexamples and synthesized retry samples as
  explicit per-variable environments.
- [x] Add explicit-environment evaluation and zero/all-one/every-one-hot tuples
  for independent label sampling, as required by XSmir affine rules.
- [x] Extend default `RealValues` contextual banks with deterministic variable
  tuples, extrema, rank/seed-diversified one-hot/one-cold bits, low masks,
  rotating patterns, and a reproducibly seeded random/small-value tail. Training
  and holdout tails no longer collapse onto diagonal `x = y = ...` rows.
  alternating masks, byte/word boundaries, carry boundaries, large shifts,
  divisors, and correlated variable assignments.
- [x] Keep independently seeded structured training and validation banks.
- [x] On SMT refutation, retain the concrete model, turn it into contextual
  cut-label values, and retry within the configured `cegis_retries` bound.
- [x] Add feasible branch-covering SMT models for up to four restored ITE
  conditions per synthesis target; point-function-specific predicates remain.

Acceptance: known sparse-mask and large-shift candidates are rejected by the
training bank or corrected by CEGIS before final acceptance; runs are reproducible
from a recorded seed and explicit sample manifest.

## Milestone 7: adaptive synthesis scheduling

- [x] Bound each backend call by the remaining global deadline; Xyntia uses wall
  time internally and external tools run under a hard process-group deadline.
- [x] Start with short probes and escalate promising node/horizon pairs.
- [x] Rank work by possible cost reduction, cut-label count, repeated semantic
  classes, constants, operator family, and adjacent-horizon history.
- [x] Skip targets whose lower bound cannot beat the incumbent.
- [x] Add optional label and horizon caps with explicit skip reporting.
- [x] Permit an adaptive backend portfolio for hard targets.
- [x] Preserve completed proved rewrites across every timeout boundary.
- [x] Restart small CHS horizons after child reductions expose a shallower rule.
- [x] Avoid caching partial-timeout CHS results and bound relational inversion
  traversal by `local_extend_depth`.

Acceptance: accepted reductions are no worse and backend time/attempt counts fall
on the 57-case CHS set and C-Full level-5.

## Milestone 8: explicit cost models

- [x] Preserve `legacy` cost for historical comparisons.
- [x] Add `paper_ast`, counting width conversions as AST operators.
- [x] Add instruction-oriented and readability-oriented cost models.
- [x] Report all stable costs while selecting with one explicit configured model.
- [x] Use whole-expression extraction for alternatives rather than requiring
  every useful intermediate form to be locally cheaper. Bounded AC,
  multiply/shift/add bridges, and small distributive/negation expansions are
  retained per e-class and selected only when they reduce configured
  whole-expression cost; post-CHS cleanup uses the same proof-bearing e-graph.

Acceptance: reports identify the selection metric; cast-heavy outputs cannot
claim paper-AST improvements merely because casts are free in the legacy metric.

## Milestone 9: conditionals and wider semantics

- [x] Simplify ITE conditions and branches independently and expose typed ITEs
  to contextual synthesis instead of making the entire node opaque.
- [x] Cover both feasible sides of restored conditions before conditional
  synthesis. Mixed conditional+shift/division targets retain all operators
  through Xyntia's `full_ite` grammar.
- [x] Add predicate extraction and proved select/min/max idioms.
- [x] Keep memory loads and C/binary lifting outside the pure-expression proof
  claim until their semantics are modeled independently. Loads now produce an
  explicit `outside_proof_semantics` report and no rewrite certificate.

## Validation cadence

For each milestone:

1. Run `make test` in the Dev Container.
2. Run focused operator/property tests with the SMT solver required.
3. Run a small deterministic smoke set before long corpora.
4. Run affected full datasets with process limits and resumable JSONL output.
5. Replay every selected certificate independently.
6. Compare against the last committed summary; never classify `ukn` as success.
7. Commit code, tests, and concise documentation atomically.

## External framework notes

`../CoBRA` provides the broadest deterministic candidate pipeline (linear,
semilinear, polynomial, decomposition, and lifting) and extensive datasets.
`../binsnake-cobra` offers a Rust/Python interface and useful mixed-width design
work. `../rumba` is a fast linear/nonlinear MBA candidate generator with C and
Python bindings. The first integration should be an optional line-oriented
subprocess backend so GreySynth does not acquire build-time language/toolchain
coupling. Exact source revision, license, command, bit width, and parser mapping
must be recorded in benchmark metadata.
