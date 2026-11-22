# MBA simplification improvement plan

This plan turns the post-correctness review into independently testable changes.
The existing rule remains non-negotiable: generated candidates are untrusted and
must pass the shared width, cost, independent-sample, and SMT acceptance policy.
Independent certificate replay remains the final corpus gate.

## Revised execution order

The thematic milestone descriptions below are retained for traceability, but
implementation order is now: backend correctness, observability, explicit cost
models, structured/one-hot samples, deterministic normalization plus decomposed
proofs, proof-aware OES, reusable CHS rules, and adaptive scheduling. Cost
models move ahead of new simplifiers so cast-heavy legacy-cost artifacts do not
steer development. Structured samples move ahead of XSmir escalation because
its affine rules require zero, all-one, and every one-hot input tuple.

The review in [neon-review.md](neon-review.md) also adds a proof requirement:
wide linear, quadratic, and polynomial candidates must be emitted as replayable
micro-steps whenever a monolithic 64-bit proof is predictably intractable.

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

Every benchmark report must separate proved, refuted, inconclusive, timeout, and
error outcomes. Quality runs record input/output costs, wall time, synthesis
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
- [ ] Enforce process-group deadlines for external tools and classify failures
  instead of flattening them to `None`.

Acceptance: no supported backend result is rejected as an unsupported AST node;
all operator fixtures replay as equivalent; the retained 57-case CHS set has no
conversion errors.

## Milestone 2: honest configuration and observability

- [ ] Centralize configuration parsing, defaults, validation, and reporting.
- [x] Implement `balanced_tree` and `sampling_strategy`.
- [ ] Include normalization and the selected cost model in the pipeline summary.
- [x] Reset all metric state for each library/API invocation.
- [x] Populate before/after semantic-class metrics correctly.
- [ ] Record no-result, timeout, unsupported-result, ill-formed-result,
  not-smaller, sample-refuted, SMT-refuted, and SMT-inconclusive separately.
- [x] Memoize repeated structural nodes in cost/depth and OES traversals.

Acceptance: changing a reported option changes behavior in a targeted test; two
runs in one process have isolated metrics; reports account for every attempt.

## Milestone 3: deterministic canonicalization and tractable proofs

- [x] Add proof-gated associative/commutative flattening, ordering, balancing,
  constant folding, duplicate elimination, and coefficient collection behind
  `ac_normalization`; keep direct greedy mode opt-in. `normalization_portfolio`
  now races baseline and AC branches from the same input and retains the cheaper
  locally proved result, subject to the shared total budget.
- [ ] Add complement, mask, extraction/extension, concat, shift, and comparison
  identities without crossing mixed-width boundaries unsafely.
- [ ] Raise the linear-MBA atom ceiling using sparse truth tables and component
  decomposition rather than dense enumeration alone.
- [ ] Normalize sparse modular polynomials and factor only when extraction cost
  improves.
- [ ] Add semilinear mask reconstruction and bit-partitioned simplification.
- [x] Seed bounded zero/one/two/fill, negated, complemented, and pairwise-derived
  constants in synthesis grammars.
- [x] Add the first compositional disjoint-partition polynomial identity, with
  ten independently replayed Boolean/ring micro-steps; it raises the audited
  100-case PLDI Poly sample from 31 to 100 strict reductions.
- [ ] Generalize decomposed certificates to arbitrary minterm polynomials, AC
  cancellation, and permutation-polynomial inversion so producer and replay do
  not depend on monolithic bit-blasted queries.
- [x] Add two-value affine-Boolean extraction with compact DNF/CNF/ANF recovery
  before falling back to a dense AND-monomial basis. NPN/ESOP tables remain a
  possible performance refinement.
- [x] Normalize after every CHS horizon and before the final OES cleanup.
- [ ] Allow CoBRA, binsnake-cobra, Rumba, or GAMBA as optional local-subtree
  candidate generators through a documented subprocess protocol. Their answers
  remain untrusted and proof-gated. Do not copy incompatibly licensed code.

Acceptance: property tests prove all committed rewrites; Poly, Non-Poly,
MBA-Obfuscator, masked, and mixed-width suites improve without a regression on
C-Full.

## Milestone 4: proof-aware OES and equality search

- [x] Keep a bounded Pareto frontier per sampled semantic class instead of only
  the single smallest representative, retaining speculative constants alongside
  real AST representatives.
- [ ] Rank representatives by extraction cost and expected proof complexity.
- [ ] Canonicalize proof-cache keys.
- [x] Retry inconclusive obligations only when a larger budget is available.
- [ ] Reuse generalized proofs and solver contexts where the solver API permits.
- [ ] Prototype a bounded equality beam/e-graph so equal-cost canonical forms
  can expose a lower-cost parent without creating rewrite cycles.

Acceptance: a targeted test demonstrates fallback from an unprovable smallest
representative to a proved runner-up; proof calls and inconclusive rates decrease
on the 1,000-case corpus.

## Milestone 5: reusable CHS rules

- [ ] After contextual synthesis, try proving the Greek-variable template with
  independent typed variables.
- [ ] Store proved universal templates in a structural rule cache and apply them
  across concrete contexts.
- [ ] Keep dependency-specific templates local when generalization is refuted or
  inconclusive.
- [ ] Version and replay learned-rule proofs independently.
- [ ] Canonicalize truncated ASTs so alpha-renaming and commutative ordering do
  not prevent reuse.

Acceptance: a synthesized rule such as `(A|B)+(A&B) -> A+B` is synthesized and
proved once, then reused for distinct operands with no additional synthesis.

## Milestone 6: samples and counterexample-guided refinement

- [ ] Represent samples as explicit per-variable environments.
- [x] Add explicit-environment evaluation and zero/all-one/every-one-hot tuples
  for independent label sampling, as required by XSmir affine rules.
- [ ] Extend deterministic contextual strata with extrema, one-hot/one-cold bit
  values, powers of two,
  alternating masks, byte/word boundaries, carry boundaries, large shifts,
  divisors, and correlated variable assignments.
- [ ] Keep independent training and validation banks.
- [ ] On SMT refutation, add the model to the synthesis bank and retry within a
  bounded CEGIS loop.
- [ ] Add branch-covering SMT samples for sparse conditionals and point functions.

Acceptance: known sparse-mask and large-shift candidates are rejected by the
training bank or corrected by CEGIS before final acceptance; runs are reproducible
from a recorded seed and explicit sample manifest.

## Milestone 7: adaptive synthesis scheduling

- [ ] Bound each backend call by the remaining global deadline. Xyntia now uses
  wall time internally; the caller still needs to pass the smaller remaining budget.
- [ ] Start with short probes and escalate promising node/horizon pairs.
- [ ] Rank work by possible cost reduction, cut-label count, repeated semantic
  classes, constants, operator family, and adjacent-horizon history.
- [ ] Skip targets whose lower bound cannot beat the incumbent.
- [ ] Cap labels/horizons and permit a backend portfolio for hard targets.
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
- [ ] Use whole-expression extraction for alternatives rather than requiring
  every useful intermediate form to be locally cheaper.

Acceptance: reports identify the selection metric; cast-heavy outputs cannot
claim paper-AST improvements merely because casts are free in the legacy metric.

## Milestone 9: conditionals and wider semantics

- [x] Simplify ITE conditions and branches independently and expose typed ITEs
  to contextual synthesis instead of making the entire node opaque.
- [ ] Restrict conditional synthesis to branch-covering samples.
- [ ] Add predicate extraction and proved select/min/max idioms.
- [ ] Keep memory loads and C/binary lifting outside the pure-expression proof
  claim until their semantics are modeled independently.

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
