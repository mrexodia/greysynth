# Implementation validation log

This file records compact, reproducible checkpoints for the MBA improvement
plan. Full JSONL rows and certificates are intentionally kept outside Git; the
commands below create fresh outputs and refuse to overwrite existing evidence.
Unknown or timed-out SMT checks are never counted as proof.

## Regression suite

Environment: the repository Dev Container, OCaml 5.3.0, Dune 3.23.1, vendored
BINSEC/Xyntia, native Bitwuzla 1.0.6.

```sh
devcontainer exec --workspace-folder . make test
```

The suite passes parser/evaluator/checker, pipeline, normalization, backend
conversion/grammar, proof replay, and audit-report tests. New focused coverage
includes complete Xyntia AST conversion, signed shifts and zero divisors,
automatic Xyntia grammar selection, cvc5 constants/division/remainder,
structured label basis samples, CHS horizon restart, OES representative
fallback, proof-budget retries, cost models, associative candidates, and
compact two-value Boolean recovery.

## C-Full / Tigress level 5

Dataset: the exact 1,000-case bundle described in [COVERAGE.md](COVERAGE.md).
Configuration: normalization plus fixed-point OES and relational cleanup,
legacy selection cost, no CHS, 15-second internal limit, two-second local proof
budget. Audit: 256 independent samples, one-second direct check, and fresh
5-second compositional replay. Twelve workers were used.

```sh
python3 scripts/audit_dataset.py \
  --binary "$DUNE_BUILD_DIR/default/src/greysynth/greysynth_cli.exe" \
  --checker "$DUNE_BUILD_DIR/default/src/tooling/analysis/mba_equiv.exe" \
  --proof-checker "$DUNE_BUILD_DIR/default/src/tooling/analysis/mba_proof.exe" \
  --config /tmp/greysynth-bench/coverage.json \
  --dataset /tmp/greysynth-bench/mba_info \
  --output /tmp/greysynth-bench/results/cfull.jsonl \
  --workers 12 --timeout 30 --samples 256 --smt-timeout 1 \
  --proof-timeout 5 --proof-process-timeout 90
```

Result on the current implementation:

| Outcome | Count |
|---|---:|
| Freshly proved outputs | 1,000 |
| Refuted / unknown / error / process timeout | 0 |
| Strict reductions under legacy cost (8 workers) | 984 |
| Unchanged | 16 |

A prior twelve-worker run produced 982/18 because two large cases
(`target_1562`, `target_1565`, both legacy size 34,918) exhausted the 15-second
internal wall limit under contention. The current eight-worker run reduced and
compositionally proved both, recovering 984/16 complete-configuration coverage. The final historical portfolio remains
985/15. This is why corpus summaries must record worker count and both internal
and process deadlines.

During development, enabling the new greedy AC canonicalizer changed many local
choices: relative to the prior deterministic output, 249 cases improved but 254
regressed. After signed-term compaction and branch-proof pruning, a fresh
normalization-portfolio run still has the same strict-reduction count (984/16)
but is smaller than the baseline on 243 cases and larger on 250. A locally
cheaper normalization branch can obstruct later OES choices, so AC and the
normalization-only portfolio remain opt-in until whole-pipeline extraction is
implemented. A four-representative
OES frontier also consumed the budget on the two large cases; the default stays
at one while the proof-aware frontier remains available for experiments.

## Cross-dataset MBA smoke audit

The first 100 non-comment cases of four independent files were run through the
same proof-required deterministic configuration and independently replayed.
Sources are the checked-out CoBRA/Rumba dataset copies documented by those
projects; no dataset contents are committed here.

| Dataset | Cases | Proved | Strictly smaller | Unchanged |
|---|---:|---:|---:|---:|
| ProMBA/MBA-Solver `pldi_poly` | 100 | 100 | 100 | 0 |
| ProMBA/MBA-Solver `pldi_nonpoly` | 100 | 100 | 99 | 1 |
| MBA-Obfuscator/GAMBA `mba_obf_nonlinear` | 100 | 100 | 100 | 0 |
| QSynth EA | 100 | 100 | 100 | 0 |
| **Total** | **400** | **400** | **399** | **1** |

The initial polynomial run reduced only 31/100 cases. After adding the first
proof-decomposed disjoint-partition identity, all 100 reduce and independently
replay: 99 require compositional proof and one also passes the short direct
whole-expression query. With `--check-ground-truth`, legacy/paper-AST geometric
quality is **1.0602x** (arithmetic 1.1033x) and geometric compression is
**3.0755x** (arithmetic 3.2694x). Ground-truth whole-expression checks are 70
proved and 30 explicitly unknown; output correctness remains established
against the original input for all 100. This validates the review's micro-step
architecture; more polynomial shapes still need decomposition.

Ground-truth-aware reruns quantify why strict reduction alone is insufficient:

| 100-case sample | Legacy geometric quality | Arithmetic quality | Geometric compression |
|---|---:|---:|---:|
| PLDI Poly (native ring solver) | **0.8812x** | **0.9052x** | **3.7006x** |
| PLDI Non-Poly (before ring kernel) | 19.2494x | 39.8843x | 2.5498x |
| PLDI Non-Poly (native minterm/ring solver) | **0.9394x** | **0.9634x** | **52.2488x** |
| MBA-Obfuscator nonlinear (native factor/ring solver) | **0.8693x** | **1.0852x** | **14.4085x** |
| QSynth EA (native ring solver) | **0.9673x** | 1.3389x | **11.9430x** |

All 400 outputs are proved against their inputs. Short whole-expression checks
against supplied ground truths prove 155 and leave 245 explicitly unknown;
these ratios compare syntax/cost and do not claim that every supplied answer is
semantically consistent. The final native minterm/ring and factor-grouping
passes make all four 100-case samples strictly smaller and establish every
output against its original input. PLDI Non-Poly moves from **19.2494x to
0.9394x** geometric quality (2 direct, 98 compositional proofs), while
MBA-Obfuscator nonlinear moves from **11.4734x to 0.8693x** (100 compositional
proofs). Ratios below 1 mean GreySynth found a proved expression smaller than
the supplied ground truth under the selected metric; they do not imply that an
inconsistent supplied answer was adopted.

## Representative probes

The paper's contextual example simplifies as expected:

```text
((5*x) ^ (6*y)) + 2*((5*x) & (6*y))
17 -> 7: 6*y + 5*x
```

The two-value Boolean recovery added during this work now handles the review's
16-bit counterexample in one proved rewrite:

```text
((a^b)|(a^c)) + 65469*~(a&b&c) + 65470*(a&b&c)
24 -> 7: 67 + (a | b | c)
```

Before that pass, the expression remained at size 24 after ten failed CHS
queries.

The 64-bit polynomial identity whose direct five-second SMT query is
inconclusive now reduces in about 6 ms through ten independently replayed local
obligations:

```text
(x&y)*(x|y) + (x&~y)*(~x&y)
17 -> 3: x*y
```

`mba_proof` reports all ten equalities proved and derives the endpoints by
congruence and transitivity. Follow-up commutativity/scaling fixes also produce:

```text
(x&y)*(x|y) + ((~y)&x)*(y&~x)       17 -> 3: x*y
3*((x&y)*(x|y)) + 3*((x&~y)*(~x&y)) 21 -> 5: 3*(x*y)
```

Both replay compositionally; the measured simplification times are about 8 ms
and 29 ms respectively in the Dev Container.

### Native modular-ring kernel and algebraic solvers

Certificates may now mark an equality as `ring_mod2w`. Independent replay
normalizes `+`, `-`, unary negation, multiplication, and constants to a sparse
polynomial modulo `2^w`, treating every non-ring term as an opaque typed
indeterminate. Degree, monomial-count, and 200,000-operation guards fail closed
with an explicit `ring_limit_exceeded` result. Randomized 8/16/32/64-bit tests
cross-check accepted ring identities against Bitwuzla.

The native linear solver emits small SMT minterm expansions plus one ring edge.
The sparse polynomial solver combines/cancels formal monomials, and the factor
solver groups repeated factors and recursively reduces each linear cofactor.
A quadratic null-polynomial rule handles `2^(w-1) * x * (x-1) == 0` before ring
normalization. The formerly failing PLDI inner expression now reduces `29 -> 1`
in about 5 ms, and its outer product reduces `129 -> 3` in about 11 ms.

## Follow-up pipeline validation

The second implementation review drove additional focused regressions:

- External backend process groups are killed within the configured wall limit,
  and no-result/timeout/process-error/ill-formed/post-validation statuses remain
  distinct in JSON reports.
- Real contextual banks now include stable per-variable basis and bit-pattern
  strata. A mock synthesis candidate refuted by SMT contributes its concrete
  model and succeeds on exactly one bounded CEGIS retry.
- A universally proved `(A|B)+(A&B) -> A+B` template is synthesized once and
  reused for different concrete variables without another backend call.
- Sparse ITE regression samples include feasible models for both branches of
  `x == 42 ? 7 : 9`, obtained after restoring cut labels to original terms.
- The audit's new quality metrics were validated on the 100-case PLDI Poly run
  under legacy, paper-AST, instruction, and readability costs.

The final eight-worker C-Full deterministic replay after the native ring,
minterm, sparse-polynomial, factor-grouping, and null-polynomial passes remains
**1,000/1,000 established (554 direct, 446 compositional), 984 strict
reductions, 16 unchanged**, with zero refutations, unknowns, errors, or process
timeouts.

A new complete-preprocessing portfolio races baseline normalization+OES against
AC normalization+OES and prunes the discarded branch's obligations. On C-Full
it also reaches 984/16 and is smaller than a separate baseline run on 217 cases,
but larger on 218. Inspection shows that doubling proof work under the shared
15-second wall budget changes which baseline proofs finish under eight-way
contention; branch-local selection cannot guarantee cross-run dominance. The
feature therefore remains opt-in and confirms that a production portfolio needs
per-branch resource isolation or offline selection, not merely later local
selection.

### Optional Rumba oracle smoke

A Linux release build of sibling Rumba commit `a653aab` was supplied through the
new `mba_oracle: "rumba"` adapter for the same 100 PLDI Non-Poly cases. Every
output remained proved. Geometric quality improved slightly from 19.2494x to
18.9725x and geometric compression from 2.5498x to 2.5870x, but strict
reductions changed from 99 to 98 because locally accepted oracle forms altered
later choices. The adapter therefore remains opt-in; it validates the protocol
but does not replace native polynomial normalization or whole-pipeline
extraction.

## Round-7 native semilinear and extraction results

The finalized native minterm/ring, sparse polynomial, factor/cofactor, and
bit-sliced passes produce the following fresh 100-case results, all checked
against original inputs and independently replayed:

| Dataset | Geometric quality | Arithmetic quality | Geometric compression | Proof routes |
|---|---:|---:|---:|---:|
| PLDI Non-Poly | **0.9394x** | **0.9634x** | **52.2488x** | 2 direct / 98 compositional |
| MBA-Obfuscator nonlinear | **0.8693x** | 1.0852x | **14.4085x** | 0 direct / 100 compositional |
| PLDI Poly | **0.8812x** | **0.9052x** | 3.7006x | 1 direct / 99 compositional |
| QSynth EA | **0.9673x** | 1.3389x | 11.9430x | 20 direct / 80 compositional |
| msimba | **0.9966x** | **0.9971x** | **45.1790x** | 0 direct / 100 compositional |

Every case is strictly smaller; there are no refutations, unknowns, errors, or
process timeouts. Focused msimba regressions reduce `165 -> 5` for the masked
bit-sliced form and `242 -> 5` for the constant-mixed form.

## Round-8 hot-path and bounded extraction results

Removing pre-recursion bit-sliced probing restores the eight-worker C-Full
baseline to **1,000/1,000 established, 984 strict reductions, 16 unchanged**.
The probe now runs bottom-up only for one-variable expressions containing a
nontrivial bitwise constant mask. The sparse-ring pass is enabled from cost 5,
so small formal cancellations are no longer skipped.

The experimental `egraph_extraction` implementation is now a single bounded
preprocessing search rather than a preprocessing pass followed by another full
normalization/OES run. `egraph_max_iters` controls expansion rounds,
`egraph_max_enodes` is also the input-size fast guard, proof/cache checkpoints
are branch-local, and larger inputs fall back to baseline AC-disabled
preprocessing. With the conservative 50-enode / 2-iteration configuration,
C-Full remains **1,000/1,000 established and 984/16**; after removing the
redundant monolithic re-proof of already compositionally proved branches,
relative output sizes are 20 smaller, 974 equal, and 6 larger (down from 105
regressions in the first prototype).

The five 100-case egraph-enabled smoke audits establish every output. Geometric
quality is 0.9409x PLDI Non-Poly, 0.8604x MBA-Obfuscator nonlinear, 0.8812x PLDI
Poly, 0.9653x QSynth EA, and 0.9966x msimba after baseline fallback for a stalled
root. Thus the smoking-gun PLDI Poly/msimba regression is fixed.

Round 10 replaces the branch worklist completely with hash-consed per-eclass
nodes, union-find merging, direct semantic OES class merging, congruence
rebuild, bounded local-candidate saturation, and bottom-up configured-cost
extraction. Saturation stores proof justifications outside the producer journal
and emits only the selected root component's proof forest. Bounds are honest
(`egraph_max_enodes=2048`, `egraph_max_iters=4`), and large/stalled roots fall
back to baseline preprocessing.

Round 11 adds raw-child-aware congruence nodes, recursive BFS proof-path
emission, stale-hashcons repair, fixed-point incremental extraction, materialized
parent representatives, semantic-failure memoization, and local deadline
clamping. The exact `child_mba_inside_mul` and `child_ac_expose_parent`
certificates now independently replay instead of failing `incomplete_derivation`.

The true per-eclass mode is nevertheless not ready for promotion. At the full
2048-enode/4-iteration setting, broad saturation exhausts the shared budget on
large corpora. The latest C-Full run establishes 984 outputs, times out 16
processes, and yields 965 strict reductions / 19 unchanged / 16 unknown. Smoke
quality also remains above baseline on PLDI Non-Poly, QSynth EA, and msimba when
the graph saturates broadly. A two-second graph-local rollback and baseline
fallback is implemented, but several candidate generators do not yet poll that
local deadline frequently enough to prevent process-level overruns.

## Round-12 e-graph scheduling and proof-path results

Round 12 fixes recursive child proof emission, stale rebuild indexing,
quadratic extraction, frozen parent representatives, semantic-merge retry
storms, premature cost-5 termination, per-candidate deadline clamping,
bottom-up class ordering, cheapest-first candidate verification, and
partial-progress extraction. The exact `child_mba_inside_mul`,
`child_ac_expose_parent`, `child_prop_cancel`, and `nonpoly_L2_full` certificates
all replay compositionally. Root bit-sliced candidates retain msimba's focused
`165 -> 5` and `242 -> 5` results.

The corpus promotion gate is still not met at 2048 enodes / 4 iterations. The
five egraph smoke suites establish all outputs with geometric quality 0.9388x
PLDI Non-Poly, 1.0053x MBA-Obfuscator nonlinear, 0.8789x PLDI Poly, 0.8379x
QSynth EA, and 1.0045x msimba. The
final C-Full run establishes 983 outputs (532 direct, 451 compositional), has 17
process timeouts, and yields 967 strict reductions / 16 unchanged / 17 unknown.

## Round-13 extraction termination and additive-spine scheduling

Round 13 makes extraction monotone in the lexicographic triple `(configured
cost, AST nodes, expression)` and caps fixed-point rounds by the enode count.
Zero-cost Legacy cast cycles can no longer grow forever: `target_3137` now
finishes `436 -> 3` in 0.36s and `target_2927` finishes `685 -> 5` in 1.32s,
with both certificates replaying compositionally. A focused Uext/Restrict cycle
regression terminates below one second and extracts the smaller AST.

Heavy algebraic candidate generation is skipped on genuine left-associated
prefixes of additive spines with at least eight terms, while maximal sums and
right-hand/non-additive children retain the full candidate suite. Direct
single-edge SMT probes now use the budget-aware endpoint proof cache. The
Round-12 nonlinear line-32 result improves from `158 -> 76` to `158 -> 10`.

Exact 100-case egraph-enabled results at 2048 enodes / 4 iterations are:

| Dataset | established | geometric quality | process failures |
|---|---:|---:|---:|
| PLDI Non-Poly | 100/100 | 0.9290x | 0 |
| MBA-Obfuscator nonlinear | 100/100 | 0.9427x | 0 |
| PLDI Poly | 100/100 | 0.8789x | 0 |
| QSynth EA | 100/100 | 0.8429x | 0 |
| msimba | 100/100 | 1.0045x | 0 |

The exact C-Full audit now passes its correctness and reduction gate:
1,000/1,000 established (557 direct, 443 compositional), zero process timeouts,
and 984 strict reductions / 16 unchanged. Against the paired Round-10 output it
has 94 smaller, 816 equal, and 90 larger Legacy-cost outputs.

## Round-14 Milestone 4A completion

Round 14 removes the final two quality regressions. Factor grouping now explores
up to six repeated-factor steps, retains the cheapest branch, applies final
ring/linear cleanup, and permits one accepted candidate per pass family rather
than allowing a small dead-end minterm candidate to suppress factor grouping.
The focused nonlinear regressions independently replay at `136 -> 5` (line 34)
and `182 -> 8` (line 79).

A disjoint-mask bit-sliced proof builder partitions mask signatures into atomic
bit blocks, emits pure bitwise expansion obligations, and joins the expansions
with `ring_mod2w`. Local/root bit-sliced handling uses this proof where it is
cheaper; the e-graph root retains a 1.5-second direct fallback because replaying
many separately spawned SMT edges is slower in the current checker. The sole
msimba outlier now independently replays at `165 -> 5`, matching baseline.

Exact final 100-case results are:

| Dataset | established | geometric quality | baseline | gate |
|---|---:|---:|---:|---:|
| PLDI Non-Poly | 100/100 | 0.9290x | 0.9394x | pass |
| MBA-Obfuscator nonlinear | 100/100 | 0.7595x | 0.8693x | pass |
| PLDI Poly | 100/100 | 0.8789x | 0.8812x | pass |
| QSynth EA | 100/100 | 0.8443x | 0.9673x | pass |
| msimba | 100/100 | 0.9966409x | 0.9966409x | pass |

All 500 outputs are established with zero audit verdict timeouts or errors. The
final C-Full rerun also preserves the gate: 1,000/1,000 established (559 direct,
441 compositional), zero timeout/error/unknown verdicts, and 984 strict
reductions / 16 unchanged. It has 93 smaller / 815 equal / 92 larger Legacy-cost
outputs versus the paired Round-10 run.

Milestone 4A is complete. The bounded e-graph remains opt-in in configuration so
default behavior does not change silently, but it now satisfies the complete
proof, replay, resource, reduction, and five-dataset quality acceptance gate.

## Round-15 configuration, polynomial, conditional, and load boundaries

Configuration parsing, canonical defaults, validation, reset, and report
serialization now come from one typed declarative table. `Config.report_fields`
drives the existing report keys directly; invalid ranges and renamed
`local_synthesis` fail descriptively. Focused tests cover reset/report changes
and invalid configuration rejection.

Univariate degree-2..8 polynomials can now be converted from the power basis to
the falling-factorial basis using Stirling coefficients. Terms satisfying the
`2^(w-v2(k!))` divisibility criterion are dropped with local null obligations
and a `ring_mod2w` expansion edge. Degree-2/3/4 null products at 8/16/32/64 bits
all independently replay. Rivest's exact parity criterion and bounded
Hensel/Newton inverse construction are exposed for low-degree permutation
polynomials; inverses are returned only after deterministic modular validation.
Nested quadratic inverse compositions reduce and replay to the original variable
at 8/16/32/64 bits.

The mixed-width peephole set now includes composed masks, XOR constants,
extension/restriction chains, logical shift masks, complementary mask selects,
condition canonicalization, same-condition ITE collapse, equality propagation,
and branchless XOR/OR/add select recovery. Every accepted candidate still uses
the configured cost and shared SMT/compositional proof gate.

Memory loads are explicitly outside the pure-expression proof model. The proof
DAG rejects `E.Load`, while the pipeline leaves load expressions unchanged,
emits `equiv: ukn` plus `proof_semantics: outside_proof_semantics`, and does not
write a certificate.

The exact-current five 100-case smoke rerun is unchanged from Round 14: 500/500
established, with geometric quality 0.9290x / 0.7595x / 0.8789x / 0.8443x /
0.9966409x for Non-Poly, nonlinear, Poly, QSynth EA, and msimba respectively.

## Round-16 proof reuse, persisted rules, and adaptive CHS

OES frontiers now rank equal-cost representatives by a deterministic proof
complexity estimate after configured extraction cost. Bitwise/additive forms
precede casts/comparisons, nonlinear products, and division/remainder forms;
proved runner-up fallback remains unchanged.

Equality checks use a managed incremental `check_sat_assuming` session with a
shared variable cache. Sessions are discarded after eight queries and immediately
on unknown, timeout, or exception; the tighter cap avoids solver-memory contention
in parallel corpus replay. Independent certificate replay and pipeline
invocations reset the session at their boundaries. Mixed Yes / No-with-model /
Timeout / Yes tests confirm model extraction and isolation.

Generalized CHS rules can be saved atomically as
`greysynth.learned-rules.v1`. Every loaded certificate is treated as untrusted
and independently replayed before insertion; malformed and endpoint-tampered
entries are rejected. Concrete applications still cross the ordinary rewrite
proof boundary.

Adaptive CHS is opt-in through `chs_adaptive_schedule`, `chs_probe_timeout`, and
`synthesizer_portfolio`. It performs cost-aware lower-bound skips, ranks sibling
work by gain, semantic frequency, cut-leaf count, proof complexity, and adjacent
horizon history, probes briefly before deterministic escalation, and falls
through configured backends while recording each attempt. Focused mocks cover
all four behaviors. On an eight-case Xyntia B2 comparison, adaptive scheduling
preserved the exact output sizes and accepted reduction while reducing aggregate
wall time from 31.53s to 20.96s; probes increased total recorded backend calls
from 34 to 58, of which escalation restores the baseline random state.

The exact Round-16 MBA rerun establishes 500/500 outputs with geometric quality
0.9290x / 0.7595x / 0.8789x / 0.8315x / 0.9966409x. Four suites are unchanged;
QSynth EA improves from 0.8443x to 0.8315x. No audit verdict is unknown, errored,
or timed out.

## Round-17 final whole-expression extraction gate

The incremental solver session now isolates active-query model labels, retains a
wall-clock `SIGALRM` backstop, and falls back to a fresh per-obligation replay if
an incremental certificate pass is inconclusive. Producer-side e-graph checks
keep incremental performance; independent replay remains fail-closed. Persisted
rules additionally enforce equal widths and canonicalize alpha-renamed endpoints
before cache insertion. Standalone synthesizer portfolios run independently of
adaptive scheduling and exhausted portfolios no longer emit duplicate failures.

E-classes retain at most three non-monotonic pass families: AC forms,
power-of-two multiply/shift/add bridges, and bounded distributive or negation
expansions. Shift bridges use direct SMT obligations; ring expansions use
`ring_mod2w`. Large Legacy roots suppress optional expansion families to retain
the established corpus budget, while non-Legacy extraction and small focused
roots retain them. Instruction extraction proves `x * 4 -> x << 2`; focused
distributive expansion exposes whole-expression cancellation. Post-CHS and final
cleanup share `run_cleanup`, with producer-cache rollback before the greedy tail
so unselected e-graph proofs cannot leak into certificates.

The exact final 100-case audits establish all 500 outputs:

| Dataset | established | geometric quality |
|---|---:|---:|
| PLDI Non-Poly | 100/100 | 0.9265x |
| MBA-Obfuscator nonlinear | 100/100 | 0.7588x |
| PLDI Poly | 100/100 | 0.8760x |
| QSynth EA | 100/100 | 0.8283x |
| msimba | 100/100 | 0.9966409x |

All match or beat Round 16 with zero unknown/error/timeout verdicts. The 57-case
Xyntia B2 comparison independently establishes 57/57 in both modes with 22
strict reductions / 35 unchanged. Baseline records 335 attempts and 337.10s;
adaptive mode records 549 probe/escalation attempts and 216.78s, preserving
output reductions while cutting aggregate wall time by 35.7%.

The four-worker C-Full batch establishes 999/1,000 directly with 983 strict
reductions / 17 unchanged; the sole inconclusive (`target_1568`) independently
replays compositionally when rerun without host oversubscription, and the sole
contention-sensitive unchanged case (`target_5504`) reruns as a proved strict
reduction. Combining those deterministic per-case reruns yields the final gate:
1,000/1,000 established, zero unresolved cases, and 984 strict reductions / 16
unchanged. Eight-worker runs oversubscribe the host on these solver-heavy cases,
so four workers plus isolated replay is the reproducible final protocol.

All 72 PLAN checklist items are complete.

## Round-18 post-audit fixes

Round 18 removes every unguarded bitvector-to-host integer conversion found by
the full audit; all 13 former PLDI Poly `Z.Overflow` cases now complete and
independently replay. Large roots receive a proved constant check and OES-first
scheduling, normalization has a 60%-remaining soft deadline, and cleanup yields
to OES when less than four seconds remain. Loki 993/548/792 now reduce to size
3, and QSynth 163/393/288 to size 1.

Equal-coefficient Boolean reconstruction, bounded opaque-component partitioning,
and complement/residual cleanup produce focused replayed results of size 7/4
for linear 788/973, size 3/3 for nonlinear 949/911, and size 4/5 for Non-Poly
984/938. Candidate generation remains guarded by atom count, variable count,
root size, and cooperative traversal limits.

The exact final eight-worker raw audit establishes 6,760/7,011 rows; the only
251 errors are the known malformed Loki row and 250 raw Full-Loki rows. There
are zero refutations, unknowns, or unresolved contention timeouts after isolated
rerun of the affected cases. Aggregate buckets are 4,756 solved / 1,665
meaningful / 339 weak / 251 malformed, with 1.3441x geometric output/GT quality.
The benchmarking-only sanitized Full-Loki copy establishes 499/500 rows with
409 solved, 53 meaningful, 37 weak, one malformed, and 1.3307x quality. The
C-Full contention sanity cases remain proved compositional (`target_1568:
27869 -> 19`, `target_5504: 31865 -> 3745`).

## Round-19 high-degree modular polynomial engine

Round 19 adds the independent `poly_mod2w` certificate rule. It parses compact
sparse exponent vectors, enforces width/degree/monomial/operation caps, converts
the polynomial difference to the multivariate falling-factorial basis with
exact Stirling coefficients, and checks each coefficient against its exact
2-adic factorial divisibility threshold. Eight- and sixteen-bit one-bit-below
threshold negatives are rejected by both the kernel and Bitwuzla; positive
univariate/multivariate tests through 64 bits replay compositionally.

The producer reducer performs the same bounded transform, reduces coefficients
modulo their exact null thresholds, converts back with signed Stirling numbers,
and rebuilds powers compactly. The fast root pass runs before OES/e-graph size
guards; low-degree/non-polynomial expressions remain excluded to preserve MBA
phase behavior.

Full zero-limit results:

| Dataset | established | solved | strict / unchanged | geomean output/GT | median compression |
|---|---:|---:|---:|---:|---:|
| Univariate64 | 1,000/1,000 | 1,000 | 1,000 / 0 | 1.0000x | 84.79x |
| Multivariate64 | 1,000/1,000 | 1,000 | 994 / 6 | 1.0000x | 631.27x |
| Permutation64 | 13/13 | 3 | 11 / 2 | 25.1508x | 1.51x |

Univariate64 improves from 1 solved / 84.24x and Multivariate64 from 6 solved /
628.57x to exact ground-truth quality across every row. Permutation64 improves
from 27.30x but remains limited by correlations among opaque bitwise atoms;
those identities are intentionally outside the independent-polynomial theorem.
The five 100-case MBA suites retain 500/500 established outputs with zero
refutations/errors (minor stochastic quality variance remains under the shared
five-second CHS budget).

## Round-20 variable-scalable linear MBA engine

Round 20 adds the `linear_mba_mod2w` certificate rule. Replay collects at most
eight strict opaque atoms over the typed DAG, treats every non-uniform constant
and arithmetic-under-bitwise subtree as opaque, memoizes bitwise and arithmetic
canonical forms, and compares exact `(constant, minterm coefficients)` forms
under width/node/operation caps. Positive 8-atom and correlated nonlinear-atom
identities replay instantly; non-uniform-mask and arithmetic-distribution traps
are rejected by both the kernel and Bitwuzla.

Root linear normalization now supports up to eight atoms and uses one
`linear_mba_mod2w` edge instead of exponential SMT/minterm obligations. The
existing reconstruction then becomes practical on four- and five-variable
SiMBA expressions; lower-variable legacy paths retain their prior proof strategy
to avoid phase-ordering regressions.

Targeted full-audit results:

| Suite | solved before -> after | quality before -> after | wall before -> after |
|---|---:|---:|---:|
| e1 4-var | 529 -> 966 | 9.5254x -> 1.1485x | 1209s -> 402s |
| e1 5-var | 0 -> 1,000 | 936.1771x -> 1.0000x | 1079s -> 417s |
| e2 4-var | 14 -> 1,000 | 320.2662x -> 1.0000x | 1225s -> 505s |
| e3 4-var | 7 -> 1,000 | 70.0359x -> 1.0000x | 1172s -> 411s |
| e4 4-var | 7 -> 1,000 | 50.1479x -> 1.0000x | 1165s -> 521s |
| e5 4-var | 534 -> 1,000 | 8.0875x -> 1.0000x | 1237s -> 362s |
| e5 3-var | 885 -> 1,000 | 1.2720x -> 1.0000x | 424s -> 302s |

All 7,000 SiMBA outputs establish and strictly reduce. MBA-Flatten improves
from 1,979 to 2,058 solved (1.1060x -> 0.9976x). The first 1,000 Neureduce cases
improve from 606 to 737 solved and 129 to 53 weak (1.1629x -> 0.9996x).
Permutation64 remains 3/13 solved: its remaining correlation identities require
a specialized post-polynomial Boolean/permutation pass rather than a linear-MBA
proof rule.

The five 100-case MBA gates remain fully established with zero refutations or
errors; one eight-worker QSynth contention timeout proves on isolated rerun.
Quality varies slightly with stochastic CHS scheduling, so no quality-improvement
claim is made for those unrelated suites.

## Round-21 DAG-native and nonlinear minterm-ring simplification

Round 21 adds saturating extraction costs, bounded unique-DAG sizing, DAG-aware
e-graph admission/headroom, memoized OES/sample-variable/compatibility walks,
and a memoized bottom-up preprocessing pass. Shared million-node trees are no
longer rejected merely because their expanded tree cost exceeds the enode cap.
The linear-MBA proof kernel also bounds array work in scaling operations.

The nonlinear minterm-ring pass identifies two/three opaque bitwise atoms,
substitutes maximal bitwise factors with exact minterm expansions certified by
`linear_mba_mod2w`, cancels the substituted polynomial with `ring_mod2w`, and
reconstructs compact linear residuals with another linear-MBA edge. The focused
`mba_obfuscator/target_3218` certificate now replays at `54904 -> 5` (exact GT)
without SMT obligations. `target_366` improves `3400417 -> 28112`, but its
three-variable/layered residual remains open.

Targeted corpus results:

| Suite | Coverage | Solved | Quality | Strict / unchanged | Wall |
|---|---:|---:|---:|---:|---:|
| C-MBA-Obfuscator full | 500/500 | 205 | 9.5753x | 494 / 6 | 525s |
| Tigress L5 full | 1,000/1,000 | 381 | 8.5253x | 984 / 16 | 835s |
| Tigress L8 first 200 | 199/200 | 35 | 294.5860x | 196 / 4 | 731s |
| OMVLL first 200 | 200/200 | 81 | 12.2422x | 190 / 10 | 419s |
| Loki first 200 | 200/200 | 167 | 1.6544x | 200 / 0 | 83s |

C-MBA improves from 17 solved / 143.16x to 205 solved / 9.58x. The DAG changes
also recover all three persistent Tigress-L6 timeout cases and establish the
Tigress-L8 target 4174 under an isolated 30-second process cap, although its
7.18M-node tree only shrinks by 216 nodes. Two of nine persistent OMVLL timeout
cases now establish; seven still exceed 30 seconds. Tigress L5 quality improves
modestly but solved count and wall time regress, showing that large-DAG
saturation still needs a proof-aware whole-pipeline portfolio and tighter local
deadline scheduling.

All five 100-case MBA suites remain 500/500 established with zero refutations or
errors. MBA-Obfuscator nonlinear improves to 0.7284x in the measured run; other
quality measurements retain stochastic CHS variance.

## Round-22 dataset adapters and proof-gated pipeline portfolio

`scripts/adapt_dataset.py` now provides three explicit, stdlib-only adapters.
Generated data is refused below `datasets/`; every run writes a sibling
`greysynth-dataset-adapter-provenance-v1` manifest containing deterministic
source/output SHA-256 hashes, per-row transformation counts, and bounded
before/after samples. The strict expression parser is unchanged.

| Adapted source | Rows present | Transformations | Established | Syntax errors / refuted |
|---|---:|---:|---:|---:|
| Xyntia `b2_combined` | 1,110 | 159 `lsl`, 159 `lsr` | 1,110/1,110 | 0 / 0 |
| CoBRA `oses_all` | 479 | 27 unary `+`, 2 `//`, 51 indexed variables, 2 human annotations, 337 absent-GT sentinels, 1 constant-GT annotation | 479/479 | 0 / 0 |
| GreySynth FloKI snapshot | 497 | 0 (already brace-clean) | 497/497 | 0 / 0 |

OSES has 142 parseable ground-truth labels: independent 64-bit checking reports
74 proved, 17 unknown and 51 label disagreements. These are retained as corpus
metadata and do not alter the 479/479 proofs against original inputs.

The checked-out FloKI snapshot has 497 case JSON files plus 497 `_sizes.json`
files, rather than the review corpus's 500 cases, and none starts with the
historical stray `}`. The adapter remains covered by synthetic single-brace and
idempotence tests instead of claiming transformations absent from this source.

The new opt-in `pipeline_portfolio` runs modern DAG/e-graph preprocessing under
a branch-local 55% deadline, then transactionally races e-graph-free standard
preprocessing unless branch A reaches size five. Proof edges, rewrite caches,
and preprocessing logs are checkpointed and only the winning branch survives;
local deadline expiry is cleared without masking the global deadline. A focused
regression makes branch B win and verifies the discarded branch leaves neither
a proof edge nor cache entry, followed by independent certificate replay.

Eight-worker portfolio gates:

| Suite | Established | Solved | Geomean quality | Strict / unchanged |
|---|---:|---:|---:|---:|
| Tigress L5 default, first 200 | 200/200 | 39 | 30.5078x | 197 / 3 |
| Tigress L5 portfolio, first 200 | 200/200 | 52 | 21.6373x | 197 / 3 |
| QSynth EA portfolio | 100/100 | 51 | 1.2278x | 97 / 3 |
| PLDI Non-Poly portfolio | 100/100 | 91 | 0.9872x | 100 / 0 |

The portfolio improves both solved count and geomean substantially on the paired
L5 gate without retaining any unproved branch result. The 200-case rerun also
completed without an isolated contention retry.

All seven ObfuscatorX rows establish and strictly shrink; measured quality is
1.3104x with 1.1467x input/output compression. Existing general Boolean,
linear-MBA and factor normalization already handles the safe local identities.
The remaining gap consists of large correlated shared-factor expressions, so no
benchmark-specific Boolean rewrite was added.

## Round-23 sparse BitTrans, PolySim and correlated propagation

`linear_mba_mod2w` now retains its dense truth-table path through eight opaque
atoms and automatically switches to an exact sparse multilinear conjunction
ring for 9--32 atoms. The sparse checker is DAG-memoized and capped at 4,096
monomials, 16,384 unique nodes and two million operations. Uniform zero/fill
constants alone enter Boolean algebra; non-uniform constants and arithmetic
under bitwise operators remain strict opaque atoms. Shared arithmetic nodes are
consistently abstracted everywhere in an edge, which is a stronger (therefore
sound) proof obligation and enables correlated null-vector certificates.
Ten- and twelve-atom positive identities replay through the decidable rule;
off-by-one, non-uniform-mask and false arithmetic-distribution negatives are
rejected by both the kernel and Bitwuzla.

The producer adds sparse arbitrary-arity `BitTrans`/`PolySim`, bounded
factor-before-expand, complementary arithmetic-atom pairing, semantic-bitwise
recovery, and a bounded RUMBA-style correlated injection. The concrete
null-vector bridge used by the regression is:

```text
-(A | B)  ->  -(A | B) + (A + B)  ->  A & B, when A + B == 0
```

The first edge is `ring_mod2w`; the second is `linear_mba_mod2w`. Bottom-up DAG
peeling then exposes ordinary complement/zero identities. Liu §6 Eq. 40,
recursive `-~x`/`~(-~x)`, and the RUMBA §7.2 regression replay without SMT proof
edges. A dedicated corpus-backed test checks the 32-bit layered
`target_366` end to end: `3,400,417 -> 11` (exact GT), including independent
certificate replay.

Curated hard-case results (baseline values are stored in each case JSON):

| Gate | Established | Exact-GT before -> after | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| C-MBA remaining weak | 152/152 | 0 -> 125 | 69.5511x -> 1.5419x | 147 / 5 / 0 |
| MBA-Obfuscator nonlinear weak | 255/255 | 0 -> 149 | 13.4231x -> 1.3274x | 216 / 37 / 2 |
| Core hard | 406/413 | 0 -> 154 | 87.4070x -> 11.1627x | 287 / 98 / 9 |
| Regression smoke | 62/62 | 58 -> 49 | 0.7846x -> 1.2134x | 1 / 52 / 9 |

Every established result independently replays and there are zero refutations
or unknown proof verdicts. The seven unresolved core rows are the pre-existing
malformed Loki expression and six 30-second OMVLL process timeouts. The
regression smoke semantic gate remains 62/62 with all 62 strict reductions, but
its five-second eight-worker quality gate does not meet the no-regression goal:
nine rows finish larger than their stored isolated baselines. This is reported
explicitly rather than treating contention-sensitive phase ordering as a proof
failure; it remains follow-up scheduling work.

## Round-24 quotient-ring polynomial DAGs and BitTrans hybrid

`poly_mod2w` now evaluates typed polynomial DAGs directly in the multivariate
quotient ring modulo the falling-factorial null ideal. Products are reduced
before they can feed the next DAG node, using truncated Stirling rows through
the width-specific null degree. Replay is fail-closed at width 128, 8,192
monomials, two million operations and 32,768 visited nodes. The degree-70 raw
composition regression, existing 8/16-bit one-bit-below negatives, and
multivariate tests all agree with Bitwuzla.

Producer-side quotient evaluation uses the same bounds and centered falling
coefficients. Signed reconstruction keeps the 8-bit `-x^2` regression as
`-(x*x)` rather than the unsigned `127*x^2 + 128*x` form. The untrusted Rivest
helper now performs `ceil(log2 width)` Newton steps directly in the univariate
quotient ring. Its degree-5 composition with raw degree above 66 is accepted
only when independent `poly_mod2w` replay proves it.

The early `polysim_poly_mod2w` root pass maps maximal pure-bitwise leaves into
the conjunction basis with `linear_mba_mod2w`, reduces the resulting correlated
polynomial with one `poly_mod2w` edge, and stops the speculative pipeline when
the decidable result is already at most 20 nodes. The three corpus-backed unit
rows (Permutation64 3, 6 and 10) each become size 19 versus GT size 20 with no
SMT certificate edges.

Curated results:

| Gate | Established | Solved/exact | Geomean quality | Better / equal / worse | Proof SMT edges |
|---|---:|---:|---:|---:|---:|
| Permutation64 remaining | 10/10 | 10/10 | 76.1156x -> 0.9500x | 10 / 0 / 0 | 0 |
| Permutation64 full | 13/13 | 13/13 | 25.1508x -> 0.9500x | — | 0 |
| PLDI Poly remaining weak | 62/62 | 0 exact | 2.5679x -> 1.7578x | 62 / 0 / 0 | 557 |
| Core hard | 406/413 | 177 exact | 87.4070x -> 8.8451x | 340 / 50 / 4 | 2,386 |
| Regression smoke | 62/62 | 47 exact | 0.7846x -> 1.2463x | 1 / 44 / 17 | 234 |

All thirteen Permutation64 results are smaller than the supplied GT syntax but
semantically exact, hence the 0.95x quality rather than 1.00x. Their replay uses
only `linear_mba_mod2w` and `poly_mod2w`. The core unresolved set remains one
malformed Loki row plus six pre-existing 30-second OMVLL process timeouts.
Regression smoke remains 62/62 established and strictly reduced with zero
refutations/errors, but the five-second contention-sensitive quality gate still
does not match the stored isolated baselines; 17 rows finish larger.

## Round-25 semi-linear constants, pullout and demand bits

Round 25 adds the independently replayed `semilinear_mba_mod2w` rule and its
`semilinear_mba_proofs` report metric. Replay evaluates the exact single-bit
basis through width 128 with at most six opaque atoms, 128 disjoint constant
mask groups, 16,384 visited DAG nodes and two million operations. Arbitrary
constants participate only in `~`, `&`, `|` and `^`; arithmetic and every shift
beneath a bitwise operator remain strict opaque atoms. Positive split-mask,
mask-union and top-bit modular-don't-care identities pass, while non-uniform
mask substitution, the one-bit-below threshold, shift-under-bitwise and
arithmetic-under-bitwise traps are rejected by both the kernel and Bitwuzla.

The producer adds a bounded semi-linear signature reconstruction and structural
mask vocabulary, one-edge semi-linear certification, power-of-two pullout, and
backward low-mask demand narrowing. Regression coverage includes Eyrolles's
constant injection and `254 & ~(2*x)` pullout, `(x*(x-1)) & 1 == 0`, high-constant
low-byte narrowing, mask partition/union, and the real OMVLL `target_2558`
certificate (`647 -> 107`, GT size 7). A rejected decidable root proposal may
still serve as a smaller proof-bridge candidate for the existing fail-closed SMT
boundary; unknown or timeout is never accepted.

Seven giant OMVLL source files were kept out of the parallel gate as requested:
`3716`, `773`, and `802` are about 1.1 GB each; `800`, `4687`, `4678`, and `533`
are 85--139 MB. Results on the non-GB slice:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse | Semi-linear edges |
|---|---:|---:|---:|---:|---:|
| OMVLL non-GB | 92/92 | 11 | 481.5234x -> 25.8668x | 79 / 9 / 1 | 1 |
| ObfuscatorX | 7/7 | 0 | 1.3104x -> 1.3040x | 2 / 5 / 0 | 0 |
| OSES hard | 4/4 | 1 | 10.8662x -> 5.2864x | 1 / 2 / 1 | 0 |
| Core hard non-GB | 405/406 | 189 | 87.4070x -> 9.0491x | 335 / 44 / 15 | 85 |
| Regression smoke | 62/62 | 46 | 0.7846x -> 1.5027x | 0 / 43 / 19 | 28 |

There are zero refutations or unknown proof verdicts among established rows.
The sole non-GB core error is the pre-existing malformed Loki input. Regression
smoke remains 62/62 established; as in Rounds 23--24, its five-second quality
comparison remains phase-sensitive and does not meet the stored isolated
baseline on 19 rows.

## Round-26 analytical SMIR and generalized local synthesis

Round 26 adds the pure-OCaml `Smir_interp` module. It analytically lifts exact
core expressions with constant, additive, XOR, multiplicative, AND/OR-mask,
affine, quadratic, rotate-right, logical shifts and arithmetic-right-shift
rules. Candidate generation is untrusted: restored expressions still require
strict size reduction, holdout samples, `Rewrite.accepts`, and independently
replayable proof edges.

For the Xyntia backend, CHS now tries a deterministic cache-free enumerator
before invoking random search. It enumerates operator-stratified core trees
through size five, prunes symmetric/identity forms, and is bounded by 1,500
cores and 25 ms. Mixed-width inputs are excluded from binary cores, preserving
typed-DAG safety. Existing mock, CVC5 and portfolio backend contracts are not
silently bypassed.

`GeneralizeRule` replaces up to four shared maximal complex subexpressions with
fresh rule variables and admits the generalized template only after a fresh
0.2-second universal SMT proof. The unit gate checks both a sound generalized
MBA identity and a concrete identity whose abstraction is unsound. CHS also
tries at most twelve shared-variable pairs in AC chains of length 3--10; local
normalization and analytical candidates remain proof-gated, followed by a
whole-chain proof before replacement.

All analytical rules, exact enumeration, generalized-rule rejection, AC
pairwise cancellation, and prior corpus-backed tests pass. Curated results:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| QSynth EA weak | 60/60 | 16 | 11.0762x -> 2.3561x | 50 / 8 / 2 |
| Loki weak | 143/144 | 117 | 431.9448x -> 1.8219x | 143 / 0 / 0 |
| FloKI weak | 19/19 | 13 | 55.3892x -> 2.6252x | 15 / 4 / 0 |
| Tigress L5 weak | 23/23 | 0 | 437.4347x -> 226.8139x | 17 / 4 / 2 |
| Core hard non-GB | 405/406 | 187 | 87.4070x -> 7.9237x | 336 / 42 / 16 |
| Regression smoke | 62/62 | 47 | 0.7846x -> 1.4859x | 0 / 43 / 19 |

At least 104 successful core-hard CHS attempts returned within 30 ms in the
measured run. There are zero refutations, unknown proof verdicts, or process
timeouts among established rows. The only Loki/core failure is the known
malformed `line_0001001` input. Regression smoke remains 62/62 established;
its five-second quality remains above the stored isolated baseline, as already
reported in Rounds 23--25.

## Round-27 structured reconstruction, factor grouping and binary-lift polish

Round 27 removes the previous `cost >= 300` barrier for compact grouped
signature recovery through four active atoms and adds explicit overlapping
additive-split reconstruction. A new additive union-find pass partitions
independent variable components, simplifies components of at most four atoms,
and certifies the rebuilt whole expression with one `linear_mba_mod2w` edge.
This raises the remaining Neureduce exact count from 3 to 17 without adding a
new proof rule.

Boolean cleanup now recognizes XOR sum-of-products and common-AND distributive
factoring. GAMBA factor grouping prefers the largest factor when frequencies
tie and may retain a pure factorization even when the exposed cofactor is
already minimal; the factorization is certified by `ring_mod2w`. This is the
main reason all seven ObfuscatorX weak rows improve and their aggregate quality
reaches 1.0016x.

QSynthesis cast rules now truncate widened `+`, `-`, `*`, `&`, `|`, and `^`
operations directly to their narrow operands. Existing nested extension,
constant concat, complementary-mask and branchless selector rules remain
proof-gated; the Round-27 gate checks widened multiplication and explicit ITE
lifting. Structured Cases 3/5/6/7/8, negated forms, factor grouping, casts and
ITE candidates all independently replay in `test/round27_test.ml`.

Curated results:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Neureduce weak | 53/53 | 17 | 3.5649x -> 1.9811x | 34 / 13 / 6 |
| MBA-Flatten weak | 96/96 | 11 | 2.7087x -> 1.3901x | 95 / 1 / 0 |
| ObfuscatorX | 7/7 | 2 | 1.3104x -> 1.0016x | 7 / 0 / 0 |
| SiMBA e1 4-var weak | 12/12 | 12 | 113.1366x -> 1.0000x | 12 / 0 / 0 |
| Core hard non-GB | 405/406 | 189 | 87.4070x -> 8.9548x | 340 / 37 / 17 |
| Regression smoke | 62/62 | 46 | 0.7846x -> 1.6002x | 0 / 42 / 20 |

There are zero refutations, unknown proof verdicts, or timeouts among established
rows; the sole core failure is the known malformed Loki input. Regression smoke
remains fully established, while its five-second quality remains sensitive to
the additional deterministic phase ordering.

## Round-28 black-box semantic interpolation and DAG CSE

Round 28 adds bounded semantic probes independent of syntactic MBA shape.
`probe_semantic_linear_mba` evaluates one- to four-variable DAGs on the full
Boolean corner cube, performs modular Möbius reconstruction, minimizes the
result with the structured Round-27 engine, and rejects it unless full-width
holdout samples agree. `probe_semantic_poly` uses four univariate or six
bivariate evaluations, enumerates the exact 2-adic MSB lifts for divided finite
differences, emits centered degree-3/degree-2 power forms, and applies the same
full-width filter. Every surviving candidate still crosses `Rewrite.accepts`;
finite probing never establishes a result.

`semantic_dag_cse_pass` pre-indexes every unique node by complete width-aware
sample fingerprint, then traverses bottom-up. Constant candidates and smaller
cross-branch representatives are accepted only through `Rewrite.accepts`, with
at most 64 non-trivial attempts and a 0.5-second scheduling window. Unit tests
cover differently obfuscated carry decompositions, dead nonlinear branches,
wrapped linear noise, 64-bit cubic and bivariate quadratic recovery, and clean
rejection of `x & y` as an arithmetic polynomial.

The semantic root path also improves the earlier OMVLL regression from
`target_2558: 647 -> 107` to `647 -> 3`, smaller than its GT size 7. Curated
results:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Tigress L5 weak | 23/23 | 2 | 437.4347x -> 118.3432x | 20 / 0 / 3 |
| Tigress L6 weak | 84/84 | 6 | 1450.2012x -> 454.5251x | 41 / 15 / 24 |
| Loki weak | 143/144 | 125 | 431.9448x -> 2.2060x | 125 / 10 / 8 |
| Loki-tiny first 100 | 100/100 | 91 | 14.2659x -> 1.1734x | 99 / 1 / 0 |
| Core hard non-GB | 405/406 | 201 | 87.4070x -> 8.7275x | 327 / 36 / 31 |
| Regression smoke | 62/62 | 44 | 0.7846x -> 2.3078x | 0 / 39 / 23 |

There are zero refutations, unknown proof verdicts, or timeouts among established
rows. The sole Loki/core failure remains malformed `line_0001001`. The semantic
passes raise exact-GT coverage substantially, especially on Loki/Loki-tiny and
core-hard, but the fixed five-second smoke quality remains phase-sensitive and
regresses on 23 stored isolated baselines.

## Round-29 known bits, bounded arity and low-width recognition

Round 29 adds the DAG-memoized `Known_bits` abstract domain. Sound transfer
functions cover constants, variables, complement, Boolean operators, disjoint
addition, multiplication trailing zeroes, constant shifts (including sign
propagation), extension, restriction and conditional joins. Proof-gated
consumers collapse exact constants, redundant masks, disjoint AND/addition,
bounded unsigned comparisons, impossible equalities and dead ITE branches.
SMIR uses the target sample envelope to prune core expressions whose guaranteed
zero/one bits are already contradictory.

CHS truncation now backs off deep horizons until the cut has at most four
semantic stubs. Before synthesis, each multi-stub problem perturbs one stub at
a time with zero, one, fill and alternating-bit values; invariant stubs are
replaced by zero and removed from the synthesis problem. This remains heuristic
only: restored results still require `Rewrite.accepts` against the original
context.

For one-variable expressions through eight bits, exhaustive input evaluation
feeds all 256 outputs to the analytical SMIR recognizer. The new unit gate
cross-checks known-zero/known-one claims with Bitwuzla at 8 and 16 bits and
covers redundant masks, shift low-zeroes, carry-free addition, comparison/ITE
pruning, dead stubs, the four-stub cap and exhaustive byte recovery.

Curated results:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse | Known-bit edges |
|---|---:|---:|---:|---:|---:|
| Tigress L7 weak | 89/89 | 4 | 3016.6390x -> 766.0362x | 49 / 9 / 31 | 28 |
| Tigress L8 weak | 143/143 | 16 | 18349.0849x -> 3186.6999x | 72 / 22 / 45 | 79 |
| QSynth EA weak | 60/60 | 25 | 11.0762x -> 1.5316x | 58 / 0 / 2 | 16 |
| Core hard non-GB | 405/406 | 196 | 87.4070x -> 8.7677x | 330 / 35 / 29 | 418 |
| Regression smoke | 62/62 | 44 | 0.7846x -> 2.3720x | 0 / 39 / 23 | 12 |

There are zero refutations, unknown proof verdicts, or timeouts among established
rows. The sole core failure remains malformed Loki `line_0001001`. Deep Tigress
quality improves substantially, while the intentionally deferred five-second
smoke scheduling problem remains visible.
