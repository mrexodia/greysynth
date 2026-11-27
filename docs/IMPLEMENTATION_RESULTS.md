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

## Round-30 forensic phase ordering and budget isolation

Round 30 moves expensive semantic probing behind decidable DAG/root passes,
limits post-DAG root probes to 256-node expressions with a 0.25-second proof
budget, and caps semantic-CSE proof attempts at 0.15 seconds. Semi-linear root
work now rejects large/no-mask/high-arity inputs before candidate construction,
and giant DAG peeling uses a minimal pass family so later semantic and
semi-linear probes cannot starve the original minterm/ring engines.

The polynomial fast exit now applies only to size-three results or compact
mask-free decidable results from large/nonlinear polynomial inputs. A one-pass
zero-seed OES path is reserved for very large two-variable shared DAGs, avoiding
the three-variable `target_366` starvation. E-graph equal-cost/equal-node
extraction now prefers lower arithmetic/bitwise alternation before structural
ordering.

The focused regression gate independently replays:

```text
C-MBA target_3218:       54,904 -> 5
PLDI Non-Poly row 895:      593 -> 5
msimba row 191:             248 -> 5
Tigress L7 target_1016: 264,797 -> 9   (unit gate <= 13)
Tigress L8 target_1016: 1,324,003 -> 9 (unit gate <= 13)
C-MBA target_366:       3,400,417 -> 11
```

Curated results:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Regression smoke | 62/62 | 51 | 2.3720x -> 0.9197x | 3 / 45 / 14 |
| Core hard non-GB | 405/406* | 208 | 87.4070x -> 6.2539x | 363 / 20 / 11 |

`*` One contended Tigress-L8 replay was unknown in the four-worker run and
proved compositionally on its isolated rerun (`1,701,958 -> 266`); the sole
remaining core error is malformed Loki `line_0001001`. Smoke returns to 61/62
strict decreases (one giant OSES row remains unchanged), with zero refutations
or timeouts. The `target_2558` five-second path remains budget-sensitive at
roughly size 21--23 (versus size 3 with a longer budget), so that flagship does
not yet meet the requested `<= 7` five-second guard despite replaying cleanly.

## Round-31 survivor-driven lifting, extraction and giant peeling

Round 31 adds constructive low-mask lifting for zero-extended low slices,
including the nested complemented form, and exposes those candidates to local
normalization and bottom-up DAG processing. Partial linear-sum extraction now
expands one small distributive layer, separates nonlinear products from linear
MBA terms, simplifies each partition independently, and composes
`ring_mod2w`/`linear_mba_mod2w` proof edges before factor grouping. Pure
factorization remains available when the cofactor is already minimal.

Root linear reconstruction now starts at size 15. Semantic linear probing also
feeds its canonical Möbius form through syntactic disjoint-component splitting,
and two-value reconstruction projects away truth-table variables that are
semantically inactive. A compact semi-linear cleanup recognizes
`offset + k*x - 2k*(mask&x) == k*(x^mask)`, restoring `msimba/191` to exact GT.
Giant DAG scheduling permits eight shrinking rounds and a bounded OES seed,
while preserving the Round-30 flagship phase order.

Focused wins include:

```text
C-MBA target_1685: 29,511 -> 5 (GT 7)
C-MBA target_3218: 54,904 -> 5
msimba row 191:       248 -> 5
Tigress L7/L8 target_1016: -> 9 in isolated audit
```

Curated results (all JSONLs retained at `/tmp/r31-*/out.jsonl`):

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| PLDI Poly weak | 62/62 | 12 | 2.5679x -> 1.2463x | 62 / 0 / 0 |
| Neureduce weak | 53/53 | 7 | 3.5649x -> 2.1308x | 37 / 11 / 5 |
| MBA-Flatten weak | 96/96 | 21 | 2.7087x -> 1.2032x | 95 / 1 / 0 |
| Core hard non-GB | 405/406 | 213 | 87.4070x -> 5.9553x | 372 / 14 / 8 |
| Regression smoke | 62/62 | 51 | 0.9197x -> 0.9162x | 3 / 47 / 12 |

There are zero refutations, unknown proof verdicts, or process timeouts among
established rows; malformed Loki `line_0001001` remains the sole core error.
Smoke remains at 61/62 strict reductions because giant OSES row 240 is still
unchanged, but its 0.9162x geomean remains below the required 0.95x ceiling.
The named PLDI rows 904/941/795 and Neureduce rows 98/632/798 improve only
partially rather than reaching their requested exact bounds, and giant Tigress
L8 target 5856 remains unchanged; these survivor gaps are reported explicitly.

## Round-32 survivor bug fixes

Round 32 moves the bounded OES seed behind giant-DAG peeling for multi-variable
inputs while retaining the proven two-variable fast path needed by the
Tigress-1016 guards. Giant bottom-up processing always retains known-bits,
peephole, nonlinear, linear and ring cleanup, and post-DAG OES is branch-local.
The Round-30 flagship gate remains green (`target_3218 -> 5`, `target_366 -> 11`,
`msimba/191 -> 5`, and Tigress L7/L8 1016 within size 13).

Linear recovery now projects two-value tables at full active support, tries both
Boolean polarities and complement forms, and partial linear-sum extraction
scores direct linear, direct ring, and ring-then-linear routes instead of
short-circuiting after a one-node ring win. Complementary low-slice substitution
and two's-complement `-x-1`/`-1-x`/`-(x+1)` peepholes are proof-gated throughout
normalization. A small candidate-side complement cleanup remains untrusted and
is still verified against the restored original context.

Curated outputs are retained at:

```text
/tmp/r32-gate/pldi/out.jsonl
/tmp/r32-gate/neureduce/out.jsonl
/tmp/r32-gate/qsynth/out.jsonl
/tmp/r32-gate/smoke/out.jsonl
/tmp/r32-core/out.jsonl
```

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| PLDI Poly weak | 62/62 | 17 | 2.5679x -> 1.1767x | 62 / 0 / 0 |
| Neureduce weak | 53/53 | 7 | 3.5649x -> 2.1738x | 32 / 12 / 9 |
| QSynth EA weak | 60/60 | 24 | 11.0762x -> 1.4940x | 58 / 0 / 2 |
| Core hard non-GB | 405/406 | 228 | 87.4070x -> 5.8241x | 367 / 14 / 13 |
| Regression smoke | 62/62 | 51 | 0.9162x -> 0.9034x | 3 / 47 / 12 |

There are zero refutations, unknown proof verdicts, or timeouts among established
rows; malformed Loki `line_0001001` remains the sole core error. Smoke stays
below the required 0.95x ceiling with 61/62 strict reductions. The requested
exact survivor targets are not all closed: PLDI 904/795, Neureduce 98/632/798,
QSynth 388, C-MBA 1685, Tigress-L8 5856, and OMVLL 771 remain above their target
bounds. These rows remain in the `/tmp/r32-*` JSONLs for the next forensic pass.

## Round-33 exact two-value offsets and bounded giant proofs

Round 33 fixes the signed bitvector two-value theorem in `linear_candidates`.
The base value is now `target.(0)` rather than unsigned `min(distinct)`, and both
zero-preserving and one-preserving Boolean encodings use their exact modular
offsets (`v0 + (v1-v0)B` and `(2v0-v1) + (v0-v1)~B`). This directly closes
Neureduce 632 and PLDI Poly 904, and substantially improves the remaining
multi-value weak suites. Full-active tables through four atoms now use the same
polarity machinery rather than requiring a dummy variable.

Raw known-bits SMT is again excluded from minimal giant-DAG mode. Mask/slice and
peephole checks are bounded, `Rewrite.accepts` clamps proof time to the remaining
global budget, and small raw expressions bypass e-graph saturation that cannot
respect the case deadline. This removes the 18-second QSynth-388 hang and takes
that row from `71 -> 9` exact GT in under four seconds. A direct abstract-checked
two-atom nonlinear product rule is available during bottom-up peeling, while
ring/linear/peephole cleanup remains active on giant DAGs.

Selected real-row results:

```text
Neureduce 98:   76 -> 7  (GT 8)
Neureduce 632:  72 -> 9  (GT 9)
Neureduce 489:  72 -> 10 (GT 11)
PLDI Poly 904:  93 -> 12 (GT 12)
QSynth EA 388:  71 -> 9  (GT 9)
MBA nonlinear 972: 166 -> 7 (GT 6)
```

Curated JSONLs are retained at `/tmp/r33-gate/*/out.jsonl` and
`/tmp/r33-core/out.jsonl`:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Neureduce weak | 53/53 | 18 | 3.5649x -> 1.1073x | 53 / 0 / 0 |
| PLDI Poly weak | 62/62 | 19 | 2.5679x -> 1.2236x | 62 / 0 / 0 |
| QSynth EA weak | 60/60 | 31 | 11.0762x -> 1.1973x | 59 / 0 / 1 |
| Core hard non-GB | 405/406 | 242 | 87.4070x -> 5.2775x | 380 / 8 / 6 |
| Regression smoke | 62/62 | 51 | 0.9034x -> 0.9181x | 3 / 48 / 11 |

There are zero refutations, unknown proof verdicts, or process timeouts among
established rows; malformed Loki `line_0001001` remains the sole core error.
Smoke remains 61/62 strict and below the required 0.95x ceiling. Canonical
Möbius component reconstruction is still incomplete for Neureduce 798/140 and
PLDI 941, and the deeply wrapped giant targets C-MBA 1685, Tigress-L8 5856 and
OMVLL 771 remain above their requested bounds.

## Round-34 De Morgan/Shannon closure and compositional peeling

Round 34 adds exact two-variable Boolean lookup plus one-variable Shannon
factoring for three-atom truth tables, in both full and active-projected
reconstruction. De Morgan cleanup is applied to compact negated terms without
changing the established large nonlinear phase order. This closes the remaining
small structured survivors: `Neureduce/98 -> 7`, `632 -> 9`, `489 -> 10`,
`140 -> 11`, `PLDI/904 -> 12`, `941 -> 12`, `QSynth/388 -> 9` on isolated
replay, and `MBA nonlinear/972 -> 6` exact GT.

Complementary low-slice substitution now runs ring reduction before scoring and
takes `C-MBA/3551: 506 -> 3` (GT 5). The direct two-atom product identity now
emits three `linear_mba_mod2w` bridge edges plus one `ring_mod2w` edge instead
of raw SMT. All remaining raw DAG peephole/mask/demand/pullout SMT calls are
capped to nodes of cost at most 512 and 0.15 seconds.

Curated outputs remain available at `/tmp/r34-gate/*/out.jsonl` and
`/tmp/r34-core/out.jsonl`:

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Neureduce weak | 53/53 | 50 | 3.5649x -> 0.9076x | 53 / 0 / 0 |
| PLDI Poly weak | 62/62 | 22 | 2.5679x -> 1.1957x | 62 / 0 / 0 |
| Core hard non-GB | 405/406* | 263 | 87.4070x -> 5.3703x | 379 / 8 / 7 |
| Regression smoke | 62/62 | 52 | 0.9181x -> 0.9079x | 3 / 49 / 10 |

`*` One contended OMVLL proof replay was unknown in the four-worker run and
proved compositionally on isolated rerun; malformed Loki `line_0001001` remains
the sole core error. There are zero refutations or process timeouts. Smoke stays
61/62 strict and below the 0.95x ceiling. Neureduce 798 remains one node above
GT, and the deeply wrapped C-MBA 1685, Tigress-L8 5856/5710, and OMVLL 771/798
still do not expose the direct compositional peel pattern.

## Authoritative Round-34 full survivor scoreboard

The final scoreboard was run at HEAD `952efd1` (implementation commit
`039ed2a`) with the exact R18 configuration, `mba_equiv`, independent
`mba_proof` replay, and eight workers. The authoritative parallel output is:

```text
/tmp/r34-all-failing/out.jsonl
```

The input contains 1,876 previously failing/weak rows. Seven pre-existing giant
OMVLL JSON files were explicitly excluded: targets 3716, 773, and 802
(approximately 1.1 GB each), 800 (139.4 MB), 4687 (114.3 MB), 4678 (92.5 MB),
and 533 (84.9 MB). Quality and better/equal/worse columns cover the 1,864 rows
that carry stored baseline and GT sizes. `U/E/T` means unknown/error/timeout;
`Row wall` is cumulative per-case wall time, while the eight-worker audit's
actual elapsed time was 1,420.7 seconds (23m 40.7s).

| Suite | Cases | Established | Refuted | U/E/T | Exact GT | Quality before -> after | Better / equal / worse | Row wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| c_mba_obfuscator | 152 | 152 | 0 | 0/0/0 | 140 | 69.5511x -> 1.0654x | 151 / 0 / 1 | 644.5s |
| floki | 19 | 19 | 0 | 0/0/0 | 15 | 55.3892x -> 1.5364x | 19 / 0 / 0 | 69.3s |
| loki | 144 | 143 | 0 | 0/1/0 | 133 | 431.9448x -> 1.4953x | 134 / 2 / 7 | 611.7s |
| loki_tiny | 403 | 403 | 0 | 0/0/0 | 401 | 16.4268x -> 1.0113x | 403 / 0 / 0 | 531.6s |
| mba_flatten | 96 | 96 | 0 | 0/0/0 | 36 | 2.7087x -> 1.1426x | 96 / 0 / 0 | 707.3s |
| mba_obf_nonlinear | 255 | 255 | 0 | 0/0/0 | 238 | 13.4231x -> 0.6802x | 255 / 0 / 0 | 953.4s |
| neureduce | 53 | 53 | 0 | 0/0/0 | 49 | 3.5649x -> 0.9087x | 53 / 0 / 0 | 261.7s |
| obfuscatorx | 7 | 7 | 0 | 0/0/0 | 7 | 1.3104x -> 0.8857x | 7 / 0 / 0 | 68.2s |
| omvll | 92 | 92 | 0 | 0/0/0 | 21 | 481.5234x -> 15.5922x | 85 / 0 / 4 | 1,055.6s |
| oses | 4 | 4 | 0 | 0/0/0 | 1 | 10.8662x -> 5.1414x | 2 / 1 / 1 | 19.9s |
| permutation64 | 10 | 10 | 0 | 0/0/0 | 10 | 76.1156x -> 0.9500x | 10 / 0 / 0 | 57.3s |
| pldi_poly | 62 | 62 | 0 | 0/0/0 | 22 | 2.5679x -> 1.1945x | 62 / 0 / 0 | 482.3s |
| qsynth_ea | 60 | 60 | 0 | 0/0/0 | 30 | 11.0762x -> 1.2309x | 59 / 0 / 1 | 423.6s |
| simba_e1_3vars | 40 | 40 | 0 | 0/0/0 | 40 | 13.1727x -> 1.0000x | 40 / 0 / 0 | 89.4s |
| simba_e1_4vars | 12 | 12 | 0 | 0/0/0 | 12 | 113.1366x -> 1.0000x | 12 / 0 / 0 | 29.0s |
| simba_e2_3vars | 37 | 37 | 0 | 0/0/0 | 37 | 47.4562x -> 1.0000x | 37 / 0 / 0 | 84.1s |
| simba_e3_3vars | 30 | 30 | 0 | 0/0/0 | 30 | 8.9435x -> 1.0000x | 30 / 0 / 0 | 70.2s |
| simba_e4_3vars | 61 | 61 | 0 | 0/0/0 | 61 | 6.3638x -> 1.0000x | 61 / 0 / 0 | 209.1s |
| tigress_l5 | 23 | 23 | 0 | 0/0/0 | 2 | 437.4347x -> 119.1323x | 22 / 0 / 1 | 232.2s |
| tigress_l6 | 84 | 84 | 0 | 0/0/0 | 4 | 1450.2012x -> 172.6973x | 73 / 5 / 2 | 834.7s |
| tigress_l7 | 89 | 89 | 0 | 0/0/0 | 0 | 3016.6390x -> 610.7064x | 84 / 2 / 3 | 966.1s |
| tigress_l8 | 143 | 140 | 0 | 0/0/3 | 9 | 18349.0849x -> 2599.5295x | 121 / 8 / 10 | 2,657.3s |
| **Overall parallel** | **1,876** | **1,872** | **0** | **0/1/3** | **1,298** | **59.9565x -> 3.7192x** | **1,816 / 18 / 30** | **11,058.6s** |

The one parallel error is the known malformed Loki `line_0001001`. The three
parallel timeouts were Tigress-L8 targets 1281, 1285, and 5697. The parallel
numbers above are preserved unchanged. All three timeout rows were rerun with
one worker and independently proved directly (three `proved`, zero unresolved),
with net-neutral outputs. Isolated artifacts are retained at:

```text
/tmp/r34-all-failing-isolated/out.jsonl
```

The separate 62-case regression smoke gate, from the same `039ed2a` binary, is
retained at `/tmp/r34-gate/smoke/out.jsonl`: 62/62 established, zero refuted or
unresolved, 52 exact-GT, quality `0.7846x -> 0.9079x`, and `3 / 49 / 10`
better/equal/worse in 37.3 seconds elapsed (258.9 cumulative row-seconds).

## True Round-34 corpus-wide exact-GT scoreboard

The 5,278 previously untested non-exact rows were audited at HEAD `039ed2a`
with the same R18 configuration and eight workers. The immutable parallel and
isolated outputs are:

```text
/tmp/r34-untested-non-exact/out.jsonl
/tmp/r34-untested-non-exact-isolated/out.jsonl
```

The parallel run established 5,276/5,278 rows (`1,366` direct and `3,910`
compositional proofs), with zero refutations, zero errors, zero process timeouts,
and two unknown proof replays; 5,174 outputs strictly decreased and 104 were
net-neutral. Elapsed time was 3,954.1 seconds (65m 54.1s). On isolated rerun,
Tigress-L8 target 1215 proved compositionally; OMVLL target 1082 remained
unknown even with a 20-second per-edge replay budget. These isolated outcomes
do not alter the parallel counts.

Applying the Round-34 all-failing and untested overlays rebuilt the managed hard
sets. `all_non_exact` shrank from 5,853 to 3,100 non-GB rows (2,753 removed,
47.04%), `untested_non_exact` is now empty, and the refreshed `core_hard`
contains 353 rows. Seven giant OMVLL rows remain separated.

| Suite | all_non_exact before -> true remaining |
|---|---:|
| c_mba_obfuscator | 155 -> 65 |
| permutation64 | 0 -> 0 |
| obfuscatorx | 0 -> 0 |
| omvll | 327 -> 177 |
| tigress_l5 | 617 -> 450 |
| tigress_l6 | 593 -> 468 |
| tigress_l7 | 610 -> 475 |
| tigress_l8 | 622 -> 501 |
| loki | 81 -> 12 |
| floki | 63 -> 21 |
| qsynth_ea | 207 -> 146 |
| pldi_poly | 320 -> 201 |
| pldi_nonpoly | 365 -> 84 |
| mba_obf_nonlinear | 161 -> 38 |
| msimba | 0 -> 0 |
| mba_flatten | 906 -> 401 |
| neureduce | 214 -> 24 |
| simba_e1_4vars | 22 -> 0 |
| simba_e1_5vars | 0 -> 0 |
| simba_e2_4vars | 0 -> 0 |
| simba_e3_4vars | 0 -> 0 |
| simba_e4_4vars | 0 -> 0 |
| simba_e5_4vars | 0 -> 0 |
| simba_e1_3vars | 42 -> 0 |
| simba_e2_3vars | 67 -> 0 |
| simba_e3_3vars | 46 -> 0 |
| simba_e4_3vars | 20 -> 0 |
| loki_tiny | 369 -> 7 |
| oses | 46 -> 30 |
| b2_combined | 0 -> 0 |
| univariate64 | 0 -> 0 |
| multivariate64 | 0 -> 0 |
| **Overall non-GB** | **5,853 -> 3,100** |

The rebuilt manifest covers all 54,105 audited expressions across 32 suites:

| Corpus-wide metric | Round-34 result |
|---|---:|
| Total audited | 54,105 |
| Known malformed skipped | 3 |
| Parseable proved | 54,091 / 54,102 (99.9797%) |
| Refuted | 0 |
| Expressions with usable GT | 52,645 |
| Proved output <= GT | 49,548 / 52,645 (94.117%) |
| Proved output <= 1.25x GT | 50,007 / 52,645 (94.989%) |
| Proved output <= 1.50x GT | 50,304 / 52,645 (95.553%) |
| Proved output <= 2.00x GT | 50,475 / 52,645 (95.878%) |
| <= GT as fraction of all audited rows | 49,548 / 54,105 (91.5775%) |
| True remaining non-GB all_non_exact | 3,100 |
| Separated giant OMVLL | 7 |

The authoritative generated counts and overlay provenance are stored in
`datasets/hard_cases/manifest.json`; generated hard-case directories remain
workspace datasets and are intentionally excluded from Git.

## Round-35 normalization modularization and parity audit

The 5,235-line `normalization.ml` implementation was split mechanically into an
acyclic include chain. `Normalization` remains the public facade, so callers,
record types, proof boundaries, and function identities are unchanged. No
candidate generator, acceptance policy, solver budget, or proof rule changed.
Compiler warning-as-error checks surfaced only three unnecessary lexical
`open Config` directives, which were removed; the build is warning-clean.

| Module | Lines | Scope |
|---|---:|---|
| `norm_common.ml` | 60 | Typed-AST, bitvector, constant, and canonical helpers |
| `norm_peepholes.ml` | 839 | Compiler/bitwise peepholes, canonical and minterm bridges |
| `norm_linear.ml` | 525 | Linear MBA and Boolean reconstruction |
| `norm_semilinear.ml` | 559 | Semi-linear masks, known-bits consumers, pullout/slices |
| `norm_poly.ml` | 936 | Permutation inversion, ring and modular polynomial engines |
| `norm_nonlinear.ml` | 1,029 | PolySim, nonlinear cancellation, factor/group recovery |
| `norm_probes.ml` | 796 | Local portfolios, quotient DAGs, semantic probes |
| `normalization.ml` | 528 | DAG/oracle/run orchestration and API facade |

`make test` passes in full. The two corpus-backed tests whose generated
`all_failing/` fixtures were intentionally removed by the new hard-dataset
builder now read the canonical `permutation64.txt` and OMVLL source case
instead; they exercise the same rows and assertions.

Parity artifacts:

```text
/tmp/r35-smoke/out.jsonl
/tmp/r35-smoke-isolated/out.jsonl
/tmp/r35-core/out.jsonl
/tmp/r35-core-isolated/out.jsonl
```

| Gate | Parallel result | Isolated resolution |
|---|---|---|
| Regression smoke (62) | 62/62 established, 0 refuted/unresolved, 51 exact, 1.0206x | Four differing rows replayed; the multivariate contention case returned `2403 -> 3`, restoring 52 exact and an overlay-adjusted 0.9104x |
| Refreshed core hard (353) | 349 established, 0 refuted/errors, 1 unknown, 3 timeouts, 5 exact, 23.1722x | All three Tigress-L8 timeout rows proved directly; OMVLL target 1082 remained unknown, giving 352 established / 1 unknown and 22.8818x |

The authoritative eight-worker smoke run was affected by one severe
Multivariate64 contention result (`3` at Round 34 versus `2403` in parallel);
therefore its raw 1.0206x does not meet the 0.95x parity threshold. The isolated
replay restores the same 52 exact-GT count and <=0.95x quality envelope without
altering the parallel record. Core-hard contains the already documented OMVLL
1082 proof unknown; there are no refutations or malformed-input errors in the
refreshed 353-case slice.

## Round-36 shift/slice-aware opaque-atom peeling

The linear and semi-linear proof kernels now explicitly support constant `Lsl`
as scalar multiplication in arithmetic position while retaining shifts as
strict opaque atoms under bitwise operators. `semilinear_mba_mod2w` additionally
recognizes only the sound low-slice form
`uext(amount, restrict(0, hi, x)) == x & ((1 << (hi+1))-1)` when the widths match;
non-zero extracts and sign extension remain opaque. Positive carry/borrow and
low-slice identities, plus negative shift-under-bitwise, non-zero-extract and
sign-extension traps, are cross-checked against Bitwuzla.

Bottom-up linear peeling no longer counts variables buried inside nonlinear or
cast children: it invokes the bounded opaque-atom reconstructor directly and
certifies successful rewrites with `linear_mba_mod2w`. Semi-linear candidates
also run in minimal giant-DAG mode. Abstract slice rules cover shifted-away low
bits, masks disjoint from zero-extended slices, low restrictions with identity
constants, and restrictions through zero extension. Complemented scaled terms
are canonicalized before bitwise cancellation, and a final small ring polish is
run before preprocessing returns.

The new synthetic `round36_test` covers large opaque children, arithmetic
shifts, low slices, shifted-away restrictions and complemented scaled terms;
`make test` remains warning-clean and fully green.

Parity and target artifacts:

```text
/tmp/r36-final-l5/out.jsonl
/tmp/r36-final-core/out.jsonl
/tmp/r36-final-core-isolated/out.jsonl
/tmp/r36-final-smoke/out.jsonl
```

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 59 | 25.4124x -> 14.8828x | 238 / 108 / 104 |
| Refreshed core hard | 353/353* | 17 | 24.3105x -> 17.1394x | 59 / 266 / 25 |
| Regression smoke | 62/62 | 53 | 0.7846x -> 0.8860x | 4 / 49 / 9 |

`*` The final eight-worker core run had three Tigress-L8 process timeouts; all
three proved directly on isolated one-worker rerun with net-neutral outputs.
The final smoke run established 62/62 directly with zero unresolved rows and no
isolation adjustment. There are zero refutations or remaining timeout/error
verdicts after isolated replay. Focused Tigress-L5 results include target 3126
exact (`5639 -> 19`), target 3500 (`4605 -> 13`, GT 11), target 4671
(`2421 -> 10`, GT 7), and target 6533 (`564 -> 11`, GT 5). The stricter
semi-linear slice hotfix reduces the final L5 exact count from the pre-hotfix
61 to 59 while restoring the required proof-kernel soundness. Deeply wrapped
Tigress-L8 giant targets still require further exposure.

## Round-37 opaque-atom semi-linear and bit-zero recovery

Round 37 changes semi-linear candidate generation to use the exact opaque atoms
collected by the strict MSiMBA preflight rather than recursively enumerating
leaf variables. Valid low slices add their effective masks to the disjoint-mask
basis while arithmetic beneath a slice remains opaque. Single-atom vocabularies
now include additive offsets, reverse subtraction, complemented offsets and
scaled forms. The permanent Round-36 counterexample remains rejected by both
the proof kernel and Bitwuzla.

Equal-Legacy-cost cast cleanup is admitted only when Paper-AST node cost strictly
decreases, allowing constant `uext`/`sext`/`restrict` folding and nested-cast
collapse without creating cost cycles. `Known_bits` now propagates trailing
zeroes and exact bit-zero parity through addition/subtraction and folds constant
shift amounts through casts. Universal low-bit parity candidates cover masked
addition/subtraction and zero-extended bit slices. Zero-SMT product peeling is
also available in the local candidate portfolio, and abstract slice identities
are tested over division-heavy opaque subtrees.

The new `round37_test` and proof-kernel negative regression pass, and `make test`
remains warning-clean. Final artifacts:

```text
/tmp/r37-l5/out.jsonl
/tmp/r37-core/out.jsonl
/tmp/r37-core-isolated/out.jsonl
/tmp/r37-smoke/out.jsonl
```

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 87 | 25.4124x -> 10.3328x | 284 / 57 / 109 |
| Refreshed core hard | 353/353* | 16 | 24.3105x -> 15.6013x | 64 / 260 / 26 |
| Regression smoke | 62/62 | 52 | 0.7846x -> 0.8910x | 3 / 49 / 10 |

`*` Three Tigress-L8 rows timed out in the parallel core run and all three
proved directly with net-neutral outputs on isolated replay. There are zero
refutations or remaining unresolved rows. Focused L5 results include target
6533 exact (`564 -> 5`), target 2135 (`502 -> 13`, GT 5), target 2618
(`1705 -> 17`, GT 3), target 3500 (`4605 -> 13`, GT 11), and target 6367
(`4907 -> 13`, GT 7). Opaque-atom and cast handling improve the aggregate
substantially, although several deeply nested target forms remain above GT.

## Round-38 opaque semantic interpolation and local structural cleanup

Round 38 adds a bounded `probe_opaque_atoms` engine for one to three repeated
opaque sub-DAGs. It tries strict operator-boundary and shared-subterm
abstractions, reconstructs a compact conjunction-basis candidate, filters it on
16 full-width abstract samples, restores the concrete atoms, and admits it only
through decidable linear-MBA replay or the existing proof-gated SMT fallback.
This keeps nonlinear multiplication, division, rotate and cast internals out of
the abstract proof obligation.

Complementary-constant product peeling now handles constant-folded `C`/`~C`
factors using semi-linear bridge edges plus ring normalization. Product peeling
is available in local portfolios as well as DAG traversal. Local candidates now
include abstract slice cleanup and common `restrict(lo,hi)` factoring across
`&`, `|`, and `^`. Unit coverage includes target-158-style opaque carries,
shared one-atom offsets, constant-complement products, division-heavy slices,
and restriction factoring; `make test` remains warning-clean.

Final artifacts:

```text
/tmp/r38-l5/out.jsonl
/tmp/r38-core/out.jsonl
/tmp/r38-core-isolated/out.jsonl
/tmp/r38-smoke/out.jsonl
```

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 134 | 25.4124x -> 6.8957x | 324 / 37 / 89 |
| Refreshed core hard | 353/353* | 63 | 24.3105x -> 6.5202x | 125 / 200 / 25 |
| Regression smoke | 62/62 | 54 | 0.7846x -> 0.8232x | 5 / 50 / 7 |

`*` Three Tigress-L8 rows timed out in the parallel core run and all three
proved directly with net-neutral outputs on isolated replay. There are zero
refutations or unresolved rows after isolation. Focused wins include Tigress-L5
target 1373 (`4264 -> 5` exact), target 1499 (`9664 -> 5` exact), target 3500
(`4605 -> 11` exact), and target 5498 (`41387 -> 7` exact). More deeply wrapped
targets such as 158, 2968, 3728, and 2618 improve but remain above GT.

## Round-39 DAG memoization and zero-SMT-first scheduling

Round 39 makes preprocessing explicitly DAG-native for highly shared inputs.
Critical recursive normalization analyses now memoize with `Sexpr.BvTbl`, the
rewrite caches use hash-cons-aware expression-pair tables, and the proof graph's
expression index uses `Sexpr.BvTbl` without changing any replay rule or proof
semantics.

`dag_bottom_up_simplify` now supports a zero-SMT mode, a cumulative SMT budget,
an optional local deadline, and soft stopping. A soft stop keeps every accepted
subtree rewrite in the memo table and rebuilds the unsimplified ancestors rather
than throwing away partial work. Every SMT-backed local check has an explicit
short timeout; once the cumulative budget is exhausted, decidable linear,
semi-linear, ring, polynomial, product, complement, and correlated-null passes
continue without invoking Bitwuzla. Highly shared roots receive the zero-SMT DAG
phase before expensive root expansion. Small-root cleanup also includes
zero-SMT product peeling and opaque-atom probing.

`test/round39_test.ml` covers a synthetic million-node AST with fewer than 100
DAG nodes, soft local-deadline preservation, target-2618-style exact product
cleanup, and independent compositional certificate replay. The complete
warning-clean `make test` gate passes.

Final eight-worker artifacts:

```text
/tmp/r39-l5/out.jsonl
/tmp/r39-core/out.jsonl
/tmp/r39-smoke/out.jsonl
```

| Gate | Established | Exact | Geomean quality before -> after | Better / equal / worse |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 155 | 25.4124x -> 5.2131x | 344 / 23 / 83 |
| Refreshed core hard | 353/353 | 71 | 24.3105x -> 3.4329x | 166 / 163 / 21 |
| Regression smoke | 62/62 | 53 | 0.7846x -> 0.8304x | 6 / 49 / 7 |

All 450 Tigress-L5 rows strictly decrease; the previous 16 net-neutral stalls
are eliminated. Core hard establishes all 353 rows directly in the parallel
run with zero timeouts, zero unknowns, and zero refutations; only four unrelated
non-Tigress rows remain net-neutral. Giant Tigress-L8 reductions include
`target_1169: 4,377,943 -> 474`, `target_6503: 2,702,423 -> 96`,
`target_3601: 2,666,519 -> 80`, `target_126: 2,486,999 -> 80`, and
`target_2790: 2,463,063 -> 7` exact. Tigress-L5 `target_158` now reaches its
size-9 GT.

## Round-40 arithmetic atom boundaries and generalized product peeling

Round 40 makes opaque interpolation preserve pure-arithmetic sub-DAGs that are
used beneath bitwise or shift shells. A DAG-memoized shell analysis chooses
arithmetic boundaries before the shared-node and operator-boundary fallbacks,
preventing carry-sensitive atoms from being split into unrelated variables.
One-atom abstractions additionally use analytical XSMIR candidates; two-atom
abstractions add direct affine/bitwise offset templates. Candidate filtering now
uses 16 independently varied full-width assignments. DAG probing covers costs
through 256 and tries linear-MBA, semi-linear-MBA, then bounded abstract SMT in
that order.

The zero-SMT product peeler now preserves exact product and sum operand order,
scans signed additive trees with up to eight terms, recognizes affine algebraic
complements modulo `2^w`, and emits explicit ring/linear bridges for those
complements. It also recognizes zero-extension of a low-width intersection and
records the existing abstract-SMT equality needed to distribute `uext` over
`&`. Final product proofs continue to compose from existing SMT, linear-MBA,
semi-linear-MBA, and ring rules; `src/proof/rewrite_proof.ml` is unchanged.

`test/round40_test.ml` covers arithmetic-boundary interpolation, one-variable
XSMIR, operand-order preservation, algebraic-complement matching under two
negative additive terms, zero-extension lifting, and independent certificate
replay. The complete warning-clean `make test` gate passes.

Final eight-worker artifacts:

```text
/tmp/r40-l5/out.jsonl
/tmp/r40-core/out.jsonl
/tmp/r40-smoke/out.jsonl
```

| Gate | Established | Exact | Round-39 -> Round-40 quality | Better / equal / worse vs Round 39 |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 207 | 5.2131x -> 3.5428x | 159 / 221 / 70 |
| Refreshed core hard | 353/353 | 82 | 3.4329x -> 3.0877x | 43 / 287 / 23 |
| Regression smoke | 62/62 | 52 | 0.8304x -> 0.8455x | 0 / 58 / 4 |

There are zero refutations, unknowns, errors, or audit timeouts. All 450
Tigress-L5 rows remain strict decreases, and all 353 core rows establish
directly in the parallel run. Exact Tigress-L5 wins include `target_126: 7`,
`target_1349: 5`, `target_2127: 5`, `target_2136: 5`, `target_2618: 3`,
`target_2818: 3`, `target_3728: 5`, and the three related targets
`6014/6027/6086: 5`; `target_2968` reaches size 3, beating its size-5 GT.
Core Tigress-L8 `target_1349` and `target_2818` also reach exact GT.

## Round-41 strict DAG budgets, wide samples, and constant-mask lifting

Round 41 closes the three scheduling leaks exposed by the expanded Round-40
passes. DAG product peeling with a non-empty abstract-equality list is now
forbidden in `zero_smt` mode and runs through the cumulative `try_smt` budget in
bounded mode. Opaque DAG probes run only on nodes with a bitwise/shift shell,
only outside minimal and zero-SMT passes, and at most 16 times per invocation.
Semi-linear replay is skipped unless the endpoints contain a mask, shift, cast,
or restriction. Algebraic-complement inspection is capped at expression cost
4096.

Opaque interpolation now checks 24 deterministic independent values spanning
the complete bit width, including 96-, 128-, and 224-bit inputs, then applies
`Rewrite.samples_agree` once to the restored concrete candidate before returning
it. Root probing accepts costs through 2048 while retaining the 256-node DAG
cap, and follows an accepted opaque rewrite with product and semi-linear
peeling. Product matching also lifts constant-mask forms such as
`uext(x & C)` and `uext(x & ~C)` through one explicit abstract equality.

`test/round41_test.ml` covers a 513–2048-cost/small-DAG opaque shell, 96- and
224-bit recovery, constant-mask zero-extension peeling, independent certificate
replay, and a strict zero-SMT non-invocation assertion. The complete
warning-clean `make test` gate passes, and `src/proof/rewrite_proof.ml` remains
unchanged.

Final eight-worker artifacts:

```text
/tmp/r41-l5/out.jsonl
/tmp/r41-core/out.jsonl
/tmp/r41-smoke/out.jsonl
/tmp/r41-l5-isolated/out.jsonl
```

| Gate | Established | Exact | Round-40 -> Round-41 quality | Better / equal / worse vs Round 40 |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 179 | 3.5428x -> 4.0487x | 100 / 237 / 113 |
| Refreshed core hard | 353/353 | 79 | 3.0877x -> 3.0512x | 37 / 278 / 38 |
| Regression smoke | 62/62 | 54 | 0.8455x -> 0.7933x | 4 / 58 / 0 |

There are zero refutations, unknowns, errors, or audit-process timeouts. The
regression smoke gate returns to 62 strict decreases; in particular
`oses__line_0000240` recovers from the Round-40 net-neutral 564,134-node output
to 4,835 nodes. Core `qsynth_ea__line_0000458` returns to size 20,
Tigress-L5 `target_6370` remains exact at size 5, and core Tigress-L6
`target_1803` reaches its size-9 GT. The authoritative parallel L5 run contains
one net-neutral row (`target_547`); its isolated replay is also established and
net-neutral, so this is not a proof failure or worker-contention timeout.

## Round-42 opaque-probe accounting and abstract proof budget

Round 42 makes two surgical scheduling changes. The per-pass opaque-probe quota
is now consumed only when `probe_opaque_atoms` returns an actual candidate;
cheap `None` results below a useful parent no longer starve that parent. Opaque
abstract checks use 0.60 seconds in DAG traversal, 0.70 seconds in cleanup, and
0.80 seconds at roots, with a 1.5-second cumulative DAG SMT budget.

The independent proof scheduler now assigns an abstract pair half rather than a
quarter of the requested timeout (`timeout *. 0.5`). This is the only Round-42
change in `src/proof/rewrite_proof.ml`; no proof rule, endpoint check, or replay
semantics changed.

`test/round42_test.ml` covers a 64-bit 77-node nonlinear-atom carry shell that
reaches size 7 and replays independently in under one second. It also places 22
non-matching bitwise subtrees below a matching opaque parent and verifies that
`None` probe results cannot exhaust the 16-candidate quota. The complete
warning-clean `make test` gate passes.

Final eight-worker artifacts:

```text
/tmp/r42-l5/out.jsonl
/tmp/r42-core/out.jsonl
/tmp/r42-smoke/out.jsonl
/tmp/r42-one/out.jsonl
```

| Gate | Established | Exact | Round-41 -> Round-42 quality | Better / equal / worse vs Round 41 |
|---|---:|---:|---:|---:|
| Tigress L5 all_non_exact | 450/450 | 200 | 4.0487x -> 3.5301x | 62 / 347 / 41 |
| Refreshed core hard | 353/353 | 82 | 3.0512x -> 3.1873x | 24 / 301 / 28 |
| Regression smoke | 62/62 | 54 | 0.7933x -> 0.7995x | 0 / 59 / 3 |

There are zero refutations, unknowns, errors, or audit-process timeouts.
Tigress-L5 recovers exact results for targets 798, 800, and 802 (all size 5),
keeps target 2127 exact, and reduces target 6503 to size 7, beating its size-9
GT. The authoritative parallel run contains four L5 and eleven core net-neutral
rows. Regression smoke has one parallel net-neutral row,
`oses__line_0000240`; its one-worker isolated replay establishes a strict
`564,134 -> 4,985` reduction, identifying parallel solver contention rather
than a proof failure.

## Round-43 balanced DAG budget and authoritative Tigress L5–L8 sweep

Round 43 rebalances only the internal DAG solver allocation. The opaque SMT
fallback inside `dag_bottom_up_simplify` uses 0.25 seconds and each bounded DAG
pass has a 1.0-second cumulative SMT budget. Root opaque probing remains at
0.80 seconds, cleanup remains at 0.70 seconds, and only successful opaque
candidate generation consumes the 16-candidate quota. Proof replay and
`src/proof/rewrite_proof.ml` are unchanged. The complete warning-clean
`make test` gate passes.

Regression smoke (`/tmp/r43-smoke/out.jsonl`) establishes all 62 rows directly
under eight workers with 62 strict decreases, 54 exact-or-better outputs, zero
refutations, and quality `0.7968x`. In particular, the prior parallel
`oses__line_0000240` stall is eliminated.

The authoritative full Tigress sweep ran each level separately with eight
workers and independent `mba_equiv` plus `mba_proof` replay:

```text
/tmp/r43-l5/out.jsonl
/tmp/r43-l6/out.jsonl
/tmp/r43-l7/out.jsonl
/tmp/r43-l8/out.jsonl
```

| Level | Established | Exact <= GT | Quality before -> after | Better / equal / worse | Strict decreases |
|---|---:|---:|---:|---:|---:|
| Tigress L5 | 450/450 | 199 | 25.4124x -> 3.5011x | 372 / 16 / 62 | 447 |
| Tigress L6 | 468/468 | 196 | 43.9750x -> 4.8564x | 417 / 12 / 39 | 465 |
| Tigress L7 | 475/475 | 174 | 83.2516x -> 7.5831x | 410 / 15 / 50 | 472 |
| Tigress L8 | 501/501 | 166* | 226.0878x -> 12.0906x | 431 / 8 / 59 | 499 |
| **Combined** | **1,894/1,894** | **735*** | **69.7301x -> 6.3890x** | **1,630 / 51 / 210** | **1,883** |

`*` Three L8 rows have no usable GT, so exact counts cover 498/501 L8 rows and
1,891/1,894 combined rows. All 1,894 rows establish in the authoritative
parallel runs with zero refutations, unknowns, errors, or audit timeout
verdicts. Consequently no isolated contention-timeout replay was required.
