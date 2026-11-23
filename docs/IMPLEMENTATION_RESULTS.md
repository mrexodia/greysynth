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

`egraph_extraction` therefore remains disabled by default. Baseline results
remain the authoritative 1,000/1,000 established, 984/16 C-Full result and the
five sub-1.00x MBA quality measurements. Milestone 4A remains open for
incremental/interruptible local-candidate scheduling and corpus acceptance.
