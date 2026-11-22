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
| PLDI Poly | 1.0602x | 1.1033x | 3.0755x |
| PLDI Non-Poly (before ring kernel) | 19.2494x | 39.8843x | 2.5498x |
| PLDI Non-Poly (ring-certified minterms) | **1.5868x** | **3.7286x** | **30.9318x** |
| MBA-Obfuscator nonlinear | 11.4734x | 11.6924x | 1.0916x |
| QSynth EA | 1.0073x | 1.3707x | 11.4693x |

All 400 outputs are proved against their inputs. Short whole-expression checks
against supplied ground truths prove 155 and leave 245 explicitly unknown;
these ratios compare syntax/cost and do not claim that every supplied answer is
semantically consistent. The native minterm + modular-ring pass subsequently
moves PLDI Non-Poly geometric quality from **19.2494x to 1.5868x** and makes all
100 cases strictly smaller. With a five-second replay schedule, all 100 outputs
are established (2 direct and 98 compositional proofs). MBA-Obfuscator algebra
is now the dominant remaining quality gap.

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

The current eight-worker C-Full deterministic run remains **1,000/1,000 proved,
984 strict reductions, 16 unchanged** after structured real samples and the
expanded local proof machinery.

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
but does not replace general polynomial normalization or whole-pipeline
portfolio extraction.
