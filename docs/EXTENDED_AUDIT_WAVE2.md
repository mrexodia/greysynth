# Extended Audit — Wave 2

## Executive summary

Wave 2 audits every remaining distinct extracted dataset with no `--limit`.
The actual denominator is **53,865 cases**, matching the requested total after
excluding comment headings from the three complex-handler files. Initial raw
line counts suggested 53,880 because each handler file contains five `#`
section headings; these are metadata, not expressions.

Results:

```text
53,547 / 53,865 established (99.41%)
0 refuted
0 unknown
0 timeout
318 syntax errors
50,473 strict reductions
3,074 unchanged
```

All 318 failures are the same Xyntia `b2_combined` syntax boundary: 159 rows use
infix `lsl` and 159 use infix `lsr`, while GreySynth's textual grammar accepts
`<<`/`>>` (and indexed/prefix forms), not those aliases. This is systemic, so it
was diagnosed rather than pointlessly rerun.

Across the 51,000 cases with ground truth, 40,732 are solved at or below GT,
3,366 are meaningfully shrunk, and 6,902 remain weak. Geometric `output / GT`
is **1.7847x**, with median compression **7.0x**. The quality aggregate hides a
sharp split: compact Boolean/linear suites are strong, while four- and
five-variable SiMBA plus high-degree polynomial suites remain the dominant gap.

## Provenance and protocol

- Repository HEAD: `a202663a1f4f1b8770b614498fc4eb35417cb68c`
- Implementation baseline: `3f856ab`
- GreySynth SHA-256:
  `e5c1ba4f0ea10ff5c4f365c65ff3e5e0811722a2f76fb453cf6bf8981007c346`
- `mba_equiv` SHA-256:
  `d95a72dc395430a3509d43fbf5716195913754cc0b0f8d24c092bb53b7a965a9`
- `mba_proof` SHA-256:
  `830a82b9e3ab6439e8fca3102a4d42798b461ec02cbb949c38cb907339439141`
- R18 config SHA-256:
  `5a496ef347d727919af7d33f066afb9d0dfd72092efbc20d608fb8734b5e5940`

All suites used ten workers and the exact R18 budget:

```text
total_timeout=5, synthesis_timeout=1, equiv_timeout=1
--timeout 20 --smt-timeout 2 --proof-timeout 5
--proof-process-timeout 90 --raw-bitwidth 64
```

Ground-truth suites used `--check-ground-truth`. Xyntia single-column suites
were converted to JSON under `/tmp/greysynth-bench/wave2-input/xyntia/` with
`{obf_expr, bitwidth: 64}` and were checked only against their original inputs.
No repository dataset was modified.

Artifacts:

```text
/tmp/greysynth-bench/wave2-r18/external/
/tmp/greysynth-bench/wave2-r18/simba/
/tmp/greysynth-bench/wave2-r18/xyntia/
```

## Classification

For suites with GT, only `proved` and `proved_compositional` rows enter quality
buckets:

- **Solved:** output size <= GT size.
- **Meaningful:** output is above GT but <= 2x GT, or input shrank by >= 50%.
- **Weak:** output remains above 2x GT and shrank by < 50%.

For Xyntia there is no GT, so only proof status, strict reduction, unchanged
count, and compression are reported.

## Master table

### External large suites

| Suite | Cases | Established (direct+comp) | Refuted | Unknown/timeout | Error | Strict | Unchanged | Solved | Meaningful | Weak | Geomean out/GT | Median compression | Wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Neureduce | 10,000 | 10,000 (1,728+8,272) | 0 | 0 | 0 | 8,987 | 1,013 | 5,869 | 2,771 | 1,360 | 1.1989x | 4.36x | 6,300.4s |
| Loki Tiny | 25,000 | 25,000 (24,480+520) | 0 | 0 | 0 | 24,695 | 305 | 24,230 | 367 | 403 | 1.0639x | 9.33x | 2,958.9s |

### SiMBA e1–e5 scaling suites

| Suite | Cases | Established (direct+comp) | Refuted | Unknown/timeout | Error | Strict | Unchanged | Solved | Meaningful | Weak | Geomean out/GT | Median compression | Wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| e1 / 2 vars | 1,000 | 1,000 (268+732) | 0 | 0 | 0 | 1,000 | 0 | 1,000 | 0 | 0 | 1.0000x | 6.67x | 188.1s |
| e1 / 3 vars | 1,000 | 1,000 (60+940) | 0 | 0 | 0 | 1,000 | 0 | 918 | 42 | 40 | 1.2080x | 21.33x | 386.4s |
| e1 / 4 vars | 1,000 | 1,000 (14+986) | 0 | 0 | 0 | 974 | 26 | 529 | 0 | 471 | 9.5254x | 107.83x | 1,209.0s |
| e1 / 5 vars | 1,000 | 1,000 (0+1,000) | 0 | 0 | 0 | 1,000 | 0 | 0 | 0 | 1,000 | 936.1771x | 1.10x | 1,079.0s |
| e2 / 2 vars | 1,000 | 1,000 (0+1,000) | 0 | 0 | 0 | 1,000 | 0 | 1,000 | 0 | 0 | 1.0000x | 20.00x | 332.5s |
| e2 / 3 vars | 1,000 | 1,000 (0+1,000) | 0 | 0 | 0 | 1,000 | 0 | 896 | 67 | 37 | 1.4113x | 53.00x | 483.7s |
| e2 / 4 vars | 1,000 | 1,000 (24+976) | 0 | 0 | 0 | 904 | 96 | 14 | 0 | 986 | 320.2662x | 1.01x | 1,225.1s |
| e3 / 2 vars | 1,000 | 1,000 (1+999) | 0 | 0 | 0 | 999 | 1 | 1,000 | 0 | 0 | 1.0000x | 4.40x | 235.7s |
| e3 / 3 vars | 1,000 | 1,000 (1+999) | 0 | 0 | 0 | 999 | 1 | 924 | 46 | 30 | 1.1546x | 14.40x | 419.1s |
| e3 / 4 vars | 1,000 | 1,000 (25+975) | 0 | 0 | 0 | 901 | 99 | 7 | 0 | 993 | 70.0359x | 1.01x | 1,172.3s |
| e4 / 2 vars | 1,000 | 1,000 (1+999) | 0 | 0 | 0 | 999 | 1 | 1,000 | 0 | 0 | 1.0000x | 3.14x | 285.7s |
| e4 / 3 vars | 1,000 | 1,000 (1+999) | 0 | 0 | 0 | 999 | 1 | 919 | 20 | 61 | 1.1523x | 10.29x | 572.1s |
| e4 / 4 vars | 1,000 | 1,000 (19+981) | 0 | 0 | 0 | 926 | 74 | 7 | 0 | 993 | 50.1479x | 1.01x | 1,164.8s |
| e5 / 2 vars | 1,000 | 1,000 (0+1,000) | 0 | 0 | 0 | 1,000 | 0 | 1,000 | 0 | 0 | 1.0000x | 5.25x | 241.2s |
| e5 / 3 vars | 1,000 | 1,000 (0+1,000) | 0 | 0 | 0 | 1,000 | 0 | 885 | 53 | 62 | 1.2720x | 15.25x | 424.3s |
| e5 / 4 vars | 1,000 | 1,000 (9+991) | 0 | 0 | 0 | 968 | 32 | 534 | 0 | 466 | 8.0875x | 80.12x | 1,237.4s |

SiMBA aggregate: **16,000/16,000 established**, 15,669 strict reductions,
10,633 solved, 228 meaningful, 5,139 weak, 5.1355x quality, and 5.33x median
compression.

### Xyntia suites (no GT)

| Suite | Cases | Established (direct+comp) | Refuted | Unknown/timeout | Error | Strict | Unchanged | Median compression | Wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| b2 | 1,110 | 1,110 (1,019+91) | 0 | 0 | 0 | 591 | 519 | 1.15x | 156.0s |
| b2_combined | 1,110 | 792 (660+132) | 0 | 0 | 318 | 433 | 359 | 1.14x | 230.6s |
| complex_handlers bp1 | 15 | 15 (10+5) | 0 | 0 | 0 | 8 | 7 | 1.05x | 7.2s |
| complex_handlers bp2 | 15 | 15 (13+2) | 0 | 0 | 0 | 3 | 12 | 1.00x | 9.4s |
| complex_handlers bp3 | 15 | 15 (1+14) | 0 | 0 | 0 | 15 | 0 | 1.13x | 13.7s |
| if_the_else merged1 | 20 | 20 (20+0) | 0 | 0 | 0 | 0 | 20 | 1.00x | 1.4s |
| if_the_else merged2 | 20 | 20 (20+0) | 0 | 0 | 0 | 0 | 20 | 1.00x | 6.1s |
| if_the_else merged3 | 20 | 20 (20+0) | 0 | 0 | 0 | 0 | 20 | 1.00x | 9.8s |
| if_the_else merged4 | 20 | 20 (20+0) | 0 | 0 | 0 | 0 | 20 | 1.00x | 9.7s |
| if_the_else merged5 | 20 | 20 (20+0) | 0 | 0 | 0 | 0 | 20 | 1.00x | 9.8s |
| Syntia b1 | 500 | 500 (500+0) | 0 | 0 | 0 | 72 | 428 | 1.00x | 8.1s |

Xyntia aggregate: **2,547/2,865 established**, 1,122 strict reductions, 1,425
unchanged, and 318 syntax errors.

### Wave 2 aggregate

| Cases | Established | Refuted | Unknown/timeout | Error | Strict | Unchanged | Solved* | Meaningful* | Weak* | Geomean out/GT* | Median compression* |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **53,865** | **53,547** | **0** | **0** | **318** | **50,473** | **3,074** | **40,732** | **3,366** | **6,902** | **1.7847x** | **7.00x** |

`*` GT metrics cover the 51,000 Neureduce/Loki-Tiny/SiMBA cases. Xyntia has no
GT and is excluded.

## Per-family diagnostics

### Neureduce

All 10,000 rows establish; 8,987 strictly reduce. Results are 5,869 solved,
2,771 meaningful, and 1,360 weak (1.1989x quality). The long tail is mostly
three-variable dense Boolean arithmetic that falls just beyond compact grouped
reconstruction. Examples:

- line 2639: size 74 unchanged, GT 5 (14.8x).
- line 3836: size 71 unchanged, GT 5 (14.2x).
- line 5151: 72 -> 71, GT 6.

Priority: broaden grouped Boolean reconstruction and component partitioning
without reintroducing the uninterruptible root-search behavior fixed in R18.

### Loki Tiny

All 25,000 rows establish; 24,695 strictly reduce. This suite is strong overall:
24,230 solved, 367 meaningful, 403 weak, and 1.0639x quality. Remaining examples
are compact but deeply nested forms where no local candidate opens the final
identity:

- line 4,816: size 264 unchanged, GT 3.
- line 19,092: size 237 unchanged, GT 3.
- line 19,782: size 205 unchanged, GT 3.

These are better targets for bounded whole-pipeline portfolios than for a larger
global e-graph.

### SiMBA e1–e5: variable scaling

The decisive factor is variable count, not merely e-level:

| Variables | Cases | Solved | Meaningful | Weak | Strict reductions |
|---|---:|---:|---:|---:|---:|
| 2 | 5,000 | **5,000** | 0 | 0 | 4,998 |
| 3 | 5,000 | **4,542** | 228 | 230 | 4,998 |
| 4 | 5,000 | 1,091 | 0 | **3,909** | 4,673 |
| 5 | 1,000 | 0 | 0 | **1,000** | 1,000 |

The current six-atom limit is not equivalent to supporting five independent
variables: dense five-variable truth tables require up to 32 minterms and much
larger Boolean reconstruction. `e1_5vars/line_730`, for example, reduces only
3,472 -> 3,165 while GT is size 3 (1,055x). Four-variable examples such as
`e2_4vars/line_249` remain size 403 for GT 1.

Priorities: connected-component decomposition before truth-table recovery,
NPN/ESOP-style compact Boolean synthesis, and proof kernels that avoid emitting
dense minterm expansions.

### Xyntia

- `b2` is fully accepted; 591/1,110 strictly reduce.
- `b2_combined` has exactly 318 parser errors: 159 use infix `lsl`, 159 use
  infix `lsr`. Example: `(... ) lsl 0x8`. This is a source-language adapter gap;
  the parser correctly rejects unsupported aliases.
- Complex-handler suites have no errors after excluding their five `#` section
  headings per file. bp3 strictly reduces all 15 expressions.
- All 100 `if_the_else` rows parse despite using single `=` as the supported
  equality spelling, but remain unchanged under the five-second configuration.
- Syntia b1 has no errors, but only 72/500 strict reductions.

Priorities: a provenance-preserving Xyntia token adapter (`lsl`/`lsr` to
`<<`/`>>`), followed by conditional-aware synthesis/extraction for
`if_the_else` and broader residual synthesis for b1/b2.

## Bugs, crashes, and timeout findings

1. **No soundness failures:** zero refuted outputs in all 53,865 cases.
2. **No crashes or solver timeouts:** every parseable Wave-2 expression
   terminates and is established.
3. **One systemic parser boundary:** 318 `b2_combined` rows use unsupported
   infix word shifts. No parser weakening or source mutation was performed.
4. **Dataset denominator correction:** complex-handler files contain 45
   expressions plus 15 `#` headings; only expressions were audited.
5. **No malformed certificates:** every accepted result either directly proves
   or independently replays compositionally.

## Grand unified backlog across ~80k evaluations

The full audit (7,011), Wave 1 (18,995), and Wave 2 (53,865) total **79,871
evaluated rows**. Using isolated-rerun results where applicable:

```text
79,273 established (99.25%)
0 refuted by the current proof-carrying pipeline
598 unresolved/input-incompatible
```

The 598 unresolved rows are 583 persistent syntax/input errors and 15 hard
resource timeouts from the earlier audits; Wave 2 adds 318 of the syntax errors
and no timeouts.

### Priority 0 — correctness and fail-closed invariants

- Preserve independent certificate replay and direct SMT checking; the old paper
  pipeline produced 16 refuted outputs, while the current pipeline produces
  zero across all three audits.
- Keep host-integer conversion guards and malformed-certificate rejection.
- Maintain isolated low-concurrency replay for contention-sensitive giant cases.

### Priority 1 — explicit dataset-language adapters

Implement adapters, not permissive parser hacks, for:

- Xyntia infix `lsl`/`lsr` aliases (318 Wave-2 rows).
- OSES unary plus, `//` annotations, and indexed `X[n]` syntax (12 Wave-1 rows),
  followed by investigation of 50 OSES GT semantic mismatches.
- Raw Full-Loki's 249 stray `}` prefixes and final unmatched row, retaining raw
  and sanitized provenance.
- Invalid OMVLL restriction bounds should remain explicit input errors.

### Priority 2 — high-degree polynomial representation

Wave 1's Univariate64, Multivariate64, and Permutation64 remain the most severe
algebraic gap: 2,002 weak rows, with quality up to 628x. Replace bounded AST
expansion with:

- high-degree falling-factorial/Hensel reduction,
- sparse Horner/composition recognition,
- modular multivariate ideal/component reduction,
- compact proof rules that do not enumerate thousands of monomials.

### Priority 3 — variable-scalable Boolean reconstruction

Wave 2 shows a clean cliff: 100% solved at two variables, 91% at three, only 22%
at four, and 0% at five. Required work:

- component partitioning before atom counting,
- compact ESOP/NPN/CNF search,
- grouped coefficient recovery over components,
- proof decomposition that avoids 2^n dense minterm certificates.

This also targets the residual Neureduce, MBA-Flatten, Non-Poly, and linear MBA
quality tails from the earlier audits.

### Priority 4 — DAG/regional simplification

Tigress L6–L8, OMVLL, Loki, and Full-Loki contain repeated trees from tens of
thousands to over a million nodes. Needed:

- structural hash-consing before traversal/cost accounting,
- regional saturation under a global extraction objective,
- persisted proved template rules across related targets,
- cooperative deadlines inside every candidate generator.

### Priority 5 — proof-gated whole-pipeline portfolios

The paper, R17, and R18 schedules each find unique small proved outputs. Race
whole pipelines and retain the minimum independently proved result, especially
for QSynth, Loki/Full-Loki, Loki Tiny, and medium Non-Poly cases. This should
recover quality without weakening soundness.

### Priority 6 — conditional and residual synthesis

All 100 Xyntia `if_the_else` rows remain unchanged, most b1 rows are unchanged,
and ObfuscatorX remains only meaningfully reduced. Improve condition-aware CHS
ranking, branch predicate extraction, and instruction/shift-aware factorization.

## Conclusion

Wave 2 confirms that the current proof boundary scales: every parseable case is
established and no output is refuted. The next gains will not come from more
single-expression peepholes. They require three architectural capabilities:
explicit source-language adapters, a high-degree polynomial representation, and
Boolean/DAG decomposition that scales beyond three variables and 2,048 enodes.
