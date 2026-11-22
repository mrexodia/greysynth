# Proof coverage and further simplification

This follow-up applies to upstream `ec490c757d43b3b6de159be144e1b61277227ee8`
plus the earlier correctness patch. Its reference corpus is the same 1,000
C-Full/Tigress-level-5 cases. Both archive hashes and all 1,000 input and
ground-truth expression hashes were checked against the earlier audit.

## Results

**All 1,000 final outputs passed fresh independent certificate replay. Of those,
985 are strictly smaller than their original inputs and 15 are unchanged.**
The replay started a new checker process for every case, bound the actual
input/output endpoints, and recomputed the size metric from the accepted DAG.
There were no refutations, unresolved proofs, process timeouts, or errors.

| Measurement on the same 1,000 inputs | Earlier patch | This follow-up |
|---|---:|---:|
| Outputs with established equivalence | 830 direct proofs | 1,000 fresh compositional proofs |
| Strictly smaller outputs | 943 (773 directly proved) | 985 (all proved) |
| Unchanged outputs | 57 | 15 |
| Refuted outputs | 0 | 0 |

The earlier 170 inconclusive whole-expression checks were not known incorrect
outputs. The new checker establishes equivalence through separately proved
local equalities and congruence; it does not reinterpret a timeout as success.
The final selected runs retain 575 successful direct whole-expression checks
and 425 inconclusive direct checks, alongside the successful replay of every
selected certificate.

The complete normalization/OES configuration alone produced 984 smaller and
16 unchanged outputs, all independently proved. The final 985/15 result is a
**portfolio across configurations**: 921 outputs from that complete run,
27 from longer full-pipeline runs on the previous 57 unchanged cases, one from
a larger proof budget for a shifted-divisor candidate, and 51 from an OES-only
fallback with normalization and fast simplification disabled. Selection uses
the smallest proved output, with a fixed preference order to break ties.

Compared with the saved outputs of the earlier patch, the selected portfolio
has **897 smaller outputs, 103 equal in size, and none larger**. The complete
normalization/OES configuration by itself had 51 larger outputs than the
earlier patch; the separately recorded fallback addresses those regressions.
This is not a claim of single-configuration dominance. The earlier output
sizes only selected retry cases; neither earlier output expressions nor
supplied answers were adopted as synthesis results.

Of the earlier 57 unchanged cases, 42 now shrink, including all 35 larger
unchanged cases. Examples from the final, freshly replayed selection:

| Case | Original size | Final size |
|---|---:|---:|
| `target_1245` | 41,867 | 1,110 |
| `target_2532` | 31,763 | 947 |
| `target_1819` | 2,698 | 13 |
| `target_1840` | 1,267 | 21 |
| `target_1222` | 5 | 3 |

Authoritative final receipts are
`analysis/results/final-independent-replay-v2.jsonl` and its `.summary.json`,
which records `all_passed: true`, exact coverage of 1,000 distinct IDs, fresh
proofs, and unchanged artifact hashes. The receipt-file SHA-256 is
`25e95ba9ba42d78e232932ba184d893d01b8825153d8a335c2be5b48882ea003`.
The earlier `cfull-best-proved-v2.summary.json` is deliberately retained as the
pre-replay selection record: its `all_passed: null` and `complete: false`
describe that stage, not the outcome of the subsequent independent replay.

The primary reference is always the original parsed expression. The supplied
ground truth is not an input to synthesis. A result passes only with a direct
whole-expression proof or independently replayed compositional proof. Sample
agreement, an inconclusive solver result, and the producer's counters are not
proofs. Direct-check outcomes remain visible when replay establishes a proof.

## Changes

### Deterministic normalization

`src/greysynth/normalization.ml` adds a memoized bottom-up pass before OES:

- Constant folding under the total bitvector evaluator.
- Low-bit mask, constant shift, power-of-two division/remainder, extraction,
  extension, and shifted-divisor candidates.
- Local linear-MBA normalization using a conjunction basis over at most four
  structural atoms, with a 256-node form-construction limit.
- Opaque treatment of nonlinear and mixed-width subexpressions.

The finite tables generate candidates. Every committed replacement still
crosses the same independent sampling and SMT acceptance boundary. No dataset
identifiers, supplied answers, or expression-to-answer lookup tables are used.
The pass retains completed validated changes when a later operation times out.

The new `normalization` setting defaults to `true`. Setting it to `false`
retains the earlier pass ordering for comparisons. The existing size metric
does not charge for extract/extension wrappers: some compact improvements are
therefore expression-size reductions, not demonstrated machine-code speedups.

### Better local proofs

Repeated complex subexpressions can be replaced consistently by fresh typed
variables before a proof attempt. This removes constraints and makes the
equality stronger. A proof of the generalized equality implies the concrete
one by substitution. A satisfiable or inconclusive generalized query never
establishes inequivalence of the original expressions; concrete checking is
the fallback. Most of the requested deadline is reserved for that fallback.

For example, the valid 64-bit reduction

```
8192 / (x << 1)
    -> 4096 / zero_extend_1(extract_0_to_62(x))
```

preserves oversized/truncated denominator behavior and division by zero. It
was rejected by the two-second acceptance budget, but the same binary accepted
it with a five-second budget. Native checking and an independent Z3 formula
both establish the equality; the producer's 5-to-3 reduction was also replayed
independently. This is a bounded proof retry, not a change to bitvector semantics.

### Independent compositional replay

An optional certificate argument exports a typed AST DAG and concrete local
equality obligations:

```sh
greysynth -obf -string-file input.txt config.json proof.json > result.json
python3 -c 'import json,sys; print(json.load(sys.stdin)["syn_expr"])' < result.json > output.txt
mba_proof -obf -string-file input.txt -gt -string-file output.txt proof.json 1,5,30
```

Use the same `-size` on both tools if unsized literals are not 64 bits. The
optional timeout schedule retries only unresolved equality obligations.

The standalone checker:

1. Validates the DAG's operator arities, widths, constant ranges, and references.
2. Binds its endpoints to the externally supplied input and actual output.
3. Rechecks local equality obligations with fresh SMT queries.
4. Uses only established equalities, congruence, and transitivity to derive
   endpoint equality.

Unused equations are permitted, but neither an equation's presence nor a
producer-supplied status establishes it. Missing derivations stay inconclusive;
refuted intermediate equalities invalidate the certificate without claiming
that the final output itself is refuted. Certificate data cannot rename the
externally supplied semantic problem.

The producer reports `recorded_not_replayed`. Only the independent checker
reports `proved_compositional`. Replay does not use synthesis caches, samples,
or acceptance counters. It shares the fixed-width expression semantics, SMT
encoding, and native solver trust boundary. It is not a SAT-proof kernel and
does not certify the C/binary lifting frontend or memory behavior.

## Why not every input can become smaller

Seven original inputs are provably minimal under the present pure-expression
grammar and size metric:

| Cases | Lower-bound argument |
|---|---|
| `target_2677` | Already size 1; every expression contains at least one charged leaf. |
| `target_1505`, `target_1508`, `target_2478`, `target_4972`, `target_6217`, `target_6441` | Already size 3 and demonstrably depend on two original input variables. Every expression costing less than 3 has at most one variable leaf. Free extract/extension wrappers cannot introduce the missing dependency. |

Concrete dependency witnesses were checked both with direct Z3 bitvector
formulas and the native checker. Thus 1,000 strict reductions are impossible;
993 is a defensible upper bound, not a claim that every other case can shrink.
The other eight unchanged cases are `target_3090`, `target_3092`, `target_3279`,
`target_3324`, `target_3585`, `target_5836`, `target_6281`, and `target_6569`.
They are not labelled minimal merely because this search found no smaller
candidate. Fourteen of the 15 unchanged inputs have size 1 or 3; the remaining
one, `target_6569`, has size 5.

## Inconsistent input/answer pairs

Two compact cases' original inputs and supplied ground truths are inequivalent
under the parsed bitvector semantics:

| Case | Concrete input | Original value | Supplied answer's value |
|---|---|---:|---:|
| `target_5836` | `x0 = 0xffffffff` | 0 | 256 |
| `target_2651` | `x0 = 0xffffffff`, `x1 = 1` | 536,870,911 | 0 |

The first pair uses sign extension in the input and zero extension in the
answer's divisor. The second uses unsigned 64-bit division followed by
truncation in the input, versus signed 32-bit division in the supplied answer.
Both mismatches were confirmed with independent direct Z3 terms and the native
checker. These observations identify inconsistent pairs; they do not determine
which expression faithfully represents the original source C program.

`target_5505` also differs textually from its supplied answer, but is equivalent:
its final shift discards the difference between arithmetic and logical right
shifts. Textual differences alone were not treated as data errors.

## Reproduction and evidence

The audit bundle retains all 1,000 original case JSON files with their supplied
answers unchanged, exact configurations, binary hashes, every per-case record,
source hashes, proof certificates, the dataset recovery script, and the
independent data-quality/minimality diagnostics. Source datasets remain
available from the [official artifact](https://zenodo.org/records/22649859).
The earlier complete inventory is in [VALIDATION.md](VALIDATION.md) and
[dataset-provenance.json](dataset-provenance.json).

The full deterministic audit enables normalization, fixed-point OES, and the
existing relational vocabulary, with a 15-second internal budget and two
seconds per accepted-rewrite proof. Longer CHS runs use a 30-second budget for
the 57 earlier unchanged cases. The shifted-divisor retry allows five seconds
for acceptance. The 51-case fallback uses a ten-second internal budget and
two seconds per acceptance proof. The direct whole-expression check allows
one second; initial independent replays allow five seconds per equality. The
final fresh selection replay uses a 5,15-second retry schedule per equality
and a 90-second process cap. Exact options are retained in each run summary.

Solver budgets and configurations differ from the earlier OES-only run.
These are coverage measurements, not a controlled speed benchmark or a
replication of the publication's full experiments. In particular, this
iteration covers only C-Full/Tigress level 5, not every referenced dataset.

The harness checks the complete corpus against its original inputs and retains
independent replay certificates when `--proof-checker` is supplied. Its process
limits are separate from the simplifier's internal budget; a native operation
already in flight can finish after the internal deadline. A cancelled
exploratory run is explicitly marked incomplete and excluded from complete
corpus totals.

Validation includes the earlier parser/evaluator/pipeline/checker suites,
18 solver-backed normalization regressions plus policy/timeout tests,
typed-DAG and certificate tampering tests, six audit-reporting tests, a real
producer/checker CLI smoke, and 27 native checks of the independent dataset
diagnostics. Selection-integrity tests also reject stale certificates paired
with edited outputs, even if the output hash was recomputed, and reject
forged size metadata. `make test` requires a working SMT backend.
