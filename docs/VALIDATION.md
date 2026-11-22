# Correctness audit and dataset provenance

Audited upstream: `binsec/greysynth`, commit
`ec490c757d43b3b6de159be144e1b61277227ee8` (21 November 2026).

## Measured results (completed native runs)

Both the untouched upstream checkout and the patched tree built successfully.
The solver-required regression suite passed using OCaml 5.3.0, Dune 3.17.2,
vendored BINSEC 0.10.1, Xyntia 0.2.0, and Bitwuzla-C 1.0.6. Tests include parser
round trips, concrete evaluation, 15 pipeline regressions plus a contextual
SMT proof, 38 checker/solver regressions, and six checker CLI cases.

### Complete C-Full / Tigress level 5: 1,000 cases

This experiment isolates OES: CHS, global synthesis, and the relational fast
pass are disabled. All runs use 100 synthesis samples and a five-second
simplification budget. A separate checker tests the returned expression
against the original input with 256 samples, then a one-second SMT query.
The patched code also uses 32 independent validation samples. The old and
patched heuristic configurations have identical JSON content; the verified
configuration additionally requires proof for every rewrite.

| Outcome | Upstream OES | Patched, sampling only | Patched, verified (default policy) |
|---|---:|---:|---:|
| Whole expression proved equivalent | 691 | 765 | 830 |
| Refuted | 123 | 2 | 0 |
| Inconclusive whole-expression check | 186 | 233 | 170 |
| Proved equivalent and strictly smaller | 655 | 723 | 773 |
| Strictly smaller, all verdicts | 964 | 958 | 943 |
| Unchanged size | 36 | 42 | 57 |
| Expansion | 0 | 0 | 0 |
| Synthesis/checker process errors | 0 | 0 | 0 |

The 170 inconclusive checks are not promoted to whole-expression proofs.
Verified mode separately proved each accepted local rewrite: the run recorded
12,680 accepted rewrite proofs, 300 disproved candidates, and 534 inconclusive
candidates. It reached the internal time budget in 85 cases while retaining
validated work. There were no hard process timeouts.

Of the **123 refuted baseline cases**, verified mode produced **118 strict
reductions**: 85 independently proved as whole expressions, 33 inconclusive
under the one-second whole-expression check. Five were unchanged and proved
equivalent. Thus the repairs do not merely replace every failure with its
original input, but they do not eliminate all unchanged outcomes either.

Sampling alone still fails. `target_1840` incorrectly changes an OR to addition.
`target_6828` becomes zero after all 256 checks agree, yet SMT finds `x0 = 60`.
Its ground truth is `2 << (x0 - 54)` at width 32, which evaluates to 128 there.
The latter is a new regression in heuristic mode relative to upstream, making
the default proof guard essential. The verified run refuted neither case.

Native CLI reproduction of the bounded-hash bug: upstream returns zero for
`(x + C) ^ ((y + C) + 0)`, with `C = 2^62`. The patched verified OES result has
seven nodes instead of nine, and the checker proves equivalence. This is a
useful simplification rather than an unchanged fallback.

### Actual Xyntia integration: targeted 64-case stress suite

The suite selects the first 32 lexicographic IDs among baseline-OES failures
and the first 32 among baseline-OES proofs. It is deliberately biased and is
**not an estimate of a population error rate**. The baseline runs OES + CHS;
the patched variant runs verified OES + CHS and enables the existing relational
fast pass. Both use a five-second simplification budget and the same separate
checker as above.

| Outcome | Upstream full pipeline | Patched combined pipeline |
|---|---:|---:|
| Whole expression proved equivalent | 23 | 39 |
| Refuted | 22 | 0 |
| Inconclusive check | 17 | 25 |
| Synthesis crashes | 2 | 0 |
| Proved equivalent and strictly smaller | 22 | 38 |
| Strictly smaller, all verdicts | 61 | 63 |
| Unchanged size | 1 | 1 |

Both baseline crashes were `Z.Overflow` (`target_1742`, `target_1840`). All 32
selected prior OES failures still shrink in the patched full pipeline, with
16 whole-expression proofs and 16 inconclusive checks. Fourteen full-baseline
refutations become proved strict reductions. Native Xyntia is actually exercised:
431 synthesis attempts across 42 patched cases, with 74 recorded successful
synthesis simplifications.

This is not uniform dominance: two baseline proofs become checker-unknown,
and among the 21 cases proved for both builds, the patched result is smaller
in four, equal-sized in sixteen, and larger in one (still smaller than its
original input). Changing the budget or search configuration can change these
outcomes. The targeted comparison also enables an existing fast pass, so it
measures the combined pipeline rather than attributing all gains to one fix.

The accompanying audit bundle contains all case records, summaries, exact
configurations, binary/checker hashes, split selection, and paired comparisons.
Elapsed run times are preserved for reproduction, but these concurrent,
different-worker runs are not a controlled speed benchmark. The friend's
specific 30% claim remains unverified; the complete isolated OES run establishes
123 refutations out of 1,000 under the stated configuration.

## What this change addresses

1. **Bounded hashes were used as semantic identities.** The evaluator indexed
   cached values by `Hashtbl.hash node`, and OES/CHS used
   `Hashtbl.hash outputs` as the entire equality key. The default OCaml hash
   visits at most ten meaningful values and one hundred total nodes. Different
   output vectors can therefore share a hash systematically when the early
   samples agree. Full expression keys and complete output signatures now
   decide equality. A digest over every output only selects a hash bucket.
2. **Evaluation mixed incompatible shift semantics.** Ordinary samples masked
   shift counts with 63; cut-leaf samples did not. Both paths now implement total
   bitvector operations consistently, including oversized shifts, rotations by
   arbitrary amounts, division/remainder by zero, and 64/128-bit edge values.
3. **Verification failed open and missed rewrite paths.** The previous
   `reject_non_equiv_simplifications` accepted unknown/timeout, did not protect
   OES or semantic-cache hits, and checked independent cut labels instead of
   the original contextual expression. Every speculative replacement now uses
   one boundary: same width, strict size reduction after restoration, complete
   sample agreement, independent validation samples, and (in the default
   strict mode) an SMT proof. Unknown is not a proof.
4. **Useful valid candidates could be lost.** Context-dependent candidates are
   checked after restoring cut leaves. The smallest representative of a shared
   cut-leaf signature is retained. A raw backend result remains available when
   algebraic postprocessing fails, changes semantics, or offers no size benefit.
   Completed validated rewrites are retained when a later node exhausts the
   total budget, including partial OES passes and CHS horizons.
5. **Checking and serialization could change the problem.** The checker now
   covers all pure operators, keeps sample agreement separate from proof, and
   rejects silent input-width coercion. Parsing/printing preserve widths and
   variable identity and round-trip supported pure expressions.

### Small reproductions

At width 64, let `C = 0x4000000000000000`:

```text
(x + C) ^ ((y + C) + 0)
```

The old output-hash construction cannot distinguish the relevant subtrees
when its hash traversal exhausts its budget in the shared corner samples.
At `x = 0, y = 1`, the expression is `1`, not `0`. The regression suite includes
this concrete OES example, a real structural-hash collision, and a check that
sample differences beyond the bounded hash prefix remain distinguishable.

The documented upstream shift example is:

```text
(x << (y & 63)) ^ (x << y)
```

At `x = 1, y = 0x8000000000000000`, its bitvector value is `1`. Masking every
shift count incorrectly makes it `0`.

A contextual success case is `(x + ~x) + 1 -> 0`. A horizon can represent it
as `alpha + beta + 1`: that template is not zero for arbitrary independent
labels, but the original context relates them. The candidate is proved against
the original expression after restoration.

## Tests and build

Follow the root README's local BINSEC/Xyntia pinning instructions, then:

```sh
make
make test
```

`make test` requires an SMT backend and runs evaluator, parser, checker CLI,
and pipeline regressions. The pipeline tests use deterministic mock backends
to isolate acceptance behavior rather than depend on stochastic synthesis.

## Benchmark protocol

`scripts/audit_dataset.py` runs an explicit binary/configuration on JSON case
files/directories or raw ProMBA expression pairs and writes a flushed JSONL record for every
case plus a summary. The reported size is the repository's `size_of_expr` metric (extension and
restriction wrappers are excluded). The output is checked against the **original input**;
ground truth checking is optional and recorded separately. The checker first
looks for a concrete counterexample using 256 samples and then asks SMT for a
proof. It never converts unknown/timeout into success.

```sh
python3 scripts/audit_dataset.py --help
```

The harness records binary and configuration SHA-256, input provenance,
per-case exit/errors/timeouts, original and result sizes, strict decreases,
unchanged sizes, and expansions. External timeouts terminate the process group.
Results apply to the specified commit, configuration, and corpus, not to every
configuration in the publication. The friend's claimed 30% error rate requires
a specified corpus, configuration, and definition of error before it can be
compared directly.

## Dataset inventory

### Evaluated datasets

| Dataset | Counts and variants | Exact source |
|---|---|---|
| Synthetic MBA | 2,511 total: 1,008 Poly + 1,003 Non-Poly + 500 QSynth in both the downloaded exports and GreySynth artifact | [Poly](https://github.com/astean1001/ProMBA/blob/main/mbasolve_benchmark/backup/dataset_poly.txt), [Non-Poly](https://github.com/astean1001/ProMBA/blob/main/mbasolve_benchmark/backup/dataset_nonpoly.txt), [QSynth](https://github.com/astean1001/ProMBA/blob/main/qsynth_benchmark/backup/qsynth.txt) |
| MBA Loki | Upstream exports: 1,000 Loki + 500 Full-Loki. GreySynth artifact: 999 + 497 = 1,496 | [Loki](https://github.com/astean1001/ProMBA/blob/main/loki_benchmark/backup/loki.txt), [Full-Loki](https://github.com/astean1001/ProMBA/blob/main/loki_benchmark/backup/floki.txt) |
| C-MBA | 500 source expressions; Tigress levels 1–8, MBA-Obfuscator, OMVLL. OMVLL artifact has 488/500 | [GreySynth artifact](https://zenodo.org/records/22649859) |
| C-BeyondMBA | 500 source expressions; the archive contains Tigress levels 1–8 and 500 OMVLL cases. Main comparisons use Tigress level 5 and OMVLL. No MBA-Obfuscator variant | [GreySynth artifact](https://zenodo.org/records/22649859) |
| C-Full | Disjoint union of C-MBA and C-BeyondMBA: 1,000 source expressions, not an additional corpus. Tigress level 5 is used for ablations; combined OMVLL data contains 988 cases | [GreySynth artifact](https://zenodo.org/records/22649859) |

The source C expressions come from OpenSSL, BearSSL, Monocypher, FFTW, GMP,
SLEEF, libcanard, libevent, libuv, open62541, Quake, and SQLite.

The artifact is an 8,517,727,232-byte saved Docker/OCI image:
[direct download](https://zenodo.org/records/22649859/files/greysynth.tar?download=1).
Its dataset layer was fetched separately and verified against its SHA-256
`2f5574f45aabfa019f9db35c94582235073cf0173b85fe39c06d994c42818fc0`.
The complete image was not downloaded. The recovered dataset archive contains
63,337 regular files; `_sizes.json` metadata files are not extra benchmark cases.
Counts refer to the embedded `datasets.tar.zst`; the table scripts were recovered
from their Docker COPY layer. This was not a reconstruction of the image's
complete merged filesystem. [dataset-provenance.json](dataset-provenance.json)
records counts, revisions, hashes, and source URLs without embedding the datasets.

### Publication and artifact discrepancies

- The paper swaps the Poly and Non-Poly counts relative to both the exported
  ProMBA files and the archived GreySynth data; their combined total agrees.
- The archived Loki population omits four examples relative to the upstream
  exports. The archived OMVLL population omits twelve C-MBA examples.
- Table 3's caption says C-Full, while section 5.4 and the recovered table layout
  select C-MBA at Tigress levels 1–8.
- The paper's validity convention and archived `run_greysynth.py` count
  `equiv = "ukn"` as successful. These numbers are not proved-equivalence rates.
- Recovered table 2/3 layouts default to randomly selected 50-case runs and
  60-second timeouts. Those defaults do not reproduce the paper's complete
  one-hour-per-case experiments. The archive also uses the older
  `local_synthesis` configuration name; the current repository uses `chs`.

### Other referenced or bundled corpora

These are useful provenance or ancillary data, not extra GreySynth evaluation
sets to add to the totals above:

- [MBA-Solver full dataset](https://github.com/softsec-unh/MBA-Solver/tree/main/full-dataset)
  is the upstream origin of the polynomial/non-polynomial families; its linear
  family is also available there. The separate [demonstration subset](https://github.com/softsec-unh/MBA-Solver/tree/main/dataset)
  is not the complete corpus.
- [QSynth original datasets](https://github.com/werew/qsynth-artifacts/tree/master/datasets):
  `syntia`, `custom_EA`, `custom_VR_EA`, and `custom_EA_ED`, each with 500
  functions; the last execution trace is truncated to 293. The ProMBA export
  above identifies the 500-expression selection used by GreySynth.
- [Loki original MBA experiment](https://github.com/RUB-SysSec/loki/tree/main/experiments/experiment_10_mba_formula), also
  [archived on Zenodo](https://zenodo.org/records/6686932).
- Vendored Xyntia [B1/Syntia](https://github.com/binsec/greysynth/blob/master/outside_tools/xyntia/datasets/syntia/b1): 500.
  Xyntia credits the [original Syntia project](https://github.com/RUB-SysSec/syntia)
  and Tim Blazytko for this dataset.
- Vendored Xyntia [B2](https://github.com/binsec/greysynth/blob/master/outside_tools/xyntia/datasets/b2): 1,110.
- Vendored Xyntia [B2 with constants](https://github.com/binsec/greysynth/blob/master/outside_tools/xyntia/datasets/b2_combined): 1,110.
- [BP1/BP2/BP3 complex handlers](https://github.com/binsec/greysynth/tree/master/outside_tools/xyntia/datasets/complex_handlers): 45 expression lines total.
- [Merged conditional datasets 1–5](https://github.com/binsec/greysynth/tree/master/outside_tools/xyntia/datasets/if_the_else): 100 total.

## Scope

Proofs establish equivalence of parsed pure bitvector expressions. They do not
prove that a C/binary extraction was faithful, and they do not model memory
loads. The existing CIL return-expression frontend does not reconstruct general
control flow or assignments; that frontend remains outside this patch. Solver
resource limits can reduce simplification coverage; inconclusive results are
retained as such, and strict mode keeps the previous expression.

## Primary references

- [OCaml 5.3 Hashtbl hashing contract](https://ocaml.org/manual/5.3/api/Hashtbl.html).
- [GreySynth source](https://github.com/binsec/greysynth/tree/ec490c757d43b3b6de159be144e1b61277227ee8).
- [GreySynth archived artifact](https://zenodo.org/records/22649859).
- [ProMBA benchmark runner and sources](https://github.com/astean1001/ProMBA).
