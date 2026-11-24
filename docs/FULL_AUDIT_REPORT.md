# Full MBA Audit: ACM CCS 2026 Release vs. Proof-Coverage

## Executive summary

This is a full, zero-limit audit of the eight supplied external MBA corpora. The
files contain **7,011 parseable CSV rows**, not 7,010: the supplied
`qsynth_ea.csv` has **500** valid rows rather than the stated 499. No row was
removed to force the expected denominator.

The comparison is intentionally fail-closed:

- **BEFORE:** `ec490c757d43b3b6de159be144e1b61277227ee8`, the ACM CCS 2026
  release, checked against the original input and ground truth with the current
  independent `mba_equiv` checker. The release has no certificate export.
- **AFTER:** `196dacb6f2f2d1af26714029430c4ba83274a2a7`, with strict rewrite
  validation, AC normalization, bounded e-graph extraction, OES, and CHS. Every
  successfully processed AFTER row produced a certificate that independently
  replayed as `proved_compositional`.

Headline results:

- Established outputs rise from **3,739/7,011 (53.3%)** to
  **6,747/7,011 (96.2%)**.
- Unproved/error rows fall from **3,272** to **264**.
- The paper release emits **16 independently refuted outputs**. AFTER emits
  **zero refuted outputs**.
- Outputs at or below ground-truth size rise from **1,025** to **4,734**.
- Weak/still-obfuscated proved outputs fall from **2,536** to **546**.
- Aggregate established-case geometric quality (`output / GT`) improves from
  **7.0072x** to **1.4671x**. On the 3,737 cases established by both versions,
  it improves from **7.0095x** to **1.3329x**.
- AFTER has no checker unknowns or timeouts. Its 264 errors are input/runtime
  failures: 250 malformed Full-Loki rows, one malformed Loki row, and 13
  `Z.Overflow` crashes in the five-second PLDI Poly run.

The largest remaining opportunities are clear: make Full-Loki ingestible,
remove the PLDI Poly `Z.Overflow` crash path, add a large-DAG strategy beyond the
2,048-enode cap, extend nonlinear/multivariable decomposition, and recover the
excellent small expressions that the paper pipeline occasionally found on
Loki/QSynth without reintroducing unsound rewrites.

## Round 18 update

Round 18 implements the issues found by this audit and was rerun with the same
5-second producer / 20-second process / 2-second checker / 5-second proof
budgets. Raw R18 artifacts are under
`/tmp/greysynth-bench/full-audit-r18-verified/`; the final Non-Poly and linear
reruns, made after tightening the eager root-linear guard, are under
`/tmp/greysynth-bench/r18-final-{pldi_nonpoly,mba_obf_linear}/`.

R18 fixes every `Z.Overflow` case, adds an OES-first large-DAG path, proves
sample-constant roots immediately, groups equal-coefficient Boolean forms,
partitions nonlinear opaque components, and normalizes complement offsets. It
also creates the benchmarking-only `floki_sanitized.txt`, stripping exactly the
249 leading `}` characters while preserving the final unmatched-parenthesis row.

### Three-way master table

| Dataset | Established BEFORE / R17 / R18 | Solved BEFORE / R17 / R18 | Meaningful BEFORE / R17 / R18 | Weak BEFORE / R17 / R18 | Unproved BEFORE / R17 / R18 | Geomean `out/GT` BEFORE / R17 / R18 |
|---|---:|---:|---:|---:|---:|---:|
| PLDI Non-Poly | 23 / 1,003 / **1,003** | 6 / 610 / 559 | 2 / 369 / **444** | 15 / 24 / **0** | 980 / 0 / 0 | 3.1847 / **1.4197** / 1.5530 |
| PLDI Poly | 423 / 995 / **1,008** | 1 / 654 / 600 | 0 / 277 / **331** | 422 / 64 / 77 | 585 / 13 / **0** | 4.5408 / **1.0345** / 1.0802 |
| MBA-Obf nonlinear | 399 / 1,000 / **1,000** | 0 / 584 / **691** | 16 / 128 / **255** | 383 / 288 / **54** | 601 / 0 / 0 | 11.1989 / 1.8849 / **1.0482** |
| QSynth EA | 165 / 500 / **500** | 152 / **252** / 252 | 11 / **221** / 199 | **2** / 27 / 49 | 335 / 0 / 0 | **0.4790** / 1.3908 / 1.5092 |
| msimba | 999 / 1,000 / **1,000** | 0 / 1,000 / **1,000** | 0 / 0 / 0 | 999 / 0 / 0 | 1 / 0 / 0 | 37.9199 / **0.9997** / **0.9997** |
| Loki | 789 / 999 / **999** | 680 / 758 / **776** | 109 / 120 / 88 | 0 / 121 / 135 | 211 / 1 / 1 | **1.0873** / 3.4392 / 3.0472 |
| Raw Full-Loki | 209 / 250 / **250** | 176 / **201** / 198 | 32 / 27 / **28** | **1** / 22 / 24 | 291 / 250 / 250 | **1.1160** / 2.2037 / 2.2416 |
| MBA-Obf linear | 732 / 1,000 / **1,000** | 10 / 675 / **680** | 8 / 325 / 320 | 714 / 0 / 0 | 268 / 0 / 0 | 16.4443 / 0.9710 / **0.9161** |
| **Raw total** | **3,739 / 6,747 / 6,760** | **1,025 / 4,734 / 4,756** | **178 / 1,467 / 1,665** | **2,536 / 546 / 339** | **3,272 / 264 / 251** | **7.0072 / 1.4671 / 1.3441** |

R18 therefore adds 13 established rows (the former PLDI Poly crashes), moves 207
proved rows out of the weak bucket, and improves aggregate geometric quality
from 1.4671x to 1.3441x. The trade-off is visible: some formerly “solved” rows
move to the broader meaningful bucket under the stricter soft-budget schedule,
particularly Non-Poly and PLDI Poly. This is a quality regression, not a
soundness regression; all 6,760 parseable R18 outputs replay or prove, with zero
refutations/unknowns/timeouts in the final protocol.

### Targeted R18 results

- All 13 former PLDI Poly `Z.Overflow` rows now complete and prove; 12 are at or
  below GT, while row 672 is size 51 versus GT 23.
- QSynth rows 163/393/288 move `192/47/33 -> 1/1/1`.
- Loki rows 993/548/792 move `10,915/8,901/8,268 -> 3/3/3`.
- Nonlinear rows 949/911 move `148/120 -> 3/3` (`6*y`, `11*y`).
- Non-Poly rows 984/938 move `69/68 -> 4/5`.
- Linear rows 788/973 move `63/37 -> 7/4`; an eight-worker repeated contention
  fixture reproduces these sizes 8/8 times for each case.
- Raw Full-Loki row 371 moves `851 -> 3`; row 433 is size 7 in the full
  eight-worker audit and size 3 in an isolated focused run.

### Sanitized Full-Loki

The sanitized file still has 500 CSV rows, of which 499 parse successfully and
one retains the upstream unmatched parenthesis. Results are:

| Cases | Established | Solved | Meaningful | Weak | Error | Geomean `out/GT` | Median compression |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 500 | **499** | **409** | 53 | 37 | 1 | **1.3307x** | **196.33x** |

This confirms that raw Full-Loki's 250-error result is almost entirely an input
format defect: stripping only the 249 stray leading braces raises established
coverage from 250 to 499 without changing parser semantics.

## Methodology and provenance

### Commits and binaries

| Component | Provenance | SHA-256 |
|---|---|---|
| BEFORE GreySynth | `ec490c757d43b3b6de159be144e1b61277227ee8` | `d42a0072b1afd0f7f062c3df903f92f3dc08d5d63c2699b497f36fcf6000a9b8` |
| AFTER GreySynth | `196dacb6f2f2d1af26714029430c4ba83274a2a7` | `948f224c3c12697931139796d4e5128e57007c97fb0facea4d60bf06c0de331b` |
| `mba_equiv` | built from `196dacb` | `72934a1768593650febf7056788dd87424cc1d08de728db61e58efe047049f4f` |
| `mba_proof` | built from `196dacb` | `d562b20a5a926aa8f114125a87824bbd0f1366f12319caa6f97a55d425bfd764` |

The paper tree was exported with `git archive ec490c7` into
`/tmp/greysynth-paper-release` and built with an isolated
`DUNE_BUILD_DIR=/tmp/greysynth-paper-build`. The current working tree was not
checked out or modified.

### Dataset inventory

| Dataset | Audited rows | File SHA-256 |
|---|---:|---|
| PLDI Non-Poly | 1,003 | `af1a572b5f6e44336aba1fbc9e9dfec036440ba0165e4555968cfed24f864e70` |
| PLDI Poly | 1,008 | `7d8ffe5aa2447465114d22298c3d546abab3d396f109b6c2bac4ed4bb3212f44` |
| MBA-Obfuscator nonlinear | 1,000 | `1bc2cb8d7a3e14c615018e17ac6e503708801755097dd3cb5087047dd255e241` |
| QSynth EA | **500** | `faf7477d9153ba9de5b869c1aaf96b5899281df6f667d60b06a3c1d77b502f2e` |
| msimba | 1,000 | `e140128b15b911b1494b907f958ecc56ec144f4294e7ea73f1cb5e2b89f0befb` |
| Loki | 1,000 | `2fe5f4efe48d96a3f128c8d23c419001bc520c64625c736bc36860656c9a77fc` |
| Full-Loki (`floki`) | 500 | `d162af52e4cc7cac21aabfbd541345af6190daf8628dee5afa78009f827530f2` |
| MBA-Obfuscator linear | 1,000 | `93d2d1c12aab180acffab21a93ba0ea9e1117128fdb3b25caa40888721fb19e6` |
| **Total** | **7,011** | — |

### Budgets and configurations

Both versions used the same per-case limits:

- GreySynth `total_timeout = 5`
- synthesis timeout/repeat: `1` second / `1`
- producer equivalence timeout: `1` second
- audit process hard timeout: `20` seconds
- independent sampling: 256 assignments
- independent SMT timeout: `2` seconds
- raw width: 64 bits
- ground-truth checking enabled

AFTER additionally used independent certificate replay with a 5-second
per-obligation retry budget and a 90-second verifier process cap.

BEFORE used the paper pipeline (`OES -> CHS`) and its release setting
`reject_non_equiv_simplifications=false`; this is essential for measuring the
published behavior, and the independent checker catches unsafe outputs. AFTER
used:

```json
{
  "normalization": true,
  "ac_normalization": true,
  "egraph_extraction": true,
  "egraph_max_enodes": 2048,
  "egraph_max_iters": 4,
  "oes": true,
  "chs": true,
  "reject_non_equiv_simplifications": true,
  "total_timeout": 5,
  "synthesis_timeout": 1,
  "equiv_timeout": 1
}
```

Config hashes are `4c28dc...99c6` (BEFORE) and `5a496e...e5940` (AFTER).
The first four BEFORE datasets ran at four workers before the resource update;
remaining BEFORE datasets ran at ten workers. AFTER ran at eight workers. Worker
count changes throughput/contention only; all per-case and independent-checker
budgets above are identical. Contention failures would have been isolated and
rerun, but neither audit produced process-timeout verdicts.

Representative command templates (there was **no `--limit`**):

```sh
# BEFORE
python3 scripts/audit_dataset.py \
  --binary /tmp/greysynth-paper-build/default/src/greysynth/greysynth_cli.exe \
  --checker /home/opam/greysynth-build/default/src/tooling/analysis/mba_equiv.exe \
  --config /tmp/greysynth-bench/full-audit-before-config.json \
  --dataset /tmp/greysynth-bench/external/DATASET \
  --output /tmp/greysynth-bench/full-audit-before/NAME/out.jsonl \
  --workers WORKERS --timeout 20 --samples 256 --smt-timeout 2 \
  --raw-bitwidth 64 --check-ground-truth

# AFTER
python3 scripts/audit_dataset.py \
  --binary /home/opam/greysynth-build/default/src/greysynth/greysynth_cli.exe \
  --checker /home/opam/greysynth-build/default/src/tooling/analysis/mba_equiv.exe \
  --proof-checker /home/opam/greysynth-build/default/src/tooling/analysis/mba_proof.exe \
  --config /tmp/greysynth-bench/full-audit-after-config.json \
  --dataset /tmp/greysynth-bench/external/DATASET \
  --output /tmp/greysynth-bench/full-audit-after/NAME/out.jsonl \
  --certificate-dir /tmp/greysynth-bench/full-audit-after/NAME/certificates \
  --workers 8 --timeout 20 --samples 256 --smt-timeout 2 \
  --proof-timeout 5 --proof-process-timeout 90 --raw-bitwidth 64 \
  --check-ground-truth
```

Raw JSONL and summaries remain under
`/tmp/greysynth-bench/full-audit-{before,after}/`.

## Classification

Rows are classified only after a successful independent proof (`proved` or
`proved_compositional`):

- **Solved:** `output_size <= ground_truth_size`.
- **Meaningfully shrunk:** output is above GT, but either input-to-output shrink
  is at least 50%, or output is at most `2 * GT`.
- **Weak / still obfuscated:** proved output remains above `2 * GT` and shrank
  by less than 50%.
- **Unproved:** refuted, unknown, timeout, error, malformed output, or missing
  dimensions. Finite sample agreement is never counted as proof.

Quality uses Legacy AST cost `output / GT`; compression uses Legacy cost
`input / output`. Metrics include established rows only. Because AFTER proves
3,008 additional rows, its all-established quality population is much broader;
the matched-cohort metric is reported separately where useful.

## Master comparison

### Soundness and proof coverage

| Dataset | Cases | BEFORE proved | BEFORE refuted | BEFORE unknown | BEFORE error | AFTER proved | AFTER refuted | AFTER unknown/timeout | AFTER error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| PLDI Non-Poly | 1,003 | 23 | 0 | 980 | 0 | **1,003** | 0 | 0 | 0 |
| PLDI Poly | 1,008 | 423 | 0 | 585 | 0 | **995** | 0 | 0 | 13 |
| MBA-Obf nonlinear | 1,000 | 399 | **1** | 598 | 2 | **1,000** | 0 | 0 | 0 |
| QSynth EA | 500 | 165 | **12** | 323 | 0 | **500** | 0 | 0 | 0 |
| msimba | 1,000 | 999 | **1** | 0 | 0 | **1,000** | 0 | 0 | 0 |
| Loki | 1,000 | 789 | **1** | 209 | 1 | **999** | 0 | 0 | 1 |
| Full-Loki | 500 | 209 | **1** | 40 | 250 | **250** | 0 | 0 | 250 |
| MBA-Obf linear | 1,000 | 732 | 0 | 266 | 2 | **1,000** | 0 | 0 | 0 |
| **Total** | **7,011** | **3,739** | **16** | **3,001** | **255** | **6,747** | **0** | **0** | **264** |

All **6,747** non-error AFTER cases have a separately replayed compositional
certificate, including the 1,443 cases where direct whole-expression SMT also
proved equivalence.

The 16 paper-release soundness failures are:

- `mba_obf_nonlinear/line_0000761`
- `qsynth_ea/line_0000033`, `89`, `92`, `99`, `120`, `132`, `148`, `158`,
  `252`, `294`, `343`, `350`
- `msimba/line_0000002`
- `loki/line_0000265`
- `floki/line_0000377`

These are checker refutations, not proof timeouts. For example, paper Loki row
265 returns a size-6 expression for a size-2,937 input, but the independent
checker refutes it; msimba row 2 returns size 119 and is also refuted. AFTER
returns proved expressions for both.

### Quality and compression

| Dataset | Solved B→A | Meaningful B→A | Weak B→A | Unproved B→A | Geomean quality B→A | Median compression B→A | Mean compression B→A |
|---|---:|---:|---:|---:|---:|---:|---:|
| PLDI Non-Poly | 6 → **610** | 2 → **369** | 15 → **24** | 980 → **0** | 3.1847x → **1.4197x** | 1.22x → **28.78x** | 10.06x → **45.54x** |
| PLDI Poly | 1 → **654** | 0 → **277** | 422 → **64** | 585 → **13** | 4.5408x → **1.0345x** | 1.03x → **3.71x** | 1.06x → **4.11x** |
| MBA-Obf nonlinear | 0 → **584** | 16 → **128** | 383 → **288** | 601 → **0** | 11.1989x → **1.8849x** | 1.06x → **11.92x** | 1.19x → **13.45x** |
| QSynth EA | 152 → **252** | 11 → **221** | 2 → **27** | 335 → **0** | **0.4790x** → 1.3908x | **12.58x** → 7.40x | **58.75x** → 23.60x |
| msimba | 0 → **1,000** | 0 → 0 | 999 → **0** | 1 → **0** | 37.9199x → **0.9997x** | 1.19x → **45.80x** | 1.19x → **45.27x** |
| Loki | 680 → **758** | 109 → **120** | 0 → 121 | 211 → **1** | **1.0873x** → 3.4392x | **368.0x** → 298.0x | **497.0x** → 380.1x |
| Full-Loki | 176 → **201** | 32 → 27 | 1 → 22 | 291 → **250** | **1.1160x** → 2.2037x | **210.0x** → 186.5x | **259.4x** → 227.7x |
| MBA-Obf linear | 10 → **675** | 8 → **325** | 714 → **0** | 268 → **0** | 16.4443x → **0.9710x** | 1.07x → **13.37x** | 1.23x → **24.99x** |
| **Total** | **1,025 → 4,734** | **178 → 1,467** | **2,536 → 546** | **3,272 → 264** | **7.0072x → 1.4671x** | **1.19x → 17.29x** | **122.83x → 86.25x** |

The mean compression decrease is not contradictory: BEFORE's mean is dominated
by a small established subset of enormous Loki expressions, whereas AFTER
establishes almost every parseable case. On the 3,737 cases established by both
versions, geometric quality improves from **7.0095x to 1.3329x**.

### Paired transitions

“New solved/meaningful” means the BEFORE row was in a different bucket.
Regressions compare output size only on rows independently established by both
versions; they are quality regressions, not soundness failures.

| Dataset | New solved | New meaningful | Both established | AFTER smaller / equal / larger |
|---|---:|---:|---:|---:|
| PLDI Non-Poly | 604 | 369 | 23 | 18 / 5 / 0 |
| PLDI Poly | 653 | 277 | 421 | 420 / 1 / 0 |
| MBA-Obf nonlinear | 584 | 125 | 399 | 357 / 4 / 38 |
| QSynth EA | 123 | 218 | 165 | 48 / 90 / 27 |
| msimba | 1,000 | 0 | 999 | 999 / 0 / 0 |
| Loki | 159 | 109 | 789 | 91 / 599 / 99 |
| Full-Loki | 50 | 26 | 209 | 31 / 150 / 28 |
| MBA-Obf linear | 665 | 323 | 732 | 724 / 7 / 1 |

## Per-dataset diagnostics

### 1. PLDI Non-Poly (1,003)

**Buckets:** BEFORE `6 solved / 2 meaningful / 15 weak / 980 unproved`;
AFTER `610 / 369 / 24 / 0`. AFTER newly establishes all 980 previously unknown
rows; 604 cases newly reach `<= GT`. Among the 23 cases proved by both, AFTER is
smaller on 18, equal on 5, and larger on 0.

**Spotlight wins:**

- row 862: size `470`, BEFORE `161`, AFTER `3` (`y & a`), GT `5`.
- row 706: `445 -> 274 -> 8`, exactly GT.
- row 868: `411 -> 89 -> 3`, versus GT `16`.
- row 322: `461 -> 169 -> 6`, versus GT `8`.
- row 657: `383 -> 223 -> 8`, exactly GT.

**Remaining targets:** rows 984 (`102 -> 69`, GT 6), 938 (`96 -> 68`, GT 6),
942 (`99 -> 64`, GT 6), and 967 (`93 -> 60`, GT 6). These residuals combine
many Boolean atoms with arithmetic coefficients and nonlinear `x*y` terms. The
six-atom truth-table ceiling and local connected-component decomposition are the
main limits. Highest-impact next work: multivariable bit slicing and scalable
component decomposition beyond six atoms.

### 2. PLDI Poly (1,008)

**Buckets:** BEFORE `1 / 0 / 422 / 585`; AFTER `654 / 277 / 64 / 13`.
AFTER newly reaches `<= GT` on 653 rows. Of 421 rows proved by both, AFTER is
smaller on 420 and equal on one; there are no size regressions.

**Spotlight wins:**

- row 992: `246 -> 239 -> 8`, GT 10.
- row 1007: `250 -> 240 -> 9`, GT 11.
- row 1000: `241 -> 234 -> 13`, GT 15.
- row 970: `238 -> 234 -> 21`, GT 23.
- row 990: `236 -> 228 -> 15`, GT 13 (large reduction, but still slightly above GT).

**Remaining targets:** the most important issue is not algebraic quality but 13
runtime errors (rows 92, 111, 144, 156, 193, 252, 260, 430, 466, 563, 627,
655, 672). Each terminates with `Fatal error: exception Z.Overflow` after a CHS
rewrite. This should be fixed before further quality tuning. Among successful
rows, 64 remain weak; rows 1006, 893, 904, 913, and 785 produce size 55–57 for
GT 12. They are dense degree-two/three sums with overlapping nonlinear
monomials. Priorities: make post-CHS arithmetic exception-safe, then add bounded
multivariate polynomial basis/factor selection.

### 3. MBA-Obfuscator nonlinear (1,000)

**Buckets:** BEFORE `0 / 16 / 383 / 601`; AFTER `584 / 128 / 288 / 0`.
AFTER newly solves 584 rows and proves every row. On the 399 jointly proved
rows, AFTER is smaller on 357, equal on 4, and larger on 38.

**Spotlight wins:**

- row 136: `126 -> 122 -> 3` (`x + 2`), GT 15.
- row 694: `149 -> 117 -> 3`, GT 4.
- row 520: `111 -> 92 -> 3`, GT 13.
- row 910: `146 -> 117 -> 4`, exactly GT.
- row 331: `143 -> 141 -> 5`, versus GT 12.

**Remaining targets:** rows 949 (`180 -> 148`, GT 3), 911 (`130 -> 120`, GT
3), 687 (`141 -> 111`, GT 3), 988 (`156 -> 134`, GT 4), and 861 (`147 ->
130`, GT 4). These contain deep products of overlapping Boolean minterms, so a
single factor-group choice does not expose the global cancellation. Add beam
search over factor partitions, null products over disjoint minterms, and
multivariable nonlinear bit slicing. The worst jointly proved regressions are
rows 963 (`62 -> 117`), 930 (`63 -> 118`), and 924 (`71 -> 120`); whole-pipeline
portfolio extraction should retain the smaller paper result when it is proved.

### 4. QSynth EA (500)

**Buckets:** BEFORE `152 / 11 / 2 / 335`; AFTER `252 / 221 / 27 / 0`.
AFTER establishes all 500 and newly reaches `<= GT` on 123 rows. Among 165
jointly proved rows, AFTER is smaller on 48, equal on 90, and larger on 27.

**Spotlight wins:**

- row 425: `2,593 -> 449 -> 15`, GT 21.
- row 195: `164 -> 98 -> 16`, exactly GT.
- row 219: `380 -> 218 -> 52`, GT 16.
- row 327: `490 -> 418 -> 124`, GT 13.
- row 187 was previously unknown and now proves as `1,055 -> 3` (`v4*v4`).

**Remaining targets:** rows 442 (`845 -> 693`, GT 16), 34 (`1,385 -> 817`, GT
20), 461 (`1,305 -> 641`, GT 18), 356 (`949 -> 542`, GT 18), and 27 (`929 ->
539`, GT 19). These are 4–5-variable nonlinear expressions with repeated
products and deeply correlated Boolean/arithmetic subterms; five seconds is
frequently consumed before high-value roots are normalized. Priorities:
multivariable slicing, repeated-class extraction across nonlinear parents, and a
larger-node e-graph schedule. The paper release has unusually strong quality on
its small proved subset (0.4790x); regressions include rows 163 (`1 -> 192`), 393
(`1 -> 47`), and 288 (`1 -> 33`). A proof-aware baseline/modern whole-pipeline
portfolio would recover these wins safely.

### 5. msimba (1,000)

**Buckets:** BEFORE `0 solved / 0 meaningful / 999 weak / 1 refuted`; AFTER
**1,000 solved**. Every row is proved and at or below GT.

**Spotlight wins:** rows 895, 779, 694, 486, and 116 all move from paper outputs
around size 210–211 to size 5 affine/XOR forms. Row 2, the paper release's one
refuted output (`165 -> 119`), becomes a proved size-5 mask/XOR expression.

**Remaining targets:** none under the requested buckets. This corpus is
saturated at the current metric. Future work should be regression protection,
not additional msimba-specific rules.

### 6. Loki (1,000)

**Buckets:** BEFORE `680 / 109 / 0 / 211`; AFTER `758 / 120 / 121 / 1`.
AFTER establishes 999 parseable rows and newly reaches `<= GT` on 159 rows.
There is one malformed source row (`line_0001001`, `Expected )`). On 789 jointly
proved rows, AFTER is smaller on 91, equal on 599, and larger on 99.

**Spotlight wins:**

- row 919: input 8,836, previously unknown, now size 3 (`y+x`), exactly GT.
- row 411: `5,382 -> 3`, newly proved, exactly GT.
- row 236: `4,356 -> 3`, newly proved, exactly GT.
- row 617: `3,826 -> 3`, newly proved, exactly GT.
- row 802: paper 13, AFTER 3 (`x^y`), exactly GT.

**Remaining targets:** rows 993 (`11,480 -> 10,915`, GT 3), 548 (`9,600 ->
8,901`, GT 3), 303 (`8,887 -> 8,648`, GT 3), 792 (`9,841 -> 8,268`, GT 3),
and 781 (`8,206 -> 8,206`, GT 3). These giant trees exceed the 2,048-enode
e-graph guard and leave little of the five-second budget after traversal. The
next optimization should be DAG hash-consing before cost accounting, repeated
subtree factoring, and region/e-class saturation rather than whole-root
fallback. Important regression warning: the paper release already proves size-3
answers on rows 993/548/792, while AFTER returns thousands of nodes. Safe
whole-pipeline portfolio retention is high impact here.

### 7. Full-Loki / `floki` (500)

**Buckets:** BEFORE `176 / 32 / 1 / 291`; AFTER `201 / 27 / 22 / 250`.
Of the 250 parseable AFTER rows, all are proved; 50 cases newly reach `<= GT`.
However, **249 source rows begin with an extraneous `}`** and one final row has
an unmatched parenthesis. Both versions reject those same 250 rows, so the
headline 50% error rate is primarily a dataset-ingestion problem, not a solver
failure.

**Spotlight wins:**

- row 260: input 2,716, previously unknown, AFTER size 3 (`x+y`).
- row 465: `1,824 -> 3`, newly proved.
- row 446: `1,297 -> 3`, newly proved.
- row 416: `1,241 -> 7 -> 3`.
- row 390: `623 -> 392 -> 19`, GT 3.

**Remaining targets:** first sanitize/repair the 250 malformed records and rerun;
this doubles the usable denominator immediately. On valid rows, targets include
433 (`1,563 -> 1,369`, GT 3), 280 (`1,307 -> 1,307`, GT 3), 435 (`1,970 ->
988`, GT 3), 371 (`915 -> 851`, GT 3), and 374 (`934 -> 834`, GT 3). They share
Loki's deep nested negation, shifts, and repeated subtrees and need the same
large-DAG regional saturation. There are 28 size regressions among jointly
proved rows; rows 433 (`3 -> 1,369`) and 371 (`3 -> 851`) are the highest-impact
portfolio misses.

### 8. MBA-Obfuscator linear (1,000)

**Buckets:** BEFORE `10 / 8 / 714 / 268`; AFTER `675 / 325 / 0 / 0`. AFTER
proves every row, newly reaches `<= GT` on 665 rows, and eliminates every weak
case. Among 732 jointly proved rows it is smaller on 724, equal on 7, and larger
on only one (row 5, `11 -> 12`).

**Spotlight wins:**

- row 993: `993 -> 925 -> 3`, exactly GT.
- row 681: `397 -> 373 -> 2`, versus GT 4.
- row 1000: `968 -> 907 -> 5`, versus GT 7.
- row 763: `570 -> 536 -> 3`, versus GT 17.
- row 732: `536 -> 495 -> 3`, versus GT 5.

**Remaining targets:** there are no weak or unproved outputs. The 325 meaningful
rows are the remaining quality tier; worst ratios include row 973 (`932 -> 37`,
GT 4), 788 (`613 -> 63`, GT 7), 998 (`993 -> 59`, GT 7), 947 (`890 -> 65`, GT
8), and 873 (`766 -> 65`, GT 8). These are mostly three-variable minterm sums.
Connected-component scaling and multivariable bit-sliced affine recovery should
move them from “meaningful” to solved.

## Prioritized next work after R18

1. **Safe cross-pipeline portfolio:** R18 removes the catastrophic Loki misses,
   but QSynth, Loki, and Full-Loki still contain rows where the paper pipeline
   found a smaller independently proved result. Retain the minimum proved whole
   pipeline, not merely the minimum local candidate.
2. **Large-DAG regional extraction:** Loki still has 135 weak rows and sanitized
   Full-Loki has 37. Regional saturation/DAG factoring is still needed beyond
   OES-first collapse.
3. **Recover solved-count regressions:** R18 improves aggregate quality and weak
   counts but moves some R17 solved Non-Poly/PLDI-Poly rows into “meaningful.”
   Race the old and new schedules under one proof journal.
4. **Extend grouped reconstruction below the 600-node eager threshold:** the
   current guard is deliberately conservative to avoid uninterruptible work;
   make candidate generation cooperatively deadline-aware so more of the 320
   remaining meaningful linear cases benefit.
5. **Sanitized corpus provenance:** keep reporting raw Full-Loki, but publish the
   exact 249-line sanitation manifest and investigate the final unmatched row
   upstream.

The central conclusion remains two-sided: R18 is fully fail-closed, removes all
valid-input crashes, and materially improves aggregate quality, while a
proof-gated whole-pipeline portfolio is still required to combine the best local
minima of R17/R18 and the paper pipeline.
