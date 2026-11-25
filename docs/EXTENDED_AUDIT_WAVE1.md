# Extended Audit — Wave 1

## Executive summary

Wave 1 audits **18,995 cases across 19 suites**, with no `--limit`, using the
current proof-carrying GreySynth pipeline at `a202663` (code baseline
`3f856ab`). Every accepted rewrite is checked against its original input by
`mba_equiv` and independently replayed with `mba_proof`.

Raw parallel results:

- **Part A — GreySynth C variants:** 9,465/9,488 established, zero refutations,
  19 timeouts, 2 unknowns, and 2 parse errors.
- **Part B — CoBRA/external:** 9,492/9,507 established, zero refutations or
  checker unknowns, with 3 timeouts and 12 OSES syntax errors.
- **Combined:** **18,957/18,995 established (99.80%)**, zero refutations,
  22 timeouts, 2 unknowns, and 14 errors.

Every failed or inconclusive raw case was rerun at one worker. Isolated reruns
recover eight Part-A cases and one OSES case. The remaining 29 cases are
reproducible: 15 Part-A cases (13 hard timeouts and two invalid OMVLL
restriction expressions) and 14 OSES cases (12 unsupported-syntax parse errors
and two hard timeouts). The isolated aggregate is therefore
**18,966/18,995 established (99.85%)**, with zero refutations.

The main optimization finding is not a subtle peephole gap: polynomial and very
large C expressions cross existing complexity guards by orders of magnitude.
`univariate64` and `multivariate64` are almost entirely unchanged, and Tigress
quality degrades monotonically with obfuscation level even though proof coverage
stays near 100%.

## Provenance and protocol

- Repository HEAD: `a202663a1f4f1b8770b614498fc4eb35417cb68c`
- Implementation commit: `3f856ab` (Round-18 code); `a202663` adds review/docs.
- GreySynth binary SHA-256:
  `e5c1ba4f0ea10ff5c4f365c65ff3e5e0811722a2f76fb453cf6bf8981007c346`
- `mba_equiv` SHA-256:
  `d95a72dc395430a3509d43fbf5716195913754cc0b0f8d24c092bb53b7a965a9`
- `mba_proof` SHA-256:
  `830a82b9e3ab6439e8fca3102a4d42798b461ec02cbb949c38cb907339439141`
- Config SHA-256:
  `5a496ef347d727919af7d33f066afb9d0dfd72092efbc20d608fb8734b5e5940`

The exact R18 config enables normalization, AC normalization, bounded e-graph
extraction, OES, CHS, and strict proof rejection, with:

```text
total_timeout=5, synthesis_timeout=1, equiv_timeout=1
```

Audit process settings:

```text
--timeout 20 --smt-timeout 2 --proof-timeout 5
--proof-process-timeout 90 --raw-bitwidth 64 --check-ground-truth
```

Normal suites use eight workers. OMVLL and Tigress levels 7/8 use four workers.
No run used `--limit`. Raw artifacts are retained under:

```text
/tmp/greysynth-bench/wave1-r18/part-a/
/tmp/greysynth-bench/wave1-r18/part-b/
/tmp/greysynth-bench/wave1-r18/isolated-reruns/
```

Representative command:

```sh
python3 scripts/audit_dataset.py \
  --binary /home/opam/greysynth-build/default/src/greysynth/greysynth_cli.exe \
  --checker /home/opam/greysynth-build/default/src/tooling/analysis/mba_equiv.exe \
  --proof-checker /home/opam/greysynth-build/default/src/tooling/analysis/mba_proof.exe \
  --config /tmp/greysynth-bench/full-audit-after-config.json \
  --dataset DATASET --output OUTPUT --certificate-dir CERTS \
  --workers 8 --timeout 20 --samples 256 --smt-timeout 2 \
  --proof-timeout 5 --proof-process-timeout 90 --raw-bitwidth 64 \
  --check-ground-truth
```

### Temporary format conversions

No source dataset was modified.

- `mba_flatten.txt` contains 3,000 logical cases. Its first 2,060 rows have two
  columns, later sections add diagnostic subexpression columns (3/5/6 columns).
  `/tmp/greysynth-bench/wave1-input/mba_flatten.csv` selects the documented
  first two fields (`complex,groundtruth`) for every row.
- OSES is tab-separated. Its 479 rows were CSV-quoted into
  `/tmp/greysynth-bench/wave1-input/oses_all.csv`.

## Classification

Only `proved` and `proved_compositional` rows enter quality buckets:

- **Solved:** output size is at or below ground-truth size.
- **Meaningful:** output remains above GT, but is at most 2x GT or shrinks input
  by at least 50%.
- **Weak:** proved, above 2x GT, and shrinks input by less than 50%.
- **Unclassified/unproved:** no proof, runtime/parse failure, or unavailable GT
  dimensions.

Quality is the geometric mean of Legacy `output / GT`; compression is the
median Legacy `input / output`. Wall time is elapsed suite time, not summed case
CPU time.

## Part A — GreySynth C variants

| Suite | Cases | Est. (direct+comp) | Refuted | Unknown/timeout | Error | Strict | Unchanged | Solved | Meaningful | Weak | Geomean out/GT | Median compression | Wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C-MBA-Obfuscator | 500 | 499 (130+369) | 0 | 1 | 0 | 462 | 37 | 17 | 19 | 463 | 143.1640x | 1.06x | 617.0s |
| C-OMVLL | 988 | 976 (660+316) | 0 | 10 | 2 | 923 | 53 | 629 | 258 | 89 | 3.0323x | 13.40x | 1,390.9s |
| Tigress L1 | 1,000 | 1,000 (796+204) | 0 | 0 | 0 | 972 | 28 | 852 | 115 | 33 | 0.9905x | 4.22x | 418.0s |
| Tigress L2 | 1,000 | 1,000 (761+239) | 0 | 0 | 0 | 971 | 29 | 653 | 289 | 58 | 1.5227x | 9.00x | 565.3s |
| Tigress L3 | 1,000 | 999 (716+283) | 0 | 1 | 0 | 978 | 22 | 500 | 433 | 66 | 2.7941x | 15.67x | 672.8s |
| Tigress L4 | 1,000 | 1,000 (709+291) | 0 | 0 | 0 | 976 | 24 | 429 | 495 | 76 | 5.1238x | 28.40x | 713.2s |
| Tigress L5 | 1,000 | 999 (765+234) | 0 | 1 | 0 | 973 | 27 | 424 | 489 | 86 | 9.1403x | 78.25x | 738.0s |
| Tigress L6 | 1,000 | 996 (740+256) | 0 | 4 | 0 | 943 | 53 | 403 | 513 | 80 | 12.0572x | 61.03x | 782.7s |
| Tigress L7 | 1,000 | 1,000 (697+303) | 0 | 0 | 0 | 954 | 46 | 390 | 521 | 89 | 15.1451x | 197.30x | 1,613.8s |
| Tigress L8 | 1,000 | 996 (712+284) | 0 | 4 | 0 | 926 | 70 | 369 | 488 | 139 | 33.4688x | 373.84x | 2,109.7s |
| **Total** | **9,488** | **9,465 (6,686+2,779)** | **0** | **21** | **2** | **9,078** | **389** | **4,666** | **3,620** | **1,179** | **6.3768x** | **13.40x** | **9,621.4s** |

Raw solved/meaningful/weak counts sum to established cases. The 23 unresolved
raw rows are excluded from those buckets.

### C-MBA vs. C-BeyondMBA

The classification manifests cover all target names across the ten C variants:

| Class | Cases | Established | Unknown/timeout | Error | Solved | Meaningful | Weak | Geomean out/GT | Median compression |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C-MBA | 4,988 | 4,968 | 20 | 0 | 1,953 | 2,031 | 984 | 12.9403x | 9.81x |
| C-BeyondMBA | 4,500 | 4,497 | 1 | 2 | 2,713 | 1,589 | 195 | 2.9179x | 19.00x |

C-MBA is substantially harder by output quality despite containing fewer parse
failures. C-BeyondMBA has better solved coverage but contains the two malformed
OMVLL restrictions.

### Isolated reruns

The raw run's 23 unresolved rows were rerun at one worker:

- Recovered: C-MBA-Obfuscator `target_366`, OMVLL `target_2246`, Tigress L3/L5
  `target_1568`, Tigress L6 `target_5068`, and three of four Tigress L8 cases.
- Persistent OMVLL: nine hard process timeouts plus two parse errors
  (`target_5052`, `target_6860`: restriction bounds outside operand width).
- Persistent Tigress: L6 targets 2327/2328/2491 and L8 target 4174 time out even
  at one worker.

After isolated reruns, Part A is **9,473/9,488 established**; persistent failures
are 13 timeouts and two malformed expressions. No case is refuted.

### Scaling trend and concrete targets

Proof coverage stays high while quality degrades sharply with Tigress level:
0.9905x at L1, 5.1238x at L4, 15.1451x at L7, and 33.4688x at L8. Compression
rises because the inputs grow faster than outputs; that should not be mistaken
for reaching GT.

Highest-impact examples:

- `mba_obfuscator/target_3218`: input/output 54,904, GT 5 (no reduction).
- `mba_obfuscator/target_1417`: 51,922 unchanged, GT 5.
- `tigress_lvl_5/target_5857`: 186,155 -> 93,077, GT 7.
- `tigress_lvl_7/target_4174`: 1,007,670 unchanged, GT 13.
- `tigress_lvl_8/target_4174`: persistent hard timeout in isolated replay.
- `tigress_lvl_3` and `tigress_lvl_5` `target_1568`: raw replay inconclusive,
  but isolated replay proves both.

The dominant root cause is giant repeated DAG-shaped syntax presented as trees:
OES yields good compression, but the 2,048-enode e-graph guard and five-second
budget cannot reach the small GT forms. Priorities are structural DAG sharing,
regional e-graph saturation, and reusable cross-target rules for the repeated
Tigress templates.

## Part B — CoBRA and external suites

| Suite | Cases | Est. (direct+comp) | Refuted | Unknown/timeout | Error | Strict | Unchanged | Solved | Meaningful | Weak | Geomean out/GT | Median compression | Wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| GAMBA MBA-Flatten | 3,000 | 3,000 (38+2,962) | 0 | 0 | 0 | 3,000 | 0 | 1,979 | 926 | 95 | 1.1060x | 7.49x | 2,382.0s |
| MBA-Blast dataset2 | 2,500 | 2,500 (16+2,484) | 0 | 0 | 0 | 2,500 | 0 | 1,869 | 631 | 0 | 0.8696x | 10.60x | 1,858.5s |
| PLDI Linear | 1,008 | 1,008 (34+974) | 0 | 0 | 0 | 1,008 | 0 | 831 | 158 | 19 | 0.8136x | 9.45x | 619.7s |
| Univariate64 | 1,000 | 1,000 (23+977) | 0 | 0 | 0 | 126 | 874 | 1 | 0 | 999 | 84.2358x | 1.00x | 1,128.5s |
| Multivariate64 | 1,000 | 1,000 (679+321) | 0 | 0 | 0 | 459 | 541 | 6 | 0 | 994 | 628.5718x | 1.00x | 1,112.2s |
| Syntia | 500 | 500 (400+100) | 0 | 0 | 0 | 477 | 23 | 479 | 17 | 4 | 0.9619x | 4.00x | 74.5s |
| OSES | 479 | 464 (172+292) | 0 | 3 | 12 | 393 | 71 | 88 | 42 | 11 | 1.3917x* | 2.29x | 311.4s |
| Permutation64 | 13 | 13 (5+8) | 0 | 0 | 0 | 8 | 5 | 3 | 1 | 9 | 27.3006x | 1.05x | 26.4s |
| ObfuscatorX | 7 | 7 (1+6) | 0 | 0 | 0 | 7 | 0 | 0 | 7 | 0 | 1.3096x | 1.14x | 10.2s |
| **Total** | **9,507** | **9,492 (1,368+8,124)** | **0** | **3** | **12** | **7,978** | **1,514** | **5,256** | **1,782** | **2,131** | **3.2102x*** | **5.67x** | **7,523.5s** |

`*` OSES quality/bucket metrics cover only rows whose ground truth parsed and
produced dimensions. Of 479 rows, 464 outputs are proved against their original
inputs, but ground-truth checking reports 323 syntax errors, 50 semantic
refutations, 21 unknowns, and only 70 proofs. Consequently 323 established rows
are GT-unclassified and the Part-B aggregate quality denominator is 9,169, not
9,492. This is a dataset-language compatibility issue, not a rewrite proof
failure.

### Isolated reruns

OSES was the only Part-B suite with raw failures. At one worker:

- One timeout becomes proved.
- Two cases remain hard timeouts (`line_69`, `line_387`).
- Twelve remain parse errors.

Adjusted Part B is **9,493/9,507 established**, with two timeouts and twelve
syntax errors. No suite produces a refuted rewrite.

### Suite diagnostics

#### Linear/Boolean suites

MBA-Blast, PLDI Linear, and Syntia are strong:

- MBA-Blast: 2,500/2,500 strict reductions, no weak outputs, 0.8696x quality.
- PLDI Linear: 1,008/1,008 strict reductions, 831 solved, 0.8136x quality.
- Syntia: 479 solved of 500, only four weak, 0.9619x quality.

MBA-Flatten is broadly successful but retains 95 weak rows. Examples include
`line_1158` (401 -> 65, GT 2), `line_1468` (451 -> 64, GT 2), and `line_1199`
(586 -> 61, GT 2). These are higher-atom nested flattening sections; extend
component partitioning and grouped reconstruction beyond the current guarded
root shapes.

#### Polynomial suites

These are the largest clear gap in Wave 1:

- Univariate64: 874 unchanged, 999 weak, only one solved; quality 84.2358x.
- Multivariate64: 541 unchanged, 994 weak, only six solved; quality 628.5718x.
- Permutation64: nine of 13 weak; quality 27.3006x.

Concrete examples:

- `univariate64/line_1001`: size 269 unchanged, GT 3.
- `multivariate64/line_999`: size 2,403 unchanged, GT 3.
- `permutation64/line_10`: size 11,169 unchanged, GT 20.
- `permutation64/line_14`: 8,819 -> 8,379, GT 20.

The current sparse-ring/null-polynomial implementation is intentionally bounded
to degree 8 and 256 monomials during candidate generation. These corpora contain
much higher powers and dense multivariate compositions. The next work should be
modular falling-factorial reduction at high degree, sparse Horner/composition
recognition, and multivariate ideal/component reduction rather than AST
expansion.

#### OSES language boundary

Persistent parse errors are concrete and clustered:

- unary-plus forms such as `+2*~x` (`lines 32, 37, 40, 41, 45, 47`),
- source comments embedded as `// ...` (`lines 245/246`),
- indexed array syntax `X[0]` (`lines 287–290`),
- one trailing-token form.

The parser should not be weakened silently. A future OSES adapter should
translate these source-language constructs explicitly and preserve provenance.
The 50 ground-truth refutations also require dataset-semantic review before they
can be treated as simplifier regressions.

#### ObfuscatorX

All seven outputs are proved and strictly reduced, but all remain merely
meaningful (quality 1.3096x). The formulas combine many variables, shifts, and
nonlinear products; the current result is useful compression but not canonical
recovery. This is a good small target set for instruction-aware factorization.

## Bugs and failures

1. **No soundness failures:** 18,995 raw cases produce zero refuted outputs.
2. **OMVLL malformed restrictions:** targets 5052 and 6860 request restriction
   bounds outside operand width and fail before synthesis.
3. **Persistent hard timeouts:** nine OMVLL, three Tigress L6, one Tigress L8,
   and two OSES cases persist at one worker under the exact 20-second hard cap.
4. **OSES syntax mismatch:** 12 rows use constructs outside GreySynth's textual
   expression grammar. Additionally, most OSES GT strings cannot currently be
   checked under the shared parser/semantics.
5. **No crashes:** no `Z.Overflow`, assertion failure, malformed certificate, or
   unexpected runtime exception was observed in Wave 1.

## Prioritized optimization plan

1. **High-degree polynomial engine:** Univariate64/Multivariate64/Permutation64
   dominate the quality tail (2,002 weak rows across those three suites).
2. **DAG-aware C simplification:** hash-cons and saturate repeated Tigress/OMVLL
   regions rather than materializing 100k–1M-node trees; persist proved template
   rules across cases.
3. **OSES input adapter:** explicitly lower unary plus, `//` annotations, and
   indexed `X[n]` variables, then revalidate GT semantics.
4. **C-MBA root decomposition:** C-MBA quality is 12.94x versus 2.92x for
   C-BeyondMBA; large arithmetic/Boolean compositions need hierarchical opaque
   component solving.
5. **MBA-Flatten high-atom sections:** generalize equal-coefficient grouping and
   connected components beyond the current conservative root limits.
6. **ObfuscatorX factorization:** use the seven-case suite as a compact target
   for shift-aware nonlinear common-subexpression recovery.

## Conclusion

Wave 1 confirms excellent fail-closed coverage—99.8% raw and 99.85% after
isolated reruns, with zero refutations—but also identifies a sharp frontier.
GreySynth is strong on linear/Boolean MBA families and low-to-mid C levels. It
needs a dedicated high-degree polynomial representation and DAG-regional
simplification to address the remaining Wave-1 quality tail.
