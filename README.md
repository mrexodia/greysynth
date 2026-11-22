# GreySynth

GreySynth is an efficient grey-box deobfuscation framework. It lifts black-box deobfuscators (like [Xyntia](https://github.com/binsec/xyntia)) to simplify obfuscated code including Mixed Boolean-Arithmetic (MBA) expressions. 

GreySynth combines two techniques:

- **OES** (output-equivalence simplification): every sub-expression is
  evaluated on a shared set of input samples, and each node is replaced by the
  smallest node in the expression that behaves the same on all samples.
- **Synthesis**: sub-trees are sampled and handed to a black-box synthesizer
  (Xyntia by default, also Syntia or cvc5), and replaced by the result when it
  is smaller. **CHS** applies this to sub-trees cut at increasing depths
  ("horizons"); *global synthesis* applies it bottom-up to every complete
  sub-tree.

## Building

### Dev Container (Docker)

With Docker running in Linux-container mode and the
[Dev Container CLI](https://github.com/devcontainers/cli) installed, run these
commands from the repository root:

```sh
devcontainer up --workspace-folder .
devcontainer exec --workspace-folder . make test
devcontainer exec --workspace-folder . bash
```

The image includes OCaml 5.3, the vendored BINSEC and Xyntia packages, and the
native Bitwuzla solver for the proof tests. The first start can take
several minutes to compile dependencies. The checkout is mounted into the
container and built with `make` on creation. Build artifacts stay inside the
container. From the container shell, use `dune exec -- greysynth` to run the CLI
without installing it, or `make install` to put it on the container's `PATH`.

If you change the Dockerfile or the vendored dependencies, recreate the container
with `devcontainer up --workspace-folder . --remove-existing-container`.
Ordinary source edits only require rerunning `make` or `make test`.

### Native build

Requirements: OCaml 5.3 with [opam](https://opam.ocaml.org/). To build GreySynth proceed as follows:

```sh
cd <greysynth-folder>
opam switch create . 5.3.0 -y
eval $(opam env)
opam install goblint-cil=2.0.8 yojson containers
opam pin outside_tools/binsec_no_simplification
opam pin outside_tools/xyntia
make && make install
```

You can now run GreySynth directly using `greysynth`.

Run the regression suite with `make test`. It exercises the evaluator, parser,
SMT checker, OES, synthesis, and cache acceptance. An installed SMT backend is
required for the proof tests. It also tests deterministic normalization,
independent certificate replay, and the audit's result classification.

## Running

```sh
greysynth -obf -string "(x|y) + (x&y)" -gt -string "x + y" default.json
```

- `-obf <src>`: the expression to simplify (required); `-gt <src>`: an optional
  ground truth, used for equivalence checks and in the report.
- `<src>` is `-string "<expr>"`, `-string-file <file>`, or
  `-cil <file.c> <function>` (the function's return expression).
- `-size <n>`: default bit width of unsized variables and constants (64).

Expression syntax: C-like operators (`+ - * & | ^ ~ << >> >>s / % ...`),
variables with an optional width (`x<32>`), see
`src/parsers/string_to_sexpr.mli`.

Progress is logged to stderr; a JSON report is printed to stdout (`syn_expr`,
`syn_sz`, `equiv`, `time`, plus per-pass statistics).

An optional second positional argument exports a proof certificate:

```sh
greysynth -obf -string-file input.txt default.json proof.json > result.json
python3 -c 'import json,sys; print(json.load(sys.stdin)["syn_expr"])' < result.json > output.txt
mba_proof -obf -string-file input.txt -gt -string-file output.txt proof.json 1,5,30
```

Use the same `-size` on both commands when unsized literals are not 64 bits.
The replay tool binds the certificate to these actual input/output expressions,
proves local equality obligations afresh, and derives endpoint equality through
congruence and transitivity. Its optional comma-separated timeouts retry only
inconclusive obligations. `verification: "proved_compositional"` establishes
equivalence even when a separate whole-expression query times out. The producer's
`proof_certificate.status: "recorded_not_replayed"` makes no such claim.


## Configuration

The first positional argument is a JSON configuration; `default.json` is a
working example. An optional second positional argument names the certificate.

| Key | Meaning |
|---|---|
| `normalization` | Run deterministic, proof-gated bitvector and local linear-MBA normalization before OES. Defaults to true; false permits comparison with the earlier pipeline. |
| `ac_normalization` | Enable experimental associative coefficient collection and Boolean cancellation. |
| `normalization_portfolio` | Run baseline and AC normalization from the same input and retain the cheaper proved branch. Disabled by default because it spends additional proof budget. |
| `normalization_max_atoms` | Maximum independent atoms in local linear-MBA truth tables (1–10, default 6). |
| `mba_oracle`, `mba_oracle_command` | Optional untrusted `rumba` or `cobra` CLI candidate generator for maximal uniform-width pure-MBA subtrees. |
| `mba_oracle_timeout`, `mba_oracle_calls` | Per-call wall timeout and maximum calls per run (defaults 2 seconds and 4). |
| `cost_model` | Candidate-selection objective: historical `legacy`, conversion-counting `paper_ast`, approximate `instruction`, or `readability`. Reports include every cost. |
| `oes` | Run OES after normalization, after each CHS horizon, and once at the end. |
| `oes_extended`, `local_extend`, `local_extend_depth` | Extra vocabulary added to the OES cache. |
| `oes_fixedpoint` | Repeat OES until the size stops decreasing. |
| `oes_candidate_limit` | Number of sampled-equivalent representatives retained per OES class. Defaults to 1; larger proof-aware frontiers are experimental because failed proofs consume the global budget. |
| `fast_simplify` | OES extension with relational vocabulary (not in the CCS'26 paper). |
| `global_synthesis` | Run global (bottom-up, untruncated) synthesis. |
| `chs` | Run CHS. |
| `chs_max_inputs`, `chs_max_horizon` | Optional CHS search caps; zero means unlimited. |
| `local_cache` | Reuse synthesis results for nodes with the same outhash. |
| `synthesizer` | `xyntia`, `syntia` or `cvc5`. Backend-specific keys: `xyntia_grammar` (`auto` chooses `mba`, `mba_shift`, or `full` per target), `xsmir_ops`, `synthesizer_cmd`, `synthesizer_script`. |
| `synthesis_timeout`, `synthesis_repeat` | Per-call synthesizer timeout (s) and attempts. |
| `cegis_retries` | Retry synthesis after an SMT refutation contributes a new explicit counterexample. Defaults to 1. |
| `learn_synthesis_rules` | Prove successful Greek-variable templates universally and reuse them across concrete contexts. Defaults to true. |
| `add_constants_to_synthesis` | Pass original and bounded derived constants to the synthesizer. |
| `synthesis_constant_limit` | Maximum constants injected into one synthesis problem (default 12). |
| `nb_samples` | Number of input samples used by OES and synthesis. |
| `branch_covering_samples` | Add feasible SMT-model samples for both sides of truncated ITE conditions. Defaults to true. |
| `check_equiv`, `equiv_timeout` | Check each pass against the ground truth, or the original input when no ground truth is supplied. The timeout also bounds individual rewrite proofs. |
| `reject_non_equiv_simplifications` | Require a proof for every OES, relational, synthesis, and cache rewrite. Enabled in `default.json`; unknown, timeout, errors, and missing solvers reject the candidate. |
| `total_timeout` | Overall time limit (s); the best result so far is reported. |
| `balanced_tree`, `sampling_strategy` | Currently only recorded in the report. |


## Correctness and validation

The default configuration requires an SMT proof before accepting a rewrite.
A candidate must have the same bit width and a strictly smaller **restored**
expression, agree with the complete synthesis sample bank and an independent
validation bank, and pass the proof. This applies to OES, relational vocabulary,
normalization, CHS, global synthesis, and cached results. Set
`reject_non_equiv_simplifications` to `false` only when sample-based heuristic
results are acceptable; finite agreement is not a proof.

CHS checks a candidate after substituting its cut leaves back into the original
context. The cut leaves can be correlated, so checking a template over
independent fresh variables can reject valid contextual simplifications.
Likewise, a small template can expand to a larger expression. Completed validated
rewrites survive a later timeout; the remaining work is skipped. Algebraic
postprocessing is checked too; the raw synthesis result is retained as a
fallback if postprocessing fails or changes the meaning.

Sample signatures retain every width-tagged output. A digest distributes hash
buckets; collisions never establish equality. Evaluation caches use complete
expression keys. Both ordinary and cut-leaf evaluation use the same total
bitvector semantics: oversized logical shifts produce zero, arithmetic shifts
produce the sign fill, rotations reduce their amount modulo the operand width,
and division/remainder by zero follow SMT-LIB bitvector semantics.

The JSON report includes `rewrite_validation` (`proved` or `sampled`) and
`rewrite_checks` counters. `check_equiv` additionally checks the complete result;
`equiv: "ukn"` is inconclusive and must never be counted as proved success.
Similarly, `mba_equiv -sample N` reports finite agreement as
`verification: "sampled"`, `sample_match: true`, and `equiv: "ukn"`.

The default expression printer includes literal widths and preserves variable
identity. Its output can be parsed again without discarding width annotations.
The string input language is a pure bitvector language with C-like precedence,
not a complete C implementation; see `string_to_sexpr.mli`.

### Scope and remaining limitations

These guarantees concern the parsed pure expression. Memory loads are not
modeled. The C frontend extracts a return expression; it does not reconstruct
arbitrary assignments or control flow. For arbitrary C or binary programs,
validate the lifting/extraction stage independently. Solver timeouts can still
prevent useful rewrites; their frequency is reported separately.

For dataset provenance, benchmark denominators, and reproduction commands, see
[`docs/VALIDATION.md`](docs/VALIDATION.md). The audit harness in
`scripts/audit_dataset.py` keeps proofs, refutations, sampling agreement,
timeouts, and errors separate and checks each result against its original
input.

For independent replay in a corpus run, pass `--proof-checker /path/to/mba_proof`
to that harness. It retains certificates, preserves the direct checker outcome,
and reports compositional proofs separately. The size metric excludes extension
and restriction wrappers; a one-leaf expression already has the minimum size.
An unchanged result is not by itself evidence of a failure or of minimality.
See [`docs/COVERAGE.md`](docs/COVERAGE.md) for the follow-up's complete
1,000-case proof replay, portfolio results, remaining minimal expressions,
and inconsistent input/ground-truth pairs.

# Cite us

```bibtex
@inproceedings{10.1145/3830454.3846695,
author = {Attias, Vidal and Menguy, Gr{\'e}goire and Bellec, Nicolas and Bardin, S{\'e}bastien and Marion, Jean-Yves},
title = {Redefining Grey-Box Deobfuscation through Context-Aware Program Synthesis, and Application to MBA},
year = {2026},
isbn = {9798400728716},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3830454.3846695},
doi = {10.1145/3830454.3846695},
booktitle = {Proceedings of the 2026 ACM SIGSAC Conference on Computer and Communications Security},
pages = {6759–6773},
numpages = {15},
keywords = {deobfuscation, reverse engineering, mixed boolean-arithmetic, grey-box, program synthesis},
location = {The Hague, Netherlands},
series = {CCS '26}
}
```
