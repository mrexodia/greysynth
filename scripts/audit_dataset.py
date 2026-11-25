#!/usr/bin/env python3
"""Audit GreySynth outputs against their ORIGINAL inputs with mba_equiv.

Example (from the repository root):
  python3 scripts/audit_dataset.py --binary ./greysynth --checker ./mba_equiv \
    --config default.json --dataset /path/to/tigress_lvl_5/mba_info \
    --output results/patched.jsonl --workers 2 --timeout 30

JSON case directories contain {obf_expr, gt_expr?, bitwidth, target?} files;
*_sizes.json and JSON manifests are ignored. A .txt/.csv file instead accepts
ProMBA's ``obfuscated,ground_truth`` pairs (64 bits unless --raw-bitwidth is set).
--limit chooses the first cases in stable lexicographic ID order, not a random
sample. Repeat --dataset to combine corpora. Ground-truth checking is opt-in;
it never substitutes for checking the synthesized result against its input.

Each checker runs in a separate process: 256 concrete samples, then a 1-second
SMT query unless sampling already refuted the result. Finite agreement and
unknown/timeout are never classified as proof. --timeout is a hard limit on
each process (including its process group); the solver also gets --smt-timeout.
Rows are flushed and fsynced as they finish. A sibling .summary.json records
counts and provenance; JSONL row order can vary with --workers. Existing output
files are refused. Exit 0 means the audit completed, not that every case passed.

With --proof-checker, GreySynth also exports a certificate for independent
SMT replay and congruence checking. Certificates are retained beside the audit.
The direct whole-expression verdict is preserved in against_input; a separate
proved_compositional verdict records a successful independent replay when the
direct query is inconclusive. A malformed certificate is an audit error.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time


STOP = threading.Event()
PROCESSES: set[subprocess.Popen] = set()
PROCESS_LOCK = threading.Lock()
VERDICTS = ("sampled", "proved", "proved_compositional", "refuted", "unknown", "error", "timeout")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def text_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Case:
    identifier: str
    source: Path
    data: dict | None = None
    line: int | None = None


def collect_cases(paths: list[Path], raw_bitwidth: int) -> list[Case]:
    cases = []
    seen = set()
    for dataset in paths:
        label = dataset.parent.name if dataset.name == "mba_info" else dataset.stem
        if dataset.is_dir() or dataset.suffix.lower() == ".json":
            files = sorted(dataset.rglob("*.json")) if dataset.is_dir() else [dataset]
            for path in files:
                if path.name.endswith("_sizes.json"):
                    continue
                try:
                    data = json.loads(path.read_text())
                except (OSError, ValueError):
                    # Preserve malformed cases as explicit errors, rather than
                    # silently improving the denominator by dropping them.
                    data = {"target": path.stem, "obf_expr": None}
                if not isinstance(data, dict) or "obf_expr" not in data:
                    continue
                relative = path.relative_to(dataset) if dataset.is_dir() else Path(path.name)
                identifier = f"{label}/{relative.with_suffix('')}"
                cases.append(Case(identifier, path))
        else:
            csv.field_size_limit(sys.maxsize)
            with dataset.open(newline="") as stream:
                for line_no, line in enumerate(stream, 1):
                    if not line.strip() or line.lstrip().startswith("#"):
                        continue
                    fields = next(csv.reader([line]))
                    if len(fields) != 2:
                        raise ValueError(f"{dataset}:{line_no}: expected expression,ground_truth")
                    identifier = f"{label}/line_{line_no:07d}"
                    data = {"obf_expr": fields[0], "bitwidth": raw_bitwidth}
                    if fields[1].strip():
                        data["gt_expr"] = fields[1]
                    cases.append(Case(identifier, dataset, data, line_no))
    for case in cases:
        if case.identifier in seen:
            raise ValueError(f"duplicate case ID: {case.identifier}; use distinct dataset names")
        seen.add(case.identifier)
    return sorted(cases, key=lambda case: case.identifier)


def signal_group(process: subprocess.Popen, sig: int) -> None:
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def stop_processes() -> None:
    STOP.set()
    with PROCESS_LOCK:
        for process in list(PROCESSES):
            signal_group(process, signal.SIGKILL)


def run_process(command: list[str], timeout: float, tmpdir: Path) -> dict:
    started = time.monotonic()
    if STOP.is_set():
        return {"status": "error", "error": "audit interrupted", "wall_seconds": 0}
    env = dict(os.environ, TMPDIR=str(tmpdir), TMP=str(tmpdir), TEMP=str(tmpdir))
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True, errors="replace", env=env, start_new_session=True)
    except OSError as exc:
        return {"status": "error", "error": str(exc), "wall_seconds": time.monotonic() - started}
    with PROCESS_LOCK:
        PROCESSES.add(process)
        if STOP.is_set():
            signal_group(process, signal.SIGKILL)
    status = "ok"
    try:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            status = "timeout"
            signal_group(process, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=0.5)
            except subprocess.TimeoutExpired:
                signal_group(process, signal.SIGKILL)
                stdout, stderr = process.communicate()
            # The leader may exit on SIGTERM while a descendant ignores it
            # and closes its pipes. Kill any remaining group members too.
            signal_group(process, signal.SIGKILL)
        if status == "ok" and process.returncode != 0:
            status = "error"
        return {"status": status, "returncode": process.returncode,
                "wall_seconds": time.monotonic() - started,
                "stdout": stdout, "stderr": stderr[-4000:]}
    except BaseException:
        signal_group(process, signal.SIGKILL)
        process.communicate()
        raise
    finally:
        with PROCESS_LOCK:
            PROCESSES.discard(process)


def decode_report(run: dict) -> tuple[dict | None, str | None]:
    if run["status"] != "ok":
        return None, run.get("error") or run.get("stderr") or run["status"]
    try:
        report = json.loads(run.get("stdout", ""))
        if not isinstance(report, dict):
            raise ValueError("expected a JSON object")
        return report, None
    except ValueError as exc:
        return None, f"invalid JSON report: {exc}"


def checker_step(args, original: Path, candidate: Path, width: int,
                 tmpdir: Path, mode: str) -> dict:
    command = [str(args.checker), "-size", str(width), "-obf", "-string-file", str(original),
               "-gt", "-string-file", str(candidate)]
    command += (["-sample", str(args.samples)] if mode == "sample" else
                ["-smt", "-timeout", str(args.smt_timeout)])
    run = run_process(command, args.timeout, tmpdir)
    report, error = decode_report(run)
    result = {k: v for k, v in run.items() if k != "stdout"}
    if report is None:
        result.update(status="timeout" if run["status"] == "timeout" else "error", error=error)
        return result
    status = report.get("verification")
    allowed = {"sampled", "refuted", "evaluation_error"} if mode == "sample" else {
        "proved", "refuted", "unknown", "timeout"}
    if status not in allowed:
        result.update(status="error", error="checker lacks the expected verification contract; use patched mba_equiv")
        return result
    result["status"] = "error" if status == "evaluation_error" else status
    for key in ("equiv", "counter_example", "equiv_time", "sample_match", "checked_samples",
                "requested_samples", "evaluation_error"):
        if key in report:
            result[key] = report[key]
    for source_key, output_key in (("obf", "input_size"), ("gt", "output_size")):
        operand = report.get(source_key, {})
        size = operand.get("size")
        if isinstance(size, int) and not isinstance(size, bool) and size > 0:
            result[output_key] = size
        costs = operand.get("costs")
        if isinstance(costs, dict) and all(
                isinstance(value, int) and not isinstance(value, bool) and value > 0
                for value in costs.values()):
            result[output_key.replace("size", "costs")] = costs
    return result


def check_pair(args, original: Path, candidate: Path, width: int, tmpdir: Path) -> dict:
    sample = checker_step(args, original, candidate, width, tmpdir, "sample")
    if sample["status"] == "refuted":
        return {"verdict": "refuted", "sample": sample,
                "smt": {"status": "not_run", "reason": "sample counterexample"}}
    smt = checker_step(args, original, candidate, width, tmpdir, "smt")
    # Sampling errors/timeouts are retained even when SMT succeeds. If SMT is
    # inconclusive, the separate sample record preserves finite agreement.
    return {"verdict": smt["status"], "sample": sample, "smt": smt}


def replay_proof(args, original: Path, candidate: Path, certificate: Path,
                 width: int, tmpdir: Path) -> dict:
    if not certificate.is_file():
        return {"status": "error", "error": "simplifier did not emit the requested certificate"}
    command = [str(args.proof_checker), "-size", str(width),
               "-obf", "-string-file", str(original),
               "-gt", "-string-file", str(candidate),
               str(certificate), str(args.proof_timeout)]
    run = run_process(command, args.proof_process_timeout, tmpdir)
    report, error = decode_report(run)
    result = {k: v for k, v in run.items() if k != "stdout"}
    result.update(certificate=str(certificate), certificate_sha256=sha256_file(certificate))
    if report is None:
        result.update(status="timeout" if run["status"] == "timeout" else "error", error=error)
        return result
    status = report.get("verification")
    if status not in {"proved_compositional", "unknown", "timeout", "invalid_certificate", "error", "refuted"}:
        result.update(status="error", error="unexpected certificate verifier contract", report=report)
        return result
    result.update(status=status, report=report)
    return result


def combined_verdict(direct: dict, replay: dict) -> str:
    """Keep direct refutations and invalid certificates visible, never fail open."""
    status = replay["status"]
    refuted = direct["verdict"] == "refuted" or direct.get("sample", {}).get("status") == "refuted"
    if refuted:
        return "error" if status == "proved_compositional" else "refuted"
    if status in {"invalid_certificate", "error", "refuted"}:
        # A refuted edge invalidates the certificate, not necessarily the final
        # expression. Do not present it as a counterexample to the output.
        return "error"
    if direct["verdict"] == "proved":
        return "proved"
    return "proved_compositional" if status == "proved_compositional" else direct["verdict"]


def checked_dimensions(check: dict) -> dict:
    return next((record for record in (check.get("sample", {}), check.get("smt", {}))
                 if "input_size" in record and "output_size" in record), {})


def classify_size(row: dict, report: dict) -> None:
    check = row.get("against_input", {})
    sizes = checked_dimensions(check)
    before, after = sizes.get("input_size"), sizes.get("output_size")
    source = "checker"
    if before is None or after is None:
        before, after, source = report.get("obf_sz"), report.get("syn_sz"), "simplifier_report"
    if any(not isinstance(v, int) or isinstance(v, bool) or v < 1 for v in (before, after)):
        row["size"] = {"relation": "unknown"}
    else:
        row["size"] = {"input": before, "output": after, "source": source,
                       "delta": after - before,
                       "relation": "strict_decrease" if after < before else
                       "netneutral" if after == before else "expansion"}
    input_costs, output_costs = sizes.get("input_costs"), sizes.get("output_costs")
    if isinstance(input_costs, dict) and isinstance(output_costs, dict):
        row["costs"] = {"input": input_costs, "output": output_costs}


def execute_case(args, case: Case) -> dict:
    started = time.monotonic()
    row = {"id": case.identifier, "source": str(case.source), "source_line": case.line,
           "synthesis_status": "error", "verdict": "error", "size": {"relation": "unknown"}}
    try:
        data = case.data if case.data is not None else json.loads(case.source.read_text())
        original, truth, width = data["obf_expr"], data.get("gt_expr"), data["bitwidth"]
        if not isinstance(original, str) or not original.strip():
            raise ValueError("obf_expr must be a nonempty string")
        if not isinstance(width, int) or isinstance(width, bool) or width <= 0:
            raise ValueError("bitwidth must be a positive integer")
        if truth is not None and not isinstance(truth, str):
            raise ValueError("gt_expr must be a string when supplied")
        row.update(bitwidth=width, input_sha256=text_hash(original))
        if truth is not None:
            row["ground_truth_sha256"] = text_hash(truth)
        with tempfile.TemporaryDirectory(prefix="case-", dir=args.tmpdir) as temp:
            tmpdir = Path(temp)
            source, candidate, ground_truth = (tmpdir / name for name in ("original.txt", "candidate.txt", "ground_truth.txt"))
            source.write_text(original)
            command = [str(args.binary), "-size", str(width), "-obf", "-string-file", str(source), str(args.config)]
            certificate = None
            if args.proof_checker:
                certificate = args.certificate_dir / (text_hash(case.identifier) + ".proof.json")
                command.append(str(certificate))
            # Keep the benchmark's expected answer out of the simplifier.
            run = run_process(command, args.timeout, tmpdir)
            report, error = decode_report(run)
            row["synthesis"] = {k: v for k, v in run.items() if k != "stdout"}
            row["synthesis_status"] = run["status"]
            if report is None:
                if run["status"] == "ok":
                    row["synthesis_status"] = "error"
                row.update(verdict="timeout" if run["status"] == "timeout" else "error", error=error)
            else:
                expression = report.get("syn_expr")
                if not isinstance(expression, str) or not expression.strip():
                    row["synthesis_status"] = "error"
                    raise ValueError("simplifier report has no nonempty syn_expr")
                row.update(syn_expr=expression, output_sha256=text_hash(expression),
                           simplifier_report={k: v for k, v in report.items() if k != "syn_expr"})
                candidate.write_text(expression)
                row["against_input"] = check_pair(args, source, candidate, width, tmpdir)
                row["verdict"] = row["against_input"]["verdict"]
                if certificate is not None:
                    row["proof_replay"] = replay_proof(args, source, candidate, certificate, width, tmpdir)
                    row["verdict"] = combined_verdict(row["against_input"], row["proof_replay"])
                classify_size(row, report)
                if args.check_ground_truth and truth is not None:
                    ground_truth.write_text(truth)
                    row["against_ground_truth"] = check_pair(args, ground_truth, candidate, width, tmpdir)
                    dimensions = checked_dimensions(row["against_ground_truth"])
                    ground_truth_costs = dimensions.get("input_costs")
                    if isinstance(ground_truth_costs, dict):
                        row.setdefault("costs", {})["ground_truth"] = ground_truth_costs
    except Exception as exc:
        row.update(verdict="error", error=f"{type(exc).__name__}: {exc}")
    row["wall_seconds"] = time.monotonic() - started
    return row


def ratio_statistics(values: list[float]) -> dict:
    if not values:
        return {"count": 0}
    return {
        "count": len(values),
        "geometric_mean": math.exp(sum(math.log(value) for value in values) / len(values)),
        "arithmetic_mean": sum(values) / len(values),
    }


def cost_metrics(rows: list[dict]) -> dict:
    metrics = {}
    for model in ("legacy", "paper_ast", "instruction", "readability"):
        quality, compression = [], []
        for row in rows:
            costs = row.get("costs", {})
            original = costs.get("input", {}).get(model)
            output = costs.get("output", {}).get(model)
            truth = costs.get("ground_truth", {}).get(model)
            if isinstance(original, int) and isinstance(output, int) and output > 0:
                compression.append(original / output)
            if isinstance(truth, int) and isinstance(output, int) and truth > 0:
                quality.append(output / truth)
        metrics[model] = {
            "quality_output_over_ground_truth": ratio_statistics(quality),
            "compression_input_over_output": ratio_statistics(compression),
        }
    return metrics


def summarize(rows: list[dict], metadata: dict, complete: bool) -> dict:
    verdicts, sizes, synthesis = Counter(), Counter(), Counter()
    samples, smt, truth, matrix, replay = Counter(), Counter(), Counter(), Counter(), Counter()
    for row in rows:
        verdicts[row["verdict"]] += 1
        sizes[row["size"]["relation"]] += 1
        synthesis[row["synthesis_status"]] += 1
        matrix[f"{row['verdict']}:{row['size']['relation']}"] += 1
        for kind, counter in (("sample", samples), ("smt", smt)):
            counter[row.get("against_input", {}).get(kind, {}).get("status", "not_run")] += 1
        if "against_ground_truth" in row:
            truth[row["against_ground_truth"]["verdict"]] += 1
        replay[row.get("proof_replay", {}).get("status", "not_run")] += 1
    return {**metadata, "complete": complete, "completed_cases": len(rows),
            "verdict_counts": {s: verdicts[s] for s in VERDICTS},
            "sample_status_counts": dict(samples), "smt_status_counts": dict(smt),
            "proof_replay_status_counts": dict(replay),
            "ground_truth_verdict_counts": dict(truth), "synthesis_status_counts": dict(synthesis),
            "size_counts": dict(sizes), "verdict_by_size": dict(matrix),
            "proved_strict_decreases": matrix["proved:strict_decrease"] + matrix["proved_compositional:strict_decrease"],
            "direct_proved_strict_decreases": matrix["proved:strict_decrease"],
            "compositional_proved_strict_decreases": matrix["proved_compositional:strict_decrease"],
            "internal_timeouts": sum(bool(row.get("simplifier_report", {}).get("has_timed_out")) for row in rows),
            "cost_metrics": cost_metrics(rows),
            "summed_case_seconds": sum(row["wall_seconds"] for row in rows)}


def write_summary(path: Path, summary: dict) -> None:
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w") as stream:
        json.dump(summary, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def executable(value: str) -> Path:
    resolved = shutil.which(value)
    path = Path(resolved or value).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise argparse.ArgumentTypeError(f"executable not found: {value}")
    return path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--binary", type=executable, required=True)
    parser.add_argument("--checker", type=executable, required=True)
    parser.add_argument("--proof-checker", type=executable,
                        help="independent mba_proof executable; enables certificate generation and replay")
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--dataset", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True, help="new JSONL file (never overwritten)")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--limit", type=int, default=None, help="first sorted cases; omitted means all")
    parser.add_argument("--timeout", type=float, default=30, help="hard seconds per process/group")
    parser.add_argument("--samples", type=int, default=256)
    parser.add_argument("--smt-timeout", type=int, default=1)
    parser.add_argument("--proof-timeout", type=int, default=2, help="seconds per certificate equality obligation")
    parser.add_argument("--proof-process-timeout", type=float, default=60,
                        help="hard seconds for the entire independent certificate verifier")
    parser.add_argument("--certificate-dir", type=Path, help="new directory for retained proof certificates")
    parser.add_argument("--case-ids", type=Path, help="JSON list of exact case IDs to audit")
    parser.add_argument("--raw-bitwidth", type=int, default=64)
    parser.add_argument("--check-ground-truth", action="store_true")
    parser.add_argument("--tmpdir", type=Path, help="defaults to a temporary directory beside --output")
    args = parser.parse_args()
    if any(value <= 0 for value in (args.workers, args.timeout, args.samples, args.smt_timeout,
                                    args.proof_timeout, args.proof_process_timeout, args.raw_bitwidth)):
        parser.error("workers, timeouts, samples and raw-bitwidth must be positive")
    if args.limit is not None and args.limit < 1:
        parser.error("limit must be positive; omit it to audit every case")
    args.config, args.output = args.config.resolve(), args.output.resolve()
    args.dataset = [path.resolve() for path in args.dataset]
    try:
        config = json.loads(args.config.read_text())
        if not isinstance(config, dict):
            raise ValueError("configuration must be a JSON object")
        cases = collect_cases(args.dataset, args.raw_bitwidth)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    total_available = len(cases)
    if not cases:
        parser.error("no expression cases found")
    if args.case_ids:
        try:
            selected = json.loads(args.case_ids.read_text())
            if (not isinstance(selected, list) or not selected
                    or any(not isinstance(x, str) for x in selected)
                    or len(set(selected)) != len(selected)):
                raise ValueError("case-ids must contain a nonempty JSON array of unique strings")
            missing = set(selected) - {case.identifier for case in cases}
            if missing:
                raise ValueError(f"case IDs not found: {sorted(missing)}")
            selected = set(selected)
            cases = [case for case in cases if case.identifier in selected]
        except (OSError, ValueError) as exc:
            parser.error(str(exc))
    cases = cases if args.limit is None else cases[:args.limit]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    summary_path = args.output.with_suffix(".summary.json")
    if args.output.exists() or summary_path.exists():
        parser.error("output or summary already exists; choose a new output path")
    if args.proof_checker:
        args.certificate_dir = (args.certificate_dir or args.output.with_suffix(".certificates")).resolve()
        if args.certificate_dir.exists():
            parser.error("certificate directory already exists; choose a new path")
        args.certificate_dir.mkdir(parents=True)
    elif args.certificate_dir:
        parser.error("--certificate-dir requires --proof-checker")
    args.tmpdir = (args.tmpdir or args.output.parent / "audit-tmp").resolve()
    args.tmpdir.mkdir(parents=True, exist_ok=True)
    metadata = {"schema_version": 2, "started_at": datetime.now(timezone.utc).isoformat(),
                "binary": str(args.binary), "binary_sha256": sha256_file(args.binary),
                "checker": str(args.checker), "checker_sha256": sha256_file(args.checker),
                "config": config, "config_path": str(args.config), "config_sha256": sha256_file(args.config),
                "datasets": [str(path) for path in args.dataset], "available_cases": total_available,
                "selected_cases": len(cases), "selected_ids_sha256": text_hash("\n".join(case.identifier for case in cases)),
                "workers": args.workers, "hard_process_timeout": args.timeout, "samples": args.samples,
                "smt_timeout": args.smt_timeout, "raw_bitwidth": args.raw_bitwidth,
                "proof_checker": str(args.proof_checker) if args.proof_checker else None,
                "proof_checker_sha256": sha256_file(args.proof_checker) if args.proof_checker else None,
                "proof_timeout": args.proof_timeout, "proof_process_timeout": args.proof_process_timeout,
                "certificate_dir": str(args.certificate_dir) if args.proof_checker else None,
                "check_ground_truth": args.check_ground_truth,
                "primary_reference": "original_input", "output": str(args.output)}
    rows, complete = [], False
    started = time.monotonic()

    def interrupted(signum, frame):
        raise KeyboardInterrupt(f"signal {signum}")

    signal.signal(signal.SIGTERM, interrupted)
    pool = ThreadPoolExecutor(max_workers=args.workers)
    try:
        with args.output.open("x") as stream:
            write_summary(summary_path, summarize(rows, metadata, False))
            futures = [pool.submit(execute_case, args, case) for case in cases]
            for future in as_completed(futures):
                row = future.result()
                stream.write(json.dumps(row, separators=(",", ":")) + "\n")
                stream.flush()
                os.fsync(stream.fileno())
                rows.append(row)
                if len(rows) % 10 == 0:
                    write_summary(summary_path, summarize(rows, metadata, False))
                    print(f"{len(rows)}/{len(cases)} cases audited", file=sys.stderr, flush=True)
            complete = True
    except KeyboardInterrupt:
        stop_processes()
        print("Interrupted; completed JSONL rows are preserved.", file=sys.stderr)
    finally:
        if not complete:
            stop_processes()
        pool.shutdown(wait=True, cancel_futures=True)
        metadata["elapsed_seconds"] = time.monotonic() - started
        summary = summarize(rows, metadata, complete)
        write_summary(summary_path, summary)
    print(json.dumps({"complete": complete, "completed_cases": len(rows),
                      "verdict_counts": summary["verdict_counts"], "size_counts": summary["size_counts"],
                      "summary": str(summary_path)}, indent=2))
    return 0 if complete else 130


if __name__ == "__main__":
    raise SystemExit(main())
