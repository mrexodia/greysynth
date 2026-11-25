#!/usr/bin/env python3
"""Build focused failing/weak and solved-regression datasets from GreySynth audit JSONLs.

Outputs (by default under datasets/hard_cases/, which is git-excluded):
  - all_failing/<suite>/*.json : every unproved, weak, and targeted unsolved case
  - core_hard/<suite>/*.json   : fast ~300-case stratified slice of the hardest cases
  - regression_smoke/<suite>/*.json : 2 complex already-solved cases per suite
  - manifest.json              : exact provenance & counts
"""

from __future__ import annotations

import csv
import json
import os
from pathlib import Path
import shutil
import sys


REPO_ROOT = Path(__file__).resolve().parent.parent
OUT_ROOT = REPO_ROOT / "datasets" / "hard_cases"

# Latest audit JSONL per suite (most recent post-R19/R20/R21/R22 runs first).
SUITES: list[tuple[str, str, int]] = [
    # (suite_key, jsonl_path, core_hard_cap)
    ("c_mba_obfuscator", "/tmp/r21-mba-final/out.jsonl", 50),
    ("permutation64", "/tmp/greysynth-bench/r20-audit/permutation64/out.jsonl", 13),
    ("obfuscatorx", "/tmp/r22-obx/out.jsonl", 7),
    ("omvll", "/tmp/greysynth-bench/wave1-r18/part-a/omvll/out.jsonl", 35),
    ("tigress_l5", "/tmp/r21-audit/tigress_l5/out.jsonl", 15),
    ("tigress_l6", "/tmp/greysynth-bench/wave1-r18/part-a/tigress_lvl_6/out.jsonl", 15),
    ("tigress_l7", "/tmp/greysynth-bench/wave1-r18/part-a/tigress_lvl_7/out.jsonl", 15),
    ("tigress_l8", "/tmp/greysynth-bench/wave1-r18/part-a/tigress_lvl_8/out.jsonl", 25),
    ("loki", "/tmp/greysynth-bench/full-audit-r18-final/loki/out.jsonl", 25),
    ("floki", "/tmp/r22-audit/floki/out.jsonl", 15),
    ("qsynth_ea", "/tmp/greysynth-bench/full-audit-r18-final/qsynth_ea/out.jsonl", 25),
    ("pldi_poly", "/tmp/greysynth-bench/full-audit-r18-final/pldi_poly/out.jsonl", 25),
    ("pldi_nonpoly", "/tmp/greysynth-bench/full-audit-r18-final/pldi_nonpoly/out.jsonl", 10),
    ("mba_obf_nonlinear", "/tmp/greysynth-bench/full-audit-r18-final/mba_obf_nonlinear/out.jsonl", 30),
    ("msimba", "/tmp/greysynth-bench/full-audit-r18-final/msimba/out.jsonl", 0),
    ("mba_flatten", "/tmp/greysynth-bench/r20-audit/mba_flatten/out.jsonl", 25),
    ("neureduce", "/tmp/greysynth-bench/r20-audit/neureduce/out.jsonl", 25),
    ("simba_e1_4vars", "/tmp/greysynth-bench/r20-audit/e1_4vars/out.jsonl", 12),
    ("simba_e1_5vars", "/tmp/greysynth-bench/r20-audit/e1_5vars/out.jsonl", 0),
    ("simba_e2_4vars", "/tmp/greysynth-bench/r20-audit/e2_4vars/out.jsonl", 0),
    ("simba_e3_4vars", "/tmp/greysynth-bench/r20-audit/e3_4vars/out.jsonl", 0),
    ("simba_e4_4vars", "/tmp/greysynth-bench/r20-audit/e4_4vars/out.jsonl", 0),
    ("simba_e5_4vars", "/tmp/greysynth-bench/r20-audit/e5_4vars/out.jsonl", 0),
    ("simba_e1_3vars", "/tmp/greysynth-bench/wave2-r18/simba/e1_3vars/out.jsonl", 10),
    ("simba_e2_3vars", "/tmp/greysynth-bench/wave2-r18/simba/e2_3vars/out.jsonl", 10),
    ("simba_e3_3vars", "/tmp/greysynth-bench/wave2-r18/simba/e3_3vars/out.jsonl", 10),
    ("simba_e4_3vars", "/tmp/greysynth-bench/wave2-r18/simba/e4_3vars/out.jsonl", 10),
    ("loki_tiny", "/tmp/greysynth-bench/wave2-r18/external/loki_tiny/out.jsonl", 15),
    ("oses", "/tmp/r22-oses-release/out.jsonl", 4),
    ("b2_combined", "/tmp/r22-audit/b2/out.jsonl", 0),
    ("univariate64", "/tmp/r19-univariate64/out.jsonl", 0),
    ("multivariate64", "/tmp/r19-multivariate64/out.jsonl", 0),
]

# Malformed source inputs that are known invalid C/Bitvector expressions (skip from failing set).
KNOWN_MALFORMED_IDS = {
    "omvll/target_5052",
    "omvll/target_6860",
}

# Always include these flagship hard targets in core_hard if present.
MUST_INCLUDE_HARD = {
    "mba_obfuscator/target_366",
    "tigress_lvl_8/target_4174",
    "tigress_lvl_7/target_4174",
}

# Always include these flagship solved targets in regression_smoke if present.
MUST_INCLUDE_SMOKE = {
    "mba_obfuscator/target_3218",
}

_LINE_CACHE: dict[str, list[str]] = {}


def read_source_case(row: dict) -> dict | None:
    source = row.get("source")
    if not source:
        return None
    src_path = Path(source)
    if not src_path.exists():
        # Try mapping /workspaces/greysynth -> REPO_ROOT
        s = str(source).replace("/workspaces/greysynth/", str(REPO_ROOT) + "/")
        src_path = Path(s)
    if not src_path.exists():
        return None
    line_no = row.get("source_line")
    if line_no is None:
        data = json.loads(src_path.read_text(encoding="utf-8"))
        out = {
            "obf_expr": data["obf_expr"],
            "bitwidth": int(data.get("bitwidth", row.get("bitwidth", 64))),
        }
        if data.get("gt_expr"):
            out["gt_expr"] = data["gt_expr"]
        return out
    key = str(src_path)
    if key not in _LINE_CACHE:
        csv.field_size_limit(sys.maxsize)
        _LINE_CACHE[key] = src_path.read_text(encoding="utf-8").splitlines()
    lines = _LINE_CACHE[key]
    idx = int(line_no) - 1
    if idx < 0 or idx >= len(lines):
        return None
    fields = next(csv.reader([lines[idx]]))
    out = {
        "obf_expr": fields[0],
        "bitwidth": int(row.get("bitwidth", 64)),
    }
    if len(fields) >= 2 and fields[1].strip():
        out["gt_expr"] = fields[1]
    return out


def classify_row(suite: str, row: dict) -> tuple[str, int | None, int | None, int | None]:
    verdict = row.get("verdict")
    sz = row.get("size") or {}
    inp = sz.get("input")
    out = sz.get("output")
    costs = row.get("costs") or {}
    gt = (costs.get("ground_truth") or {}).get("legacy")
    if gt is None:
        agt = row.get("against_ground_truth") or {}
        gt = (agt.get("sample") or {}).get("output_size")
    if verdict not in ("proved", "proved_compositional"):
        return ("unproved", inp, out, gt)
    if suite == "obfuscatorx" and gt is not None and out is not None and out > gt:
        return ("weak", inp, out, gt)
    if suite == "permutation64" and gt is not None and out is not None and out > gt:
        return ("weak", inp, out, gt)
    if gt is None or inp is None or out is None:
        if verdict in ("proved", "proved_compositional") and inp is not None and out is not None and out < inp:
            return ("solved_nogt", inp, out, gt)
        return ("other", inp, out, gt)
    if out <= gt:
        return ("solved", inp, out, gt)
    if out <= 2 * gt or out <= 0.5 * inp:
        return ("meaningful", inp, out, gt)
    return ("weak", inp, out, gt)


def safe_filename(case_id: str) -> str:
    return case_id.replace("/", "__").replace("\\", "__").replace(":", "_") + ".json"


def write_case(dest_dir: Path, suite: str, row: dict, bucket: str, inp, out, gt) -> bool:
    payload = read_source_case(row)
    if payload is None:
        return False
    payload["target"] = f"{suite}__{row['id']}"
    payload["origin_suite"] = suite
    payload["origin_id"] = row["id"]
    payload["baseline_verdict"] = row.get("verdict")
    payload["baseline_bucket"] = bucket
    payload["baseline_input_size"] = inp
    payload["baseline_output_size"] = out
    payload["baseline_gt_size"] = gt
    suite_dir = dest_dir / suite
    suite_dir.mkdir(parents=True, exist_ok=True)
    out_file = suite_dir / safe_filename(row["id"])
    out_file.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return True


def main() -> int:
    if OUT_ROOT.exists():
        shutil.rmtree(OUT_ROOT)
    all_failing_dir = OUT_ROOT / "all_failing"
    core_hard_dir = OUT_ROOT / "core_hard"
    smoke_dir = OUT_ROOT / "regression_smoke"
    for d in (all_failing_dir, core_hard_dir, smoke_dir):
        d.mkdir(parents=True, exist_ok=True)

    manifest = {
        "all_failing": {},
        "core_hard": {},
        "regression_smoke": {},
        "totals": {"all_failing": 0, "core_hard": 0, "regression_smoke": 0},
    }

    for suite, jsonl_path, core_cap in SUITES:
        if not os.path.exists(jsonl_path):
            print(f"[skip] {suite}: missing {jsonl_path}", file=sys.stderr)
            continue
        failing_rows = []
        solved_rows = []
        with open(jsonl_path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                cid = row.get("id", "")
                if cid in KNOWN_MALFORMED_IDS:
                    continue
                bucket, inp, out, gt = classify_row(suite, row)
                if bucket in ("unproved", "weak"):
                    ratio = (out / gt) if (out and gt) else 1e9
                    priority = 0 if bucket == "unproved" else (0 if cid in MUST_INCLUDE_HARD else 1)
                    failing_rows.append((priority, -ratio, -(inp or 0), cid, row, bucket, inp, out, gt))
                elif bucket in ("solved", "solved_nogt"):
                    if (inp or 0) > (out or 0):
                        must = 0 if cid in MUST_INCLUDE_SMOKE else 1
                        solved_rows.append((must, -(inp or 0), cid, row, bucket, inp, out, gt))

        failing_rows.sort(key=lambda x: (x[0], x[1], x[2], x[3]))
        solved_rows.sort(key=lambda x: (x[0], x[1], x[2]))

        # Write ALL failing/weak cases
        n_all = 0
        for _, _, _, _, row, bucket, inp, out, gt in failing_rows:
            if write_case(all_failing_dir, suite, row, bucket, inp, out, gt):
                n_all += 1

        # Write core_hard stratified slice (all unproved + worst weak up to core_cap)
        n_core = 0
        if core_cap > 0 and failing_rows:
            unproved_all = [x for x in failing_rows if x[5] == "unproved" or x[3] in MUST_INCLUDE_HARD]
            weak_rest = [x for x in failing_rows if x not in unproved_all]
            # Take evenly across hardness spectrum (top half worst + stratified sample) so we cover diverse patterns
            remaining = max(0, core_cap - len(unproved_all))
            chosen = list(unproved_all)
            if remaining > 0 and weak_rest:
                top_n = min(len(weak_rest), max(1, remaining // 2))
                chosen.extend(weak_rest[:top_n])
                tail = weak_rest[top_n:]
                need = remaining - top_n
                if need > 0 and tail:
                    step = max(1, len(tail) / need)
                    for i in range(min(need, len(tail))):
                        chosen.append(tail[min(len(tail) - 1, int(i * step))])
            for _, _, _, _, row, bucket, inp, out, gt in chosen:
                if write_case(core_hard_dir, suite, row, bucket, inp, out, gt):
                    n_core += 1

        # Write 2 complex already-solved cases per suite for regression_smoke
        n_smoke = 0
        for _, _, _, row, bucket, inp, out, gt in solved_rows[:2]:
            if write_case(smoke_dir, suite, row, bucket, inp, out, gt):
                n_smoke += 1

        manifest["all_failing"][suite] = n_all
        manifest["core_hard"][suite] = n_core
        manifest["regression_smoke"][suite] = n_smoke
        manifest["totals"]["all_failing"] += n_all
        manifest["totals"]["core_hard"] += n_core
        manifest["totals"]["regression_smoke"] += n_smoke
        print(f"{suite:20s}: all_failing={n_all:4d}  core_hard={n_core:3d}  regression_smoke={n_smoke}")

    (OUT_ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("\nTOTALS:", manifest["totals"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
