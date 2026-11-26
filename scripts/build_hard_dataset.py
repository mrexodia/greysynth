#!/usr/bin/env python3
"""Build focused non-exact (out > GT or unproved) and solved-regression datasets
from GreySynth audit JSONLs, with support for overlaying newer audit runs to
monotonically shrink the remaining unsolved set.

Outputs (by default under datasets/hard_cases/, which is git-excluded):
  - all_non_exact/<suite>/*.json      : EVERY parseable non-GB expression not yet proved <= GT
  - untested_non_exact/<suite>/*.json : subset of all_non_exact/ not yet seen in any --overlay JSONL
  - core_hard/<suite>/*.json          : fast stratified slice of all_non_exact/
  - giant_gb_omvll/*.json             : 7 pre-existing >85 MB-1.17 GB flat-text OMVLL files (kept out of parallel runs)
  - regression_smoke/<suite>/*.json   : 2 complex already-solved cases per suite (for regression guards)
  - manifest.json                     : exact provenance, per-suite counts & corpus-wide solve percentages
"""

from __future__ import annotations

import argparse
import csv
import json
import os
from pathlib import Path
import shutil
import sys


REPO_ROOT = Path(__file__).resolve().parent.parent
OUT_ROOT = REPO_ROOT / "datasets" / "hard_cases"

# Latest baseline audit JSONL per suite (32 audited suites, 54,105 total expressions).
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
    ("pldi_nonpoly", "/tmp/greysynth-bench/full-audit-r18-final/pldi_nonpoly/out.jsonl", 25),
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
    ("oses", "/tmp/r22-oses-release/out.jsonl", 10),
    ("b2_combined", "/tmp/r22-audit/b2/out.jsonl", 0),
    ("univariate64", "/tmp/r19-univariate64/out.jsonl", 0),
    ("multivariate64", "/tmp/r19-multivariate64/out.jsonl", 0),
]

# Malformed source inputs that are known invalid C/Bitvector expressions.
KNOWN_MALFORMED_IDS = {
    "omvll/target_5052",
    "omvll/target_6860",
    "loki/line_0001001",
}

# Pre-existing >85 MB-1.17 GB unshared flat-text OMVLL files (separated from parallel runs).
GIANT_GB_IDS = {
    "omvll/target_3716",
    "omvll/target_773",
    "omvll/target_802",
    "omvll/target_800",
    "omvll/target_4687",
    "omvll/target_4678",
    "omvll/target_533",
}

# Always include these flagship hard targets in core_hard if still non-exact.
MUST_INCLUDE_HARD = {
    "mba_obfuscator/target_366",
    "mba_obfuscator/target_1685",
    "tigress_lvl_8/target_4174",
    "tigress_lvl_7/target_4174",
    "tigress_lvl_8/target_5856",
    "omvll/target_771",
}

# Always include these flagship solved targets in regression_smoke if present.
MUST_INCLUDE_SMOKE = {
    "mba_obfuscator/target_3218",
}

_LINE_CACHE: dict[str, list[str]] = {}


def safe_filename(case_id: str) -> str:
    return case_id.replace("/", "__").replace("\\", "__").replace(":", "_") + ".json"


def load_overlays(paths: list[str]) -> dict[tuple[str, str], dict]:
    """Load newer audit JSONLs in order (later overlays take precedence)."""
    overlays: dict[tuple[str, str], dict] = {}
    for raw_path in paths:
        p = Path(raw_path)
        if not p.exists():
            print(f"[warn] overlay missing: {raw_path}", file=sys.stderr)
            continue
        loaded = 0
        with p.open(encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                origin_suite = None
                origin_id = None
                src = row.get("source")
                if src and Path(src).exists():
                    try:
                        meta = json.loads(Path(src).read_text(encoding="utf-8"))
                        origin_suite = meta.get("origin_suite")
                        origin_id = meta.get("origin_id")
                    except Exception:
                        pass
                if not origin_suite or not origin_id:
                    # Fallback: parse <prefix>/<suite>/<origin_id_with___>
                    parts = str(row.get("id", "")).split("/")
                    if len(parts) >= 3:
                        origin_suite = parts[-2]
                        origin_id = parts[-1].replace("__", "/")
                if origin_suite and origin_id:
                    overlays[(origin_suite, origin_id)] = row
                    loaded += 1
        print(f"[overlay] loaded {loaded} rows from {raw_path}")
    return overlays


def read_source_case(row: dict) -> dict | None:
    source = row.get("source")
    if not source:
        return None
    src_path = Path(source)
    if not src_path.exists():
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


def extract_sizes(row: dict) -> tuple[int | None, int | None, int | None]:
    sz = row.get("size") or {}
    costs = row.get("costs") or {}
    inp = (costs.get("input") or {}).get("legacy")
    if inp is None:
        inp = sz.get("input")
    out = (costs.get("output") or {}).get("legacy")
    if out is None:
        out = sz.get("output")
    gt = (costs.get("ground_truth") or {}).get("legacy")
    if gt is None:
        agt = row.get("against_ground_truth") or {}
        gt = (agt.get("sample") or {}).get("output_size")
    return inp, out, gt


def classify_row(row: dict) -> tuple[str, int | None, int | None, int | None]:
    verdict = row.get("verdict")
    inp, out, gt = extract_sizes(row)
    if verdict not in ("proved", "proved_compositional"):
        return ("unproved", inp, out, gt)
    if gt is None or gt <= 0 or inp is None or out is None:
        if inp is not None and out is not None and out < inp:
            return ("solved_nogt", inp, out, gt)
        return ("other_nogt", inp, out, gt)
    if out <= gt:
        return ("exact_gt", inp, out, gt)
    if out <= 2 * gt or out <= 0.5 * inp:
        return ("meaningful_gt", inp, out, gt)
    return ("weak_gt", inp, out, gt)


def write_case(
    dest_dir: Path,
    suite: str,
    baseline_row: dict,
    active_row: dict,
    bucket: str,
    inp: int | None,
    out: int | None,
    gt: int | None,
    tested_by_overlay: bool,
    flat: bool = False,
) -> bool:
    payload = read_source_case(baseline_row)
    if payload is None:
        return False
    payload["target"] = f"{suite}__{baseline_row['id']}"
    payload["origin_suite"] = suite
    payload["origin_id"] = baseline_row["id"]
    payload["baseline_verdict"] = active_row.get("verdict")
    payload["baseline_bucket"] = bucket
    payload["baseline_input_size"] = inp
    payload["baseline_output_size"] = out
    payload["baseline_gt_size"] = gt
    payload["tested_by_overlay"] = tested_by_overlay
    suite_dir = dest_dir if flat else (dest_dir / suite)
    suite_dir.mkdir(parents=True, exist_ok=True)
    out_file = suite_dir / safe_filename(baseline_row["id"])
    out_file.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--overlay",
        action="append",
        default=[],
        help="Path to a newer audit out.jsonl to overlay onto baseline suites (repeatable).",
    )
    parser.add_argument(
        "--out-root",
        default=str(OUT_ROOT),
        help=f"Output root directory (default: {OUT_ROOT})",
    )
    args = parser.parse_args()

    out_root = Path(args.out_root)
    overlays = load_overlays(args.overlay)

    all_non_exact_dir = out_root / "all_non_exact"
    untested_dir = out_root / "untested_non_exact"
    core_hard_dir = out_root / "core_hard"
    giant_gb_dir = out_root / "giant_gb_omvll"
    smoke_dir = out_root / "regression_smoke"

    # Rebuild managed directories cleanly (never delete unrelated files outside out_root).
    for d in (all_non_exact_dir, untested_dir, core_hard_dir, giant_gb_dir, smoke_dir):
        if d.exists():
            shutil.rmtree(d)
        d.mkdir(parents=True, exist_ok=True)
    # Remove stale legacy all_failing directory if present to avoid confusion.
    legacy_failing = out_root / "all_failing"
    if legacy_failing.exists():
        shutil.rmtree(legacy_failing)

    manifest: dict = {
        "overlays": args.overlay,
        "all_non_exact": {},
        "untested_non_exact": {},
        "core_hard": {},
        "regression_smoke": {},
        "corpus_summary": {
            "total_audited": 0,
            "malformed_skipped": 0,
            "giant_gb_separated": 0,
            "proved": 0,
            "refuted": 0,
            "with_gt": 0,
            "exact_gt": 0,
            "le_125x_gt": 0,
            "le_150x_gt": 0,
            "le_200x_gt": 0,
        },
        "totals": {
            "all_non_exact": 0,
            "untested_non_exact": 0,
            "core_hard": 0,
            "giant_gb_omvll": 0,
            "regression_smoke": 0,
        },
    }
    cs = manifest["corpus_summary"]

    for suite, jsonl_path, core_cap in SUITES:
        if not os.path.exists(jsonl_path):
            print(f"[skip] {suite}: missing {jsonl_path}", file=sys.stderr)
            continue

        non_exact_rows = []
        solved_rows = []
        n_giant = 0

        with open(jsonl_path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                b_row = json.loads(line)
                cid = b_row.get("id", "")
                cs["total_audited"] += 1

                if cid in KNOWN_MALFORMED_IDS:
                    cs["malformed_skipped"] += 1
                    continue

                tested = (suite, cid) in overlays
                a_row = overlays.get((suite, cid), b_row)
                bucket, inp, out, gt = classify_row(a_row)

                # Keep regression_smoke anchored to baseline solved rows so dune tests stay stable.
                b_bucket, b_inp, b_out, b_gt = classify_row(b_row)
                if b_bucket in ("exact_gt", "solved_nogt") and (b_inp or 0) > (b_out or 0):
                    must = 0 if cid in MUST_INCLUDE_SMOKE else 1
                    solved_rows.append((must, -(b_inp or 0), cid, b_row, b_row, b_bucket, b_inp, b_out, b_gt))

                if a_row.get("verdict") == "refuted":
                    cs["refuted"] += 1
                if a_row.get("verdict") in ("proved", "proved_compositional"):
                    cs["proved"] += 1
                if gt is not None and gt > 0:
                    cs["with_gt"] += 1
                    if a_row.get("verdict") in ("proved", "proved_compositional") and out is not None:
                        ratio = out / gt
                        if out <= gt:
                            cs["exact_gt"] += 1
                        if ratio <= 1.25:
                            cs["le_125x_gt"] += 1
                        if ratio <= 1.50:
                            cs["le_150x_gt"] += 1
                        if ratio <= 2.00:
                            cs["le_200x_gt"] += 1

                if cid in GIANT_GB_IDS:
                    cs["giant_gb_separated"] += 1
                    if write_case(giant_gb_dir, suite, b_row, a_row, bucket, inp, out, gt, tested, flat=True):
                        n_giant += 1
                    continue

                if bucket in ("unproved", "weak_gt", "meaningful_gt"):
                    ratio = (out / gt) if (out and gt) else 1e9
                    priority = 0 if bucket == "unproved" else (0 if cid in MUST_INCLUDE_HARD else (1 if bucket == "weak_gt" else 2))
                    non_exact_rows.append((priority, -ratio, -(inp or 0), cid, b_row, a_row, bucket, inp, out, gt, tested))

        non_exact_rows.sort(key=lambda x: (x[0], x[1], x[2], x[3]))
        solved_rows.sort(key=lambda x: (x[0], x[1], x[2]))

        n_non_exact = 0
        n_untested = 0
        for _, _, _, _, b_row, a_row, bucket, inp, out, gt, tested in non_exact_rows:
            if write_case(all_non_exact_dir, suite, b_row, a_row, bucket, inp, out, gt, tested):
                n_non_exact += 1
            if not tested:
                if write_case(untested_dir, suite, b_row, a_row, bucket, inp, out, gt, tested):
                    n_untested += 1

        n_core = 0
        if core_cap > 0 and non_exact_rows:
            must_rows = [x for x in non_exact_rows if x[6] == "unproved" or x[3] in MUST_INCLUDE_HARD]
            rest_rows = [x for x in non_exact_rows if x not in must_rows]
            remaining = max(0, core_cap - len(must_rows))
            chosen = list(must_rows)
            if remaining > 0 and rest_rows:
                top_n = min(len(rest_rows), max(1, remaining // 2))
                chosen.extend(rest_rows[:top_n])
                tail = rest_rows[top_n:]
                need = remaining - top_n
                if need > 0 and tail:
                    step = max(1.0, len(tail) / need)
                    for i in range(min(need, len(tail))):
                        chosen.append(tail[min(len(tail) - 1, int(i * step))])
            for _, _, _, _, b_row, a_row, bucket, inp, out, gt, tested in chosen:
                if write_case(core_hard_dir, suite, b_row, a_row, bucket, inp, out, gt, tested):
                    n_core += 1

        n_smoke = 0
        for _, _, _, b_row, a_row, bucket, inp, out, gt in solved_rows[:2]:
            if write_case(smoke_dir, suite, b_row, a_row, bucket, inp, out, gt, False):
                n_smoke += 1

        manifest["all_non_exact"][suite] = n_non_exact
        manifest["untested_non_exact"][suite] = n_untested
        manifest["core_hard"][suite] = n_core
        manifest["regression_smoke"][suite] = n_smoke
        manifest["totals"]["all_non_exact"] += n_non_exact
        manifest["totals"]["untested_non_exact"] += n_untested
        manifest["totals"]["core_hard"] += n_core
        manifest["totals"]["giant_gb_omvll"] += n_giant
        manifest["totals"]["regression_smoke"] += n_smoke
        print(
            f"{suite:20s}: non_exact={n_non_exact:4d}  untested={n_untested:4d}  "
            f"core_hard={n_core:3d}  smoke={n_smoke}"
        )

    parseable = cs["total_audited"] - cs["malformed_skipped"]
    cs["proved_pct_parseable"] = round(100.0 * cs["proved"] / max(parseable, 1), 4)
    cs["exact_gt_pct"] = round(100.0 * cs["exact_gt"] / max(cs["with_gt"], 1), 3)
    cs["le_125x_pct"] = round(100.0 * cs["le_125x_gt"] / max(cs["with_gt"], 1), 3)
    cs["le_150x_pct"] = round(100.0 * cs["le_150x_gt"] / max(cs["with_gt"], 1), 3)
    cs["le_200x_pct"] = round(100.0 * cs["le_200x_gt"] / max(cs["with_gt"], 1), 3)

    (out_root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("\nTOTALS:", manifest["totals"])
    print("CORPUS SUMMARY:", json.dumps(cs, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
