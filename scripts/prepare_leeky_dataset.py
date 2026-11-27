#!/usr/bin/env python3
"""Convert datasets/leeky/ (Schema-1 uniform-width JSONL + panels.json) into
audit_dataset.py-compatible JSON directories under datasets/leeky/adapted/,
with optional deduplication against existing suites under datasets/.

Outputs (all under datasets/leeky/adapted/, which is git-excluded):
  - core_64/<id>.json            : all unique 64-bit cases (with panels & is_control metadata)
  - heldout_balanced64/<id>.json : 64-bit mba-balanced-v1 slice (strictly held-out generalization test)
  - dev_64/<id>.json             : 64-bit cases disjoint from mba-balanced-v1
  - cross_width/w<W>/<id>.json   : non-64-bit cases (widths 2, 8, 16, 32, 128)
  - manifest.json                : exact counts, panel membership, control flags, and overlap audit
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import re
import shutil
import sys


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_IN = REPO_ROOT / "datasets" / "leeky"
DEFAULT_OUT = DEFAULT_IN / "adapted"

WS_AND_WIDTH = re.compile(r"\s+|<\d+>")


def normalize_expr(expr: str) -> str:
    return WS_AND_WIDTH.sub("", expr)


def collect_existing_corpus_exprs(datasets_root: Path, skip_dir: Path) -> tuple[set[str], set[str], int]:
    """Scan existing datasets/ JSON/CSV files (excluding leeky/ and giant >20 MB files)
    to detect any exact or whitespace/width-normalized overlap."""
    inputs: set[str] = set()
    refs: set[str] = set()
    files_scanned = 0
    skip_resolved = skip_dir.resolve()

    for path in sorted(datasets_root.rglob("*")):
        if not path.is_file():
            continue
        resolved = path.resolve()
        if skip_resolved == resolved or skip_resolved in resolved.parents:
            continue
        if path.stat().st_size > 20_000_000:
            continue
        suffix = path.suffix.lower()
        if suffix == ".json":
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except Exception:
                continue
            if isinstance(data, dict):
                files_scanned += 1
                obf = data.get("obf_expr") or data.get("input") or data.get("expression")
                gt = data.get("gt_expr") or data.get("reference") or data.get("ground_truth")
                if isinstance(obf, str):
                    inputs.add(normalize_expr(obf))
                if isinstance(gt, str):
                    refs.add(normalize_expr(gt))
        elif suffix in (".csv", ".txt") and "hard_cases" not in path.parts:
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            files_scanned += 1
            for line in text.splitlines():
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                parts = line.split(",", 1)
                inputs.add(normalize_expr(parts[0]))
                if len(parts) > 1 and parts[1].strip():
                    refs.add(normalize_expr(parts[1]))
    return inputs, refs, files_scanned


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--in-dir", default=str(DEFAULT_IN))
    parser.add_argument("--out-dir", default=str(DEFAULT_OUT))
    parser.add_argument(
        "--check-overlap",
        action="store_true",
        help="Scan existing datasets/ for normalized expression overlap and record in manifest.json.",
    )
    parser.add_argument(
        "--dedup-overlap",
        action="store_true",
        help="Exclude cases whose normalized input matches an existing dataset (implies --check-overlap).",
    )
    args = parser.parse_args()

    in_dir = Path(args.in_dir)
    out_dir = Path(args.out_dir)
    core_path = in_dir / "core.jsonl"
    panels_path = in_dir / "panels.json"
    if not core_path.exists():
        print(f"error: missing {core_path}", file=sys.stderr)
        return 1

    rows = [json.loads(line) for line in core_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    panels_data = json.loads(panels_path.read_text(encoding="utf-8")) if panels_path.exists() else {"panels": {}}
    panels = panels_data.get("panels", {})

    id_to_panels: dict[str, list[str]] = collections.defaultdict(list)
    for panel_name, tracks in sorted(panels.items()):
        for cid in tracks.get("core", []):
            id_to_panels[cid].append(panel_name)

    existing_inputs: set[str] = set()
    existing_refs: set[str] = set()
    files_scanned = 0
    if args.check_overlap or args.dedup_overlap:
        existing_inputs, existing_refs, files_scanned = collect_existing_corpus_exprs(
            REPO_ROOT / "datasets", in_dir
        )

    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    counts = collections.Counter()
    panel_counts_64 = collections.Counter()
    overlap_input_ids: list[str] = []
    overlap_ref_ids: list[str] = []
    seen_norm_inputs: set[str] = set()
    internal_dups = 0

    for row in rows:
        cid = row["id"]
        width = int(row["width"])
        obf = row["input"]
        ref = row["reference"]
        is_control = (obf == ref)
        norm_in = normalize_expr(obf)
        norm_ref = normalize_expr(ref)

        if (width, norm_in) in seen_norm_inputs:
            internal_dups += 1
            continue
        seen_norm_inputs.add((width, norm_in))

        in_overlap = norm_in in existing_inputs
        ref_overlap = norm_ref in existing_refs
        if in_overlap:
            overlap_input_ids.append(cid)
            if args.dedup_overlap:
                counts["skipped_overlap"] += 1
                continue
        if ref_overlap:
            overlap_ref_ids.append(cid)

        case_panels = sorted(id_to_panels.get(cid, []))
        payload = {
            "target": f"leeky__{cid[:16]}",
            "leeky_id": cid,
            "obf_expr": obf,
            "gt_expr": ref,
            "bitwidth": width,
            "panels": case_panels,
            "is_control": is_control,
            "overlap_input": in_overlap,
            "overlap_reference": ref_overlap,
        }
        fname = f"{cid[:16]}_w{width}.json"
        blob = json.dumps(payload, indent=2) + "\n"

        if width == 64:
            counts["core_64"] += 1
            if is_control:
                counts["core_64_controls"] += 1
            for p in case_panels:
                panel_counts_64[p] += 1
            core_64_dir = out_dir / "core_64"
            core_64_dir.mkdir(parents=True, exist_ok=True)
            (core_64_dir / fname).write_text(blob, encoding="utf-8")

            if "mba-balanced-v1" in case_panels:
                counts["heldout_balanced64"] += 1
                ho_dir = out_dir / "heldout_balanced64"
                ho_dir.mkdir(parents=True, exist_ok=True)
                (ho_dir / fname).write_text(blob, encoding="utf-8")
            else:
                counts["dev_64"] += 1
                dev_dir = out_dir / "dev_64"
                dev_dir.mkdir(parents=True, exist_ok=True)
                (dev_dir / fname).write_text(blob, encoding="utf-8")
        else:
            counts[f"width_{width}"] += 1
            cw_dir = out_dir / "cross_width" / f"w{width}"
            cw_dir.mkdir(parents=True, exist_ok=True)
            (cw_dir / fname).write_text(blob, encoding="utf-8")

    manifest = {
        "source": str(core_path.relative_to(REPO_ROOT)),
        "total_records": len(rows),
        "internal_duplicates_skipped": internal_dups,
        "overlap_audit": {
            "checked": bool(args.check_overlap or args.dedup_overlap),
            "deduped": bool(args.dedup_overlap),
            "existing_files_scanned": files_scanned,
            "input_overlap_count": len(overlap_input_ids),
            "reference_overlap_count": len(overlap_ref_ids),
            "sample_input_overlaps": overlap_input_ids[:20],
        },
        "counts": dict(sorted(counts.items())),
        "panel_counts_64": dict(sorted(panel_counts_64.items())),
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
