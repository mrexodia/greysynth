#!/usr/bin/env python3
"""Explicit, provenance-preserving adapters for external MBA dialects.

The adapters never modify their inputs and refuse to write below this checkout's
``datasets`` directory.  Every output has a sibling ``.provenance.json`` whose
hashes cover exact file bytes (and relative names for directory outputs).
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
from typing import Callable

DIALECTS = ("xyntia-shifts", "oses", "floki-brace")
INDEXED_VARIABLE = re.compile(r"\b([A-Za-z_]\w*)\[(\d+)\]")
FLOOR_DIVISION = re.compile(r"(?<=\s)//(?=\s)")
OSES_TRAILING_ANNOTATION = re.compile(r"\s+\((?:needs Z3|with resets\s*=\s*\d+)\)\s*$")
OSES_CONSTANT_GROUND_TRUTH = re.compile(r"\(constant\s+([+-]?(?:0[xX][0-9A-Fa-f]+|\d+))\)")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def sha256_tree(path: Path) -> str:
    """Hash a directory independent of its absolute location."""
    digest = hashlib.sha256()
    for child in sorted(item for item in path.rglob("*") if item.is_file()):
        relative = child.relative_to(path).as_posix().encode("utf-8")
        data = child.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()


def source_hash(path: Path) -> str:
    return sha256_tree(path) if path.is_dir() else sha256_file(path)


def provenance_path(output: Path) -> Path:
    return output.with_name(output.name + ".provenance.json")


def replace_count(pattern: re.Pattern[str], replacement: str, text: str) -> tuple[str, int]:
    return pattern.subn(replacement, text)


def adapt_xyntia_expression(expression: str) -> tuple[str, dict[str, int]]:
    expression, lsl = re.subn(r"\blsl\b", "<<", expression)
    expression, lsr = re.subn(r"\blsr\b", ">>", expression)
    return expression, {"lsl_to_lshift": lsl, "lsr_to_rshift": lsr}


def strip_unary_plus(expression: str) -> tuple[str, int]:
    """Remove unary '+' tokens without changing surrounding whitespace."""
    remove: list[int] = []
    for index, character in enumerate(expression):
        if character != "+":
            continue
        previous = index - 1
        while previous >= 0 and expression[previous].isspace():
            previous -= 1
        following = index + 1
        while following < len(expression) and expression[following].isspace():
            following += 1
        unary_context = previous < 0 or expression[previous] in "(,+-*/%&|^~<>"
        operand_follows = following < len(expression) and (
            expression[following].isalnum()
            or expression[following] in "(_~-"
        )
        if unary_context and operand_follows:
            remove.append(index)
    if not remove:
        return expression, 0
    removed = set(remove)
    return "".join(ch for index, ch in enumerate(expression) if index not in removed), len(remove)


def adapt_oses_expression(expression: str) -> tuple[str, dict[str, int]]:
    expression, unary = strip_unary_plus(expression)
    expression, division = replace_count(FLOOR_DIVISION, "/", expression)
    expression, indexed = replace_count(INDEXED_VARIABLE, r"\1_\2", expression)
    expression, annotation = replace_count(OSES_TRAILING_ANNOTATION, "", expression)
    return expression, {
        "unary_plus_removed": unary,
        "floor_div_to_unsigned_bv_div": division,
        "indexed_variable_to_identifier": indexed,
        "trailing_human_annotation_removed": annotation,
        "missing_ground_truth_sentinel_removed": 0,
        "constant_ground_truth_annotation_unwrapped": 0,
    }


def changed_sample(row: int, before: str, after: str, field: str = "expression") -> dict | None:
    if before == after:
        return None
    return {"row": row, "field": field, "before": before, "after": after}


def ensure_output(input_path: Path, output: Path) -> None:
    source = input_path.resolve()
    target = output.resolve()
    if source == target or (source.is_dir() and source in target.parents):
        raise ValueError("output must not equal or be nested below the input")
    datasets = (Path(__file__).resolve().parent.parent / "datasets").resolve()
    if target == datasets or datasets in target.parents:
        raise ValueError("refusing to write generated data below datasets/")
    manifest = provenance_path(output)
    if output.exists() or manifest.exists():
        raise FileExistsError(f"output or provenance manifest already exists: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)


def adapt_xyntia(input_path: Path, output: Path, bitwidth: int) -> tuple[list[dict], list[dict]]:
    if not input_path.is_file():
        raise ValueError("xyntia-shifts input must be a file")
    output.mkdir()
    rows: list[dict] = []
    samples: list[dict] = []
    case = 0
    for line_number, raw in enumerate(input_path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        case += 1
        adapted, counts = adapt_xyntia_expression(raw)
        relative = f"target_{case:06d}.json"
        payload = {"target": f"target_{case:06d}", "obf_expr": adapted, "bitwidth": bitwidth}
        (output / relative).write_text(
            json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        rows.append({"row": case, "source_line": line_number, "output": relative,
                     "transformations": counts})
        sample = changed_sample(case, raw, adapted)
        if sample is not None and len(samples) < 8:
            samples.append(sample)
    return rows, samples


def adapt_oses(input_path: Path, output: Path, _bitwidth: int) -> tuple[list[dict], list[dict]]:
    if not input_path.is_file():
        raise ValueError("oses input must be a file")
    rows: list[dict] = []
    samples: list[dict] = []
    with input_path.open(encoding="utf-8", newline="") as source, \
         output.open("w", encoding="utf-8", newline="") as destination:
        writer = csv.writer(destination, lineterminator="\n")
        case = 0
        for line_number, raw in enumerate(source, 1):
            if not raw.strip() or raw.lstrip().startswith("#"):
                continue
            fields = raw.rstrip("\r\n").split("\t")
            if len(fields) != 2:
                raise ValueError(f"{input_path}:{line_number}: expected expression<TAB>ground_truth")
            case += 1
            output_fields: list[str] = []
            totals = {"unary_plus_removed": 0, "floor_div_to_unsigned_bv_div": 0,
                      "indexed_variable_to_identifier": 0,
                      "trailing_human_annotation_removed": 0,
                      "missing_ground_truth_sentinel_removed": 0,
                      "constant_ground_truth_annotation_unwrapped": 0}
            field_counts: dict[str, dict[str, int]] = {}
            for name, expression in zip(("obf", "gt"), fields):
                constant_gt = OSES_CONSTANT_GROUND_TRUTH.fullmatch(expression.strip())
                if name == "gt" and expression.strip() == "-":
                    adapted = ""
                    counts = {key: 0 for key in totals}
                    counts["missing_ground_truth_sentinel_removed"] = 1
                elif name == "gt" and constant_gt is not None:
                    adapted = constant_gt.group(1)
                    counts = {key: 0 for key in totals}
                    counts["constant_ground_truth_annotation_unwrapped"] = 1
                else:
                    adapted, counts = adapt_oses_expression(expression)
                output_fields.append(adapted)
                field_counts[name] = counts
                for key, value in counts.items():
                    totals[key] += value
                sample = changed_sample(case, expression, adapted, name)
                if sample is not None and len(samples) < 8:
                    samples.append(sample)
            writer.writerow(output_fields)
            rows.append({"row": case, "source_line": line_number,
                         "transformations": totals, "fields": field_counts})
    return rows, samples


def adapt_floki(input_path: Path, output: Path, _bitwidth: int) -> tuple[list[dict], list[dict]]:
    if not input_path.is_dir():
        raise ValueError("floki-brace input must be a directory")
    output.mkdir()
    rows: list[dict] = []
    samples: list[dict] = []
    case = 0
    for source in sorted(item for item in input_path.rglob("*") if item.is_file()):
        relative = source.relative_to(input_path)
        destination = output / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source.suffix.lower() != ".json" or source.name.endswith("_sizes.json"):
            shutil.copyfile(source, destination)
            continue
        data = json.loads(source.read_text(encoding="utf-8"))
        if not isinstance(data, dict) or not isinstance(data.get("obf_expr"), str):
            shutil.copyfile(source, destination)
            continue
        case += 1
        before = data["obf_expr"]
        count = int(before.startswith("}"))
        if count:
            data["obf_expr"] = before[1:]
        destination.write_text(json.dumps(data, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        rows.append({"row": case, "source": relative.as_posix(),
                     "output": relative.as_posix(),
                     "transformations": {"leading_stray_brace_removed": count}})
        sample = changed_sample(case, before, data["obf_expr"], "obf_expr")
        if sample is not None and len(samples) < 8:
            samples.append(sample)
    return rows, samples


ADAPTERS: dict[str, Callable[[Path, Path, int], tuple[list[dict], list[dict]]]] = {
    "xyntia-shifts": adapt_xyntia,
    "oses": adapt_oses,
    "floki-brace": adapt_floki,
}


def run(dialect: str, input_path: Path, output: Path, bitwidth: int = 64) -> Path:
    if bitwidth <= 0:
        raise ValueError("bitwidth must be positive")
    input_path = input_path.resolve()
    output = output.resolve()
    if not input_path.exists():
        raise FileNotFoundError(input_path)
    ensure_output(input_path, output)
    before_hash = source_hash(input_path)
    rows, samples = ADAPTERS[dialect](input_path, output, bitwidth)
    after_hash = source_hash(input_path)
    if before_hash != after_hash:
        raise RuntimeError("input changed while adapting")
    manifest = {
        "format": "greysynth-dataset-adapter-provenance-v1",
        "dialect": dialect,
        "source": {"path": str(input_path), "sha256": before_hash},
        "output": {"path": str(output), "sha256": source_hash(output)},
        "row_count": len(rows),
        "rows": rows,
        "samples": samples,
    }
    manifest_path = provenance_path(output)
    manifest_path.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return manifest_path


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dialect", choices=DIALECTS, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--bitwidth", type=int, default=64)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        manifest = run(args.dialect, args.input, args.output, args.bitwidth)
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as error:
        print(f"adapt_dataset: {error}", file=sys.stderr)
        return 2
    print(manifest)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
