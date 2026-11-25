from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts import adapt_dataset as adapter


class AdaptDatasetTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def digest(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def manifest(self, output: Path) -> dict:
        return json.loads(adapter.provenance_path(output).read_text(encoding="utf-8"))

    def test_xyntia_shifts_hashes_counts_idempotence_and_nonmutation(self) -> None:
        source = self.root / "b2"
        source.write_text("a lsl b\nc lsr d\ne + f\n", encoding="utf-8")
        source_before = source.read_bytes()
        output = self.root / "adapted-b2"
        adapter.run("xyntia-shifts", source, output, 32)
        self.assertEqual(source.read_bytes(), source_before)
        data = json.loads((output / "target_000001.json").read_text())
        self.assertEqual(data, {"target": "target_000001", "obf_expr": "a << b", "bitwidth": 32})
        manifest = self.manifest(output)
        self.assertEqual(manifest["row_count"], 3)
        self.assertEqual(manifest["source"]["sha256"], self.digest(source))
        self.assertEqual(manifest["output"]["sha256"], adapter.sha256_tree(output))
        self.assertEqual(manifest["rows"][0]["transformations"]["lsl_to_lshift"], 1)
        once, _ = adapter.adapt_xyntia_expression("x lsl y lsr z")
        twice, counts = adapter.adapt_xyntia_expression(once)
        self.assertEqual(once, twice)
        self.assertEqual(sum(counts.values()), 0)

    def test_oses_all_rules_are_per_field_and_idempotent(self) -> None:
        source = self.root / "oses.txt"
        source.write_text(
            "# expression<TAB>gt\n(+2*~X[0]) // 0x61\tX[0] / 0x61\n"
            "X[1]+(+X[2]) (needs Z3)\tX[1]+X[2]\n"
            "x+y\t-\n"
            "x\t(constant 123)\n",
            encoding="utf-8",
        )
        source_before = source.read_bytes()
        output = self.root / "oses.csv"
        adapter.run("oses", source, output)
        self.assertEqual(source.read_bytes(), source_before)
        with output.open(newline="", encoding="utf-8") as stream:
            rows = list(csv.reader(stream))
        self.assertEqual(rows[0], ["(2*~X_0) / 0x61", "X_0 / 0x61"])
        self.assertEqual(rows[1], ["X_1+(X_2)", "X_1+X_2"])
        self.assertEqual(rows[2], ["x+y", ""])
        self.assertEqual(rows[3], ["x", "123"])
        self.assertEqual(self.manifest(output)["rows"][3]["transformations"]
                         ["constant_ground_truth_annotation_unwrapped"], 1)
        self.assertEqual(self.manifest(output)["rows"][2]["transformations"]
                         ["missing_ground_truth_sentinel_removed"], 1)
        self.assertEqual(self.manifest(output)["rows"][1]["transformations"]
                         ["trailing_human_annotation_removed"], 1)
        manifest = self.manifest(output)
        counts = manifest["rows"][0]["transformations"]
        self.assertEqual(counts["unary_plus_removed"], 1)
        self.assertEqual(counts["floor_div_to_unsigned_bv_div"], 1)
        self.assertEqual(counts["indexed_variable_to_identifier"], 2)
        self.assertEqual(manifest["source"]["sha256"], self.digest(source))
        self.assertEqual(manifest["output"]["sha256"], self.digest(output))
        once, _ = adapter.adapt_oses_expression("(+X[0]) // 0x61")
        twice, counts = adapter.adapt_oses_expression(once)
        self.assertEqual(once, twice)
        self.assertEqual(sum(counts.values()), 0)

    def test_floki_removes_exactly_one_brace_and_preserves_fields(self) -> None:
        source = self.root / "mba_info"
        source.mkdir()
        first = {"target": "target_0", "obf_expr": "}(x+y)", "gt_expr": "x+y",
                 "bitwidth": 64, "variables": ["x", "y"]}
        second = {"target": "target_1", "obf_expr": "x", "gt_expr": "x", "bitwidth": 64}
        (source / "target_0.json").write_text(json.dumps(first), encoding="utf-8")
        (source / "target_1.json").write_text(json.dumps(second), encoding="utf-8")
        (source / "target_0_sizes.json").write_text('{"obf_sz": 3}\n', encoding="utf-8")
        source_hash = adapter.sha256_tree(source)
        output = self.root / "clean-mba_info"
        adapter.run("floki-brace", source, output)
        self.assertEqual(adapter.sha256_tree(source), source_hash)
        cleaned = json.loads((output / "target_0.json").read_text())
        expected = dict(first, obf_expr="(x+y)")
        self.assertEqual(cleaned, expected)
        self.assertEqual((output / "target_0_sizes.json").read_text(), '{"obf_sz": 3}\n')
        manifest = self.manifest(output)
        self.assertEqual(manifest["row_count"], 2)
        self.assertEqual(manifest["rows"][0]["transformations"]["leading_stray_brace_removed"], 1)
        second_output = self.root / "clean-again"
        adapter.run("floki-brace", output, second_output)
        second_manifest = self.manifest(second_output)
        self.assertTrue(all(row["transformations"]["leading_stray_brace_removed"] == 0
                            for row in second_manifest["rows"]))

    def test_refuses_mutation_and_existing_outputs(self) -> None:
        source = self.root / "source"
        source.write_text("x\n", encoding="utf-8")
        with self.assertRaises(ValueError):
            adapter.run("xyntia-shifts", source, source)
        output = self.root / "out"
        output.mkdir()
        with self.assertRaises(FileExistsError):
            adapter.run("xyntia-shifts", source, output)


if __name__ == "__main__":
    unittest.main()
