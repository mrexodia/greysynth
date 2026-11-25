#!/usr/bin/env python3
"""Regression checks for the audit's independent-proof result contract."""

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "audit_dataset", Path(__file__).resolve().parents[1] / "scripts" / "audit_dataset.py")
audit = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = audit
spec.loader.exec_module(audit)


class ProofReporting(unittest.TestCase):
    def test_empty_csv_ground_truth_is_absent(self):
        with tempfile.TemporaryDirectory() as directory:
            dataset = Path(directory) / "adapted.csv"
            dataset.write_text("x,\n")
            cases = audit.collect_cases([dataset], 64)
            self.assertEqual(len(cases), 1)
            self.assertNotIn("gt_expr", cases[0].data)

    def test_independent_replay_resolves_unknown_but_preserves_direct_result(self):
        direct = {"verdict": "unknown", "sample": {"status": "sampled"}}
        self.assertEqual(audit.combined_verdict(direct, {"status": "proved_compositional"}),
                         "proved_compositional")
        self.assertEqual(direct["verdict"], "unknown")

    def test_no_replay_never_promotes_an_unknown(self):
        self.assertEqual(audit.combined_verdict({"verdict": "unknown"}, {"status": "not_run"}),
                         "unknown")

    def test_refuted_edge_is_certificate_error_not_final_output_refutation(self):
        self.assertEqual(audit.combined_verdict({"verdict": "unknown"}, {"status": "refuted"}),
                         "error")

    def test_sample_counterexample_cannot_be_hidden_by_replay(self):
        direct = {"verdict": "unknown", "sample": {"status": "refuted"}}
        self.assertEqual(audit.combined_verdict(direct, {"status": "proved_compositional"}), "error")
        self.assertEqual(audit.combined_verdict(direct, {"status": "unknown"}), "refuted")

    def test_invalid_certificate_is_reported_even_when_direct_proof_succeeds(self):
        self.assertEqual(audit.combined_verdict({"verdict": "proved"}, {"status": "invalid_certificate"}),
                         "error")

    def test_summary_distinguishes_proof_routes_from_sample_agreement(self):
        rows = []
        for verdict in ("proved", "proved_compositional", "unknown", "sampled"):
            rows.append({"verdict": verdict, "size": {"relation": "strict_decrease"},
                         "synthesis_status": "ok", "wall_seconds": 0})
        summary = audit.summarize(rows, {}, True)
        self.assertEqual(summary["proved_strict_decreases"], 2)
        self.assertEqual(summary["direct_proved_strict_decreases"], 1)
        self.assertEqual(summary["compositional_proved_strict_decreases"], 1)
        self.assertEqual(summary["verdict_counts"]["unknown"], 1)

    def test_summary_reports_ground_truth_quality_and_compression(self):
        rows = [
            {"verdict": "proved", "size": {"relation": "strict_decrease"},
             "synthesis_status": "ok", "wall_seconds": 0,
             "costs": {"input": {"legacy": 20, "paper_ast": 24},
                       "output": {"legacy": 5, "paper_ast": 6},
                       "ground_truth": {"legacy": 4, "paper_ast": 6}}},
            {"verdict": "proved", "size": {"relation": "strict_decrease"},
             "synthesis_status": "ok", "wall_seconds": 0,
             "costs": {"input": {"legacy": 9, "paper_ast": 12},
                       "output": {"legacy": 3, "paper_ast": 4},
                       "ground_truth": {"legacy": 3, "paper_ast": 4}}},
        ]
        metrics = audit.summarize(rows, {}, True)["cost_metrics"]
        self.assertAlmostEqual(
            metrics["legacy"]["quality_output_over_ground_truth"]["arithmetic_mean"],
            1.125)
        self.assertAlmostEqual(
            metrics["legacy"]["compression_input_over_output"]["geometric_mean"],
            (12.0) ** 0.5)


if __name__ == "__main__":
    unittest.main()
