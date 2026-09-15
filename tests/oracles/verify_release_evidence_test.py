#!/usr/bin/env python3
"""Check historical SMT evidence compatibility without changing retained results."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import verify_release_evidence as evidence


class SMTNamingTests(unittest.TestCase):
    def summary(self, missing_key: str) -> dict:
        counts = dict.fromkeys(evidence.SMT_COUNT_KEYS, 0)
        counts["generated"] = counts["exact_bit_cases"] = 1
        counts[missing_key] = counts.pop("missing_floatlib")
        return {"counts": counts, "status": "pass", "mismatch_samples": []}

    def test_current_and_historical_counts_normalize_without_mutation(self) -> None:
        expected = self.summary("missing_floatlib")["counts"]
        for key in ("missing_floatlib", "missing_floatlean"):
            with self.subTest(key=key):
                summary = self.summary(key)
                original = copy.deepcopy(summary)
                self.assertEqual(evidence.smt_counts(summary, "fixture"), expected)
                self.assertEqual(summary, original)

    def test_ambiguous_or_unknown_count_keys_fail(self) -> None:
        for key in ("missing_floatlean", "unexpected"):
            with self.subTest(key=key):
                summary = self.summary("missing_floatlib")
                summary["counts"][key] = 0
                with self.assertRaisesRegex(ValueError, "unexpected SMT count keys"):
                    evidence.smt_counts(summary, "fixture")

    def test_historical_missing_result_still_fails(self) -> None:
        summary = self.summary("missing_floatlean")
        summary["counts"]["missing_floatlean"] = 1
        with self.assertRaisesRegex(ValueError, "missing_floatlib is nonzero"):
            evidence.smt_counts(summary, "fixture")

    def check_rows(self, bits_column: str, match: str = "true") -> None:
        text = (
            "id\toperation\tsource\tdestination\trounding\toperands\t"
            f"solver_kind\tsolver_bits\t{bits_column}\tmatch\n"
            f"0\tadd\tf16\tf16\trne\t0000,0000\tzero\t0000\t0000\t{match}\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "results.tsv"
            path.write_text(text)
            evidence.verify_smt_results(path, 1)
            self.assertEqual(path.read_text(), text)

    def test_current_and_historical_result_headers_pass(self) -> None:
        for key in ("floatlib_bits", "floatlean_bits"):
            with self.subTest(key=key):
                self.check_rows(key)

    def test_unknown_header_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "header"):
            self.check_rows("unexpected_bits")

    def test_historical_mismatch_still_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "SMT mismatch retained"):
            self.check_rows("floatlean_bits", match="false")


if __name__ == "__main__":
    unittest.main()
