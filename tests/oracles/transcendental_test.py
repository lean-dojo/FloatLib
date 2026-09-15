#!/usr/bin/env python3
"""Focused unit tests for the transcendental ULP reporter."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

MODULE_PATH = Path(__file__).with_name("transcendental_report.py")
SPEC = importlib.util.spec_from_file_location("transcendental_report", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
REPORT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = REPORT
SPEC.loader.exec_module(REPORT)


class EncodingTests(unittest.TestCase):
    def test_binary32_adjacent_positive_values(self) -> None:
        fmt = REPORT.FORMAT_INFO["binary32"]
        self.assertEqual(REPORT.ulp_distance(0x3F800000, 0x3F800001, fmt), 1)

    def test_binary32_adjacent_negative_values(self) -> None:
        fmt = REPORT.FORMAT_INFO["binary32"]
        self.assertEqual(REPORT.ulp_distance(0xBF800000, 0xBF800001, fmt), 1)

    def test_signed_zero_has_zero_distance(self) -> None:
        for format_name, negative_zero in (
            ("binary32", 0x80000000),
            ("binary64", 0x8000000000000000),
        ):
            with self.subTest(format_name=format_name):
                fmt = REPORT.FORMAT_INFO[format_name]
                self.assertEqual(REPORT.ulp_distance(0, negative_zero, fmt), 0)

    def test_nan_payload_is_value_match_not_bit_match(self) -> None:
        fmt = REPORT.FORMAT_INFO["binary64"]
        reference = 0x7FF8000000000000
        candidate = 0xFFF8000000000001
        self.assertTrue(REPORT.value_matches(candidate, reference, fmt))
        self.assertNotEqual(candidate, reference)

    def test_infinity_is_not_finite(self) -> None:
        fmt = REPORT.FORMAT_INFO["binary32"]
        self.assertTrue(REPORT.is_infinite(0x7F800000, fmt))
        self.assertFalse(REPORT.is_finite(0x7F800000, fmt))


class SummaryTests(unittest.TestCase):
    def test_buckets_and_percentiles(self) -> None:
        pairs = [
            (0x3F800000, 0x3F800000),
            (0x3F800001, 0x3F800000),
            (0x3F800003, 0x3F800000),
            (0x3F80000F, 0x3F800000),
            (0x3F800010, 0x3F800000),
            (0x3F800100, 0x3F800000),
        ]
        summary = REPORT.make_summary("candidate", "binary32", "exp", pairs)
        self.assertEqual(summary.ulp_0, 1)
        self.assertEqual(summary.ulp_1, 1)
        self.assertEqual(summary.ulp_2_3, 1)
        self.assertEqual(summary.ulp_4_15, 1)
        self.assertEqual(summary.ulp_16_255, 1)
        self.assertEqual(summary.ulp_256_plus, 1)
        self.assertEqual(summary.nonfinite_mismatch, 0)
        self.assertEqual(summary.ulp_max, 256)
        self.assertEqual(summary.ulp_p50, 3)
        self.assertEqual(summary.ulp_p90, 256)

    def test_nonfinite_mismatch_is_separate_from_nan_class_match(self) -> None:
        pairs = [
            (0x7F800000, 0x7F7FFFFF),
            (0xFFC00001, 0x7FC00000),
        ]
        summary = REPORT.make_summary("candidate", "binary32", "sinh", pairs)
        self.assertEqual(summary.finite_pairs, 0)
        self.assertEqual(summary.value_exact, 1)
        self.assertEqual(summary.nonfinite_mismatch, 1)


class CorpusTests(unittest.TestCase):
    def test_duplicate_case_is_rejected(self) -> None:
        row = "same\tbinary32\texp\t0\t0\t0\n"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.tsv"
            path.write_text(row + row, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate comparison case"):
                REPORT.parse_cases(path, 0)

    def test_incomplete_matrix_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.tsv"
            path.write_text(
                "only\tbinary32\texp\t0\t0\t0\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "has 1 cases, expected 37"):
                REPORT.parse_cases(path, 0)


class ProviderTests(unittest.TestCase):
    def test_rlibm_uses_the_c_bridge_symbols(self) -> None:
        self.assertEqual(
            REPORT.rlibm_symbols(),
            {
                ("binary32", "exp"): "floatlib_rlibm_exp",
                ("binary32", "log"): "floatlib_rlibm_log",
                ("binary32", "sinh"): "floatlib_rlibm_sinh",
                ("binary32", "cosh"): "floatlib_rlibm_cosh",
            },
        )


if __name__ == "__main__":
    unittest.main()
