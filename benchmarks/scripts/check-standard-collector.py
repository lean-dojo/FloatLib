#!/usr/bin/env python3
"""Reject truncated, contradictory and misidentified timing evidence."""
import importlib.util
from pathlib import Path
import unittest


path = Path(__file__).with_name("collect-standard-matrix.py")
spec = importlib.util.spec_from_file_location("standard_collector", path)
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)


def native():
    return "".join(
        f"MATRIX_NATIVE Posit addition width=8 trial={trial} count=8 "
        "elapsed=800 ns=100 sink=160 value=20\n" for trial in range(3))


def kernel():
    return (
        "MATRIX_KERNEL Posit addition width=8 case=2\n"
        "with the tagged kernel rules: 12.345 µs\n"
        "value: 20\n")


class EvidenceChecks(unittest.TestCase):
    def test_native_complete(self):
        result = collector.parse_native(native(), "Posit", "addition", 8)
        self.assertEqual((result["ns"], result["value"]), (100, 20))
        self.assertEqual(len(result["trials"]), 3)

    def test_native_incomplete(self):
        for text in [native().rstrip("\n"), native().splitlines(True)[0],
                     native().replace("trial=2", "trial=1")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                collector.parse_native(text, "Posit", "addition", 8)

    def test_native_arithmetic_and_identity(self):
        for text in [native().replace("elapsed=800", "elapsed=808", 1),
                     native().replace("sink=160", "sink=161", 1),
                     native().replace("value=20", "value=21", 1),
                     native().replace("width=8", "width=16", 1)]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                collector.parse_native(text, "Posit", "addition", 8)

    def test_kernel_complete(self):
        result = collector.parse_kernel(kernel(), "Posit", "addition", 8, 2)
        self.assertEqual(result, {"ns": 12345, "value": 20})

    def test_kernel_truncation_and_duplicates(self):
        for text in [kernel().rstrip("\n"), kernel().split("value:")[0],
                     kernel() + "value: 20\n", kernel() + kernel(),
                     kernel() + "error: reduction failed\n",
                     kernel().replace("case=2", "case=3")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                collector.parse_kernel(text, "Posit", "addition", 8, 2)

    def test_complete_sequential_batch(self):
        second = kernel().replace("addition", "multiply").replace("case=2", "case=3")
        text = kernel() + second
        catalog = {"family": "Posit", "cases": [
            {"label": "unused0"}, {"label": "unused1"},
            {"label": "addition"}, {"label": "multiply"}]}
        results = collector.validate_kernel_batch(text, catalog, 8, [2, 3])
        self.assertEqual(results[2], {"ns": 12345, "value": 20})
        self.assertEqual(results[3], results[2])
        with self.assertRaises(ValueError):
            collector.parse_kernel(text, "Posit", "addition", 8, 2)

    def test_batch_requires_every_declared_result(self):
        second = kernel().replace("addition", "multiply").replace("case=2", "case=3")
        catalog = {"family": "Posit", "cases": [
            {"label": "unused0"}, {"label": "unused1"},
            {"label": "addition"}, {"label": "multiply"}]}
        for text, indices in [
                (kernel() + second.rstrip("\n"), [2, 3]),
                (kernel() + second + "error: later case failed\n", [2, 3]),
                (kernel(), [2, 3]), (kernel() + second, [3, 2]),
                (kernel() + second, [2]), (kernel() + second, [2, 2, 3]),
                (kernel() + second + second, [2, 3])]:
            with self.subTest(indices=indices), self.assertRaises(ValueError):
                collector.validate_kernel_batch(text, catalog, 8, indices)


if __name__ == "__main__":
    unittest.main()
