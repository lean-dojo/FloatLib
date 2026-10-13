#!/usr/bin/env python3

"""Check external preflight and requested agreement without changing retained evidence."""

from __future__ import annotations

import csv
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import verify_release_matrix as matrix
import verify_binary_agreement as agreement


class PreflightTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="floatlib-preflight-")
        self.addCleanup(self.temporary.cleanup)
        self.benchmark = Path(self.temporary.name)
        self.environment = self.benchmark / "environment"
        self.environment.mkdir()

    def capture(self, brand: str) -> None:
        path = self.environment / "external-posit-conformance.csv"
        with path.open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(matrix.PREFLIGHT_HEADER)
            for width in matrix.WIDTHS:
                if width < 5:
                    continue
                for operation in matrix.OPERATIONS:
                    rejected = (width, operation) in matrix.EXPECTED_UNIVERSAL_REJECTIONS
                    diagnostic = f"universal-{width}-{operation}.txt"
                    (self.environment / diagnostic).write_text(
                        f"Stillwater Universal disagrees with {brand} for posit{width}\n"
                        if rejected else ""
                    )
                    writer.writerow(
                        ["Stillwater Universal", width, operation,
                         "reject" if rejected else "pass", diagnostic]
                    )

    def test_historical_and_current_diagnostics_are_accepted(self) -> None:
        for brand in ("LeanFloat", "FloatLib"):
            with self.subTest(brand=brand):
                self.capture(brand)
                statuses = matrix.read_universal_preflight(self.benchmark)
                self.assertEqual(
                    {key for key, status in statuses.items() if status == "reject"},
                    matrix.EXPECTED_UNIVERSAL_REJECTIONS,
                )

    def test_unrelated_diagnostics_are_rejected(self) -> None:
        self.capture("OtherLibrary")
        with self.assertRaisesRegex(ValueError, "lacks the expected disagreement"):
            matrix.read_universal_preflight(self.benchmark)


class RequestedAgreementTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="floatlib-agreement-")
        self.addCleanup(self.temporary.cleanup)
        self.raw = Path(self.temporary.name)
        self.requested = {label: set() for label in agreement.LANE_ADAPTERS.values()
                          if label is not None}

    def trial(self, labels: tuple[str, ...], *, flocq_sink: int = 123) -> Path:
        path = self.raw / "trial-01.csv"
        with path.open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=[
                "implementation", "family", "totalBits", "operation", "agreementIterations",
                "agreementSink", "agreementFixtureTraceDigest",
            ])
            writer.writeheader()
            for label in labels:
                self.requested[label].add(("64", "add"))
                writer.writerow({
                    "implementation": "ExecFloat" if label == "FloatLib" else label,
                    "family": "binary-interchange", "totalBits": "64", "operation": "add",
                    "agreementIterations": 256,
                    "agreementSink": flocq_sink if label == "Flocq" else 123,
                    "agreementFixtureTraceDigest": 456,
                })
        return path

    def verify(self, path: Path) -> int:
        return agreement.verify_trial(path, False, False, False, True,
                                      self.requested["FloatLib"] & self.requested["MPFR"],
                                      256, self.requested)

    def test_flocq_only_and_unpaired_requests_are_accepted(self) -> None:
        for labels in (("Flocq",), ("FloatLib", "Flocq"), ("MPFR", "Flocq")):
            with self.subTest(labels=labels):
                self.requested = {label: set() for label in self.requested}
                self.assertEqual(self.verify(self.trial(labels)), 0)

    def test_paired_flocq_result_must_agree(self) -> None:
        path = self.trial(("FloatLib", "MPFR", "Flocq"))
        self.assertEqual(self.verify(path), 1)
        path = self.trial(("FloatLib", "MPFR", "Flocq"), flocq_sink=999)
        with self.assertRaisesRegex(ValueError, "workload differs"):
            self.verify(path)

    def test_missing_requested_flocq_row_is_rejected(self) -> None:
        path = self.trial(("FloatLib", "MPFR"))
        self.requested["Flocq"].add(("64", "add"))
        with self.assertRaisesRegex(ValueError, "requested Flocq grid differs"):
            self.verify(path)

    def test_requested_flocq_may_have_fewer_paired_cells(self) -> None:
        path = self.trial(("FloatLib", "MPFR", "Flocq"))
        with path.open("a", newline="") as stream:
            csv.writer(stream).writerows([
                ["ExecFloat", "binary-interchange", "64", "sub", 256, 123, 456],
                ["MPFR", "binary-interchange", "64", "sub", 256, 123, 456],
            ])
        self.requested["FloatLib"].add(("64", "sub"))
        self.requested["MPFR"].add(("64", "sub"))
        self.assertEqual(self.verify(path), 2)

    def test_requested_flocq_rejects_unsupported_widths(self) -> None:
        path = self.raw / "requested-matrix.csv"
        path.write_text("lane,totalBits,operation\nflocq-reference,5,add\n")
        with self.assertRaisesRegex(ValueError, "unsupported requested Flocq width"):
            agreement.read_requested_matrix(path)


if __name__ == "__main__":
    unittest.main()
