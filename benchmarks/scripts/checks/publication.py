#!/usr/bin/env python3

"""Check provenance compatibility and requested agreement without changing retained evidence."""

from __future__ import annotations

import csv
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import verify_release_matrix as matrix
import verify_binary_agreement as agreement


class SourceCaptureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="floatlib-publication-")
        self.addCleanup(self.temporary.cleanup)
        self.benchmark = Path(self.temporary.name) / "benchmark"
        self.provenance = self.benchmark / "provenance"
        self.provenance.mkdir(parents=True)

    def capture(
        self, roots: tuple[str, ...], *, omit_config: bool = False
    ) -> dict[str, str]:
        paths = ["lakefile.lean", "lean-toolchain", "lake-manifest.json"]
        if omit_config:
            paths.remove("lean-toolchain")
        paths += [f"{root}/Numerics/Example.lean" for root in roots]
        ledger = "".join(f"{'a' * 64}  {path}\n" for path in sorted(paths))
        (self.provenance / "source-files.sha256").write_text(ledger)
        (self.provenance / "worktree-status.txt").write_text("")
        (self.provenance / "worktree.patch").write_text("")
        snapshot = "head_revision=" + "b" * 40 + "\n"
        for name, key in (
            ("source-files.sha256", "source_file_hashes_sha256"),
            ("worktree-status.txt", "worktree_status_sha256"),
            ("worktree.patch", "worktree_patch_sha256"),
        ):
            snapshot += f"{key}={matrix.sha256(self.provenance / name)}\n"
        (self.provenance / "source-snapshot.txt").write_text(snapshot)
        return {
            "gitCommit": "b" * 40,
            "gitDirtyFiles": "0",
            "leanSourceAndBuildConfigHash": hashlib.sha256(ledger.encode()).hexdigest(),
        }

    def test_historical_and_current_roots_preserve_recorded_bytes(self) -> None:
        for root in ("LeanFloat", "FloatLib"):
            with self.subTest(root=root):
                metadata = self.capture((root,))
                before = {
                    path.name: path.read_bytes() for path in self.provenance.iterdir()
                }
                matrix.verify_source_metadata(self.benchmark, metadata)
                self.assertEqual(
                    before,
                    {path.name: path.read_bytes() for path in self.provenance.iterdir()},
                )

    def test_renaming_ledger_paths_does_not_preserve_the_digest(self) -> None:
        historical = self.capture(("LeanFloat",))
        current = self.capture(("FloatLib",))
        self.assertNotEqual(
            historical["leanSourceAndBuildConfigHash"],
            current["leanSourceAndBuildConfigHash"],
        )
        with self.assertRaisesRegex(ValueError, "source hash differs"):
            matrix.verify_source_metadata(self.benchmark, historical)

    def test_mixed_library_roots_are_ambiguous(self) -> None:
        metadata = self.capture(("LeanFloat", "FloatLib"))
        with self.assertRaisesRegex(ValueError, "exactly one library source root"):
            matrix.verify_source_metadata(self.benchmark, metadata)

    def test_unknown_library_root_is_rejected(self) -> None:
        metadata = self.capture(("OtherLibrary",))
        with self.assertRaisesRegex(ValueError, "exactly one library source root"):
            matrix.verify_source_metadata(self.benchmark, metadata)

    def test_missing_build_config_is_rejected(self) -> None:
        metadata = self.capture(("FloatLib",), omit_config=True)
        with self.assertRaisesRegex(ValueError, "missing build files"):
            matrix.verify_source_metadata(self.benchmark, metadata)

    def test_corrupted_source_ledger_is_rejected(self) -> None:
        metadata = self.capture(("LeanFloat",))
        with (self.provenance / "source-files.sha256").open("a") as stream:
            stream.write(f"{'c' * 64}  FloatLib/Tampered.lean\n")
        with self.assertRaisesRegex(ValueError, "differs from source snapshot"):
            matrix.verify_source_metadata(self.benchmark, metadata)


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
