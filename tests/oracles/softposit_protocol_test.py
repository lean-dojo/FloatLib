#!/usr/bin/env python3
"""Focused corruption tests for the SoftPosit binary stream checker."""

from __future__ import annotations

import struct
import subprocess
import sys
import unittest
from pathlib import Path


if len(sys.argv) < 2:
    raise SystemExit(f"usage: {sys.argv[0]} ORACLE_BINARY [unittest options]")

ORACLE_BINARY = Path(sys.argv.pop(1)).resolve()
SOURCE_REVISION = bytes.fromhex("11" * 20)
SOURCE_REVISION_TEXT = SOURCE_REVISION.hex()


def expected_case_count(source_cases: int, first_case: int, stride: int) -> int:
    if first_case >= source_cases:
        return 0
    return 1 + (source_cases - 1 - first_case) // stride


def header(
    *,
    source_cases: int,
    first_case: int = 0,
    stride: int = 1,
    expected_cases: int | None = None,
    revision: bytes = SOURCE_REVISION,
) -> bytes:
    if expected_cases is None:
        expected_cases = expected_case_count(source_cases, first_case, stride)
    return struct.pack(
        "<4s7B5x5Q20s4x",
        b"SPX2",
        2,  # protocol version
        80,  # header size
        2,  # posit width
        1,  # add
        0,  # pX2
        2,  # arity
        1,  # sampled
        expected_cases,
        first_case,
        stride,
        source_cases,
        0x1234,
        revision,
    )


def add_zero_record(case_id: int) -> bytes:
    return struct.pack("<QIII", case_id, 0, 0, 0)


class SoftPositProtocolTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not ORACLE_BINARY.is_file():
            raise RuntimeError(f"oracle binary does not exist: {ORACLE_BINARY}")

    def check(self, stream: bytes) -> subprocess.CompletedProcess[bytes]:
        return subprocess.run(
            [str(ORACLE_BINARY), "posit", "10"],
            input=stream,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    def test_valid_shard_reports_authenticated_metadata(self) -> None:
        result = self.check(
            header(source_cases=4, first_case=1, stride=2)
            + add_zero_record(1)
            + add_zero_record(3)
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        output = result.stdout.decode()
        self.assertIn("expected_cases=2", output)
        self.assertIn("first_case=1 stride=2", output)
        self.assertIn(f"revision={SOURCE_REVISION_TEXT}", output)
        self.assertIn("cases=2 mismatches=0 protocol_errors=0", output)

    def test_wrong_first_case_id_fails(self) -> None:
        result = self.check(header(source_cases=1) + add_zero_record(1))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "case id 1 does not match the required id 0",
            result.stderr.decode(),
        )

    def test_duplicate_case_id_fails(self) -> None:
        result = self.check(
            header(source_cases=2) + add_zero_record(0) + add_zero_record(0)
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "case id 0 does not match the required id 1",
            result.stderr.decode(),
        )
        self.assertIn("protocol_errors=1", result.stdout.decode())

    def test_reordered_case_ids_fail(self) -> None:
        result = self.check(
            header(source_cases=2) + add_zero_record(1) + add_zero_record(0)
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("protocol_errors=2", result.stdout.decode())

    def test_clean_early_eof_fails_final_count(self) -> None:
        result = self.check(header(source_cases=2) + add_zero_record(0))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "final case count 1 does not match authenticated expectation 2",
            result.stderr.decode(),
        )
        self.assertIn("protocol_errors=1", result.stdout.decode())

    def test_extra_record_fails(self) -> None:
        result = self.check(
            header(source_cases=1) + add_zero_record(0) + add_zero_record(1)
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("lies outside the source case space 1", result.stderr.decode())
        self.assertIn("protocol_errors=2", result.stdout.decode())

    def test_inconsistent_authenticated_count_is_rejected(self) -> None:
        result = self.check(header(source_cases=1, expected_cases=2))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "header expects 2 records, but its source and shard metadata imply 1",
            result.stderr.decode(),
        )

    def test_zero_source_revision_is_rejected(self) -> None:
        result = self.check(header(source_cases=1, revision=bytes(20)))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "SoftPosit source revision is the all-zero object id",
            result.stderr.decode(),
        )


if __name__ == "__main__":
    unittest.main()
