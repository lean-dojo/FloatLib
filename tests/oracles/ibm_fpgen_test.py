#!/usr/bin/env python3
"""Focused tests for the IBM FPgen interoperability adapter."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import ibm_fpgen


class EncodingTests(unittest.TestCase):
    def test_binary32_examples(self) -> None:
        self.assertEqual(
            ibm_fpgen.encode_binary("+1.000000P0", ibm_fpgen.F32), 0x3F800000
        )
        self.assertEqual(ibm_fpgen.encode_binary("+0.000001P-126", ibm_fpgen.F32), 1)
        self.assertEqual(
            ibm_fpgen.encode_binary("+0.7FFFFFP-126", ibm_fpgen.F32),
            0x007FFFFF,
        )
        self.assertEqual(
            ibm_fpgen.encode_binary("-1.7FFFFFP127", ibm_fpgen.F32),
            0xFF7FFFFF,
        )

    def test_special_values_use_canonical_representatives_and_preserve_zero_sign(
        self,
    ) -> None:
        self.assertEqual(ibm_fpgen.encode_binary("+Inf", ibm_fpgen.F32), 0x7F800000)
        self.assertEqual(ibm_fpgen.encode_binary("-Inf", ibm_fpgen.F32), 0xFF800000)
        self.assertEqual(ibm_fpgen.encode_binary("+Zero", ibm_fpgen.F32), 0)
        self.assertEqual(ibm_fpgen.encode_binary("-Zero", ibm_fpgen.F32), 0x80000000)
        self.assertEqual(ibm_fpgen.encode_binary("Q", ibm_fpgen.F32), 0x7FC00000)
        self.assertEqual(ibm_fpgen.encode_binary("S", ibm_fpgen.F32), 0x7F800001)

    def test_widened_cast_results(self) -> None:
        self.assertEqual(
            ibm_fpgen.encode_binary("+1.FFFFFE0000000P127", ibm_fpgen.F64),
            0x47EFFFFFE0000000,
        )
        self.assertEqual(
            ibm_fpgen.encode_binary(
                "+1.FFFFFE0000000000000000000000P127",
                ibm_fpgen.F128,
            ),
            (0x407E << 112) | (0x7FFFFF << 89),
        )

    def test_invalid_semantic_encodings_are_rejected(self) -> None:
        invalid = (
            "+1.FFFFFFP0",  # top padding bit exceeds binary32's 23-bit fraction
            "+1.00000P0",  # wrong field width
            "+0.000001P-125",  # subnormal exponent must be -126
            "+0.000000P-126",  # zero must use the named representation
            "+1.000000P128",  # exponent outside binary32
            "0x1p0",  # not the suite's semantic syntax
        )
        for text in invalid:
            with self.subTest(text=text), self.assertRaises(ibm_fpgen.AdapterError):
                ibm_fpgen.encode_binary(text, ibm_fpgen.F32)


class ParsingTests(unittest.TestCase):
    def source(self, text: str) -> ibm_fpgen.Source:
        return ibm_fpgen.Source(Path("sample.fptest"), "sample.fptest", 7, text)

    def parse(self, text: str) -> ibm_fpgen.ParsedCase:
        source = self.source(text)
        fields = text.split()
        return ibm_fpgen.parse_supported_case(
            fields, ibm_fpgen.OPERATIONS[fields[0]], source
        )

    def test_optional_trap_field_is_disambiguated_by_arity(self) -> None:
        plain = self.parse("b32+ =0 +1.000000P0 +1.000000P0 -> +1.000000P1")
        trapped = self.parse("b32+ =0 i +1.000000P0 +1.000000P0 -> +1.000000P1")
        self.assertEqual(plain.traps, frozenset())
        self.assertEqual(trapped.traps, frozenset("i"))
        self.assertFalse(ibm_fpgen.trap_was_delivered(trapped))

    def test_delivered_underflow_trap_normalizes_all_suite_spellings(self) -> None:
        for underflow in "uvw":
            parsed = self.parse(
                f"b32* =0 u +0.000001P-126 +0.000001P-126 -> +Zero x{underflow}"
            )
            self.assertTrue(ibm_fpgen.trap_was_delivered(parsed))

    def test_invalid_grammar_reports_source_location(self) -> None:
        text = "b32+ =0 +1.000000P0 -> +1.000000P0"
        with self.assertRaisesRegex(
            ibm_fpgen.AdapterError,
            r"sample\.fptest:7: expected 2 operand",
        ):
            self.parse(text)

    def test_underflow_is_recomputed_after_rounding(self) -> None:
        tiny = ibm_fpgen.encode_binary("+0.7FFFFFP-126", ibm_fpgen.F32)
        normal = ibm_fpgen.encode_binary("+1.000000P-126", ibm_fpgen.F32)
        self.assertEqual(ibm_fpgen.status_bits(frozenset("xv"), tiny, ibm_fpgen.F32), 3)
        self.assertEqual(
            ibm_fpgen.status_bits(frozenset("xu"), normal, ibm_fpgen.F32), 1
        )
        self.assertEqual(ibm_fpgen.status_bits(frozenset("v"), normal, ibm_fpgen.F32), 2)


class SuiteTests(unittest.TestCase):
    def write_suite(self, root: Path) -> None:
        (root / "sample.fptest").write_text(
            "Copyright ignored header\n"
            "d64+ =0 +1E0 +1E0 -> +2E0\n"
            "b32cp =0 +1.000000P0 -> +1.000000P0\n"
            "b32V =0 i -Inf -> # i\n"
            "b32* > xu -1.48FDB5P-78 +1.4381CEP-73 -> -1.197F2AP42 xu\n"
            "b32+ =0 i -1.6E9177P49 -1.7FFFFFP127 -> -1.7FFFFFP127 x\n"
            "b32b64cff =0 +1.000000P0 -> +1.0000000000000P0\n",
            encoding="utf-8",
        )

    def test_classification_output_and_source_maps(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            suite = root / "suite"
            output = root / "output"
            suite.mkdir()
            self.write_suite(suite)

            counters, cases = ibm_fpgen.classify_suite(suite)
            self.assertEqual(
                {
                    name: counters[name]
                    for name in (
                        "case_records",
                        "decimal",
                        "unsupported",
                        "no_result",
                        "trap_produced",
                        "emitted",
                    )
                },
                {
                    "case_records": 6,
                    "decimal": 1,
                    "unsupported": 0,
                    "no_result": 1,
                    "trap_produced": 1,
                    "emitted": 3,
                },
            )

            summary = ibm_fpgen.write_outputs(output, counters, cases)
            self.assertEqual(summary["counters"]["emitted"], 3)
            self.assertEqual(
                (output / "f32_copy_near_even.stream").read_text(encoding="utf-8"),
                "3f800000 3f800000 0\n",
            )
            self.assertEqual(
                (output / "f32_add_near_even.stream").read_text(encoding="utf-8"),
                "d86e9177 ff7fffff ff7fffff 1\n",
            )
            cast_stream = output / "f32_to_f64_near_even.stream"
            self.assertEqual(
                cast_stream.read_text(encoding="utf-8"),
                "3f800000 3ff0000000000000 0\n",
            )
            source_map = (output / "f32_add_near_even.map.tsv").read_text(
                encoding="utf-8"
            )
            self.assertIn("case\tfile\tline\tsource\n", source_map)
            self.assertIn("sample.fptest\t6\tb32+ =0", source_map)
            loaded = json.loads((output / "summary.json").read_text(encoding="utf-8"))
            self.assertEqual(loaded, summary)

    def test_selection_and_classification_operations_are_emitted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            suite = root / "suite"
            suite.mkdir()
            (suite / "extended.fptest").write_text(
                "b32<C =0 +1.000000P0 +1.000000P1 -> +1.000000P0\n"
                "b32>A =0 -1.000000P0 +1.000000P0 -> +1.000000P0\n"
                "b32?f =0 +Inf -> 0x0\n",
                encoding="utf-8",
            )

            counters, cases = ibm_fpgen.classify_suite(suite)
            self.assertEqual(counters["emitted"], 3)
            self.assertEqual(counters["unsupported"], 0)
            fields_by_operation = {case.group.operation: case.fields for case in cases}
            self.assertEqual(
                fields_by_operation["minNum"],
                ("3f800000", "40000000", "3f800000", "0"),
            )
            self.assertEqual(
                fields_by_operation["maxNumMag"],
                ("bf800000", "3f800000", "3f800000", "0"),
            )
            self.assertEqual(
                fields_by_operation["isFinite"],
                ("7f800000", "0", "0"),
            )

    def test_nonoverlapping_nan_and_underflow_semantics_are_counted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            suite = Path(temporary) / "suite"
            suite.mkdir()
            (suite / "overlap.fptest").write_text(
                "b32?- =0 Q -> 0x1\n"
                "b32+ =0 Q S -> Q\n"
                "b32* =0 +1.000000P-126 +0.7FFFFFP-126 -> +0.7FFFFFP-126 xu\n"
                "b32+ =0 +1.000000P0 +1.000000P0 -> +1.000000P1\n",
                encoding="utf-8",
            )

            counters, cases = ibm_fpgen.classify_suite(suite)
            self.assertEqual(counters["unsupported"], 3)
            self.assertEqual(counters["unsupported_nan_sign"], 1)
            self.assertEqual(counters["unsupported_nan_precedence"], 1)
            self.assertEqual(counters["unsupported_underflow_convention"], 1)
            self.assertEqual(counters["emitted"], 1)
            self.assertEqual(len(cases), 1)

    def test_malformed_rounding_mode_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            suite = Path(temporary) / "suite"
            suite.mkdir()
            (suite / "malformed.fptest").write_text(
                "b32+ banana +1.000000P0 +1.000000P0 -> +1.000000P1\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ibm_fpgen.AdapterError, "invalid rounding mode"):
                ibm_fpgen.classify_suite(suite)

    def test_empty_semantic_overlap_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            suite = Path(temporary) / "suite"
            suite.mkdir()
            (suite / "decimal.fptest").write_text(
                "d64+ =0 +1E0 +1E0 -> +2E0\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ibm_fpgen.AdapterError, "no cases"):
                ibm_fpgen.classify_suite(suite)

    def test_nonempty_output_directory_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            suite = root / "suite"
            output = root / "output"
            suite.mkdir()
            output.mkdir()
            (output / "old").write_text("stale", encoding="utf-8")
            self.write_suite(suite)
            counters, cases = ibm_fpgen.classify_suite(suite)
            with self.assertRaises(ibm_fpgen.AdapterError):
                ibm_fpgen.write_outputs(output, counters, cases)


if __name__ == "__main__":
    unittest.main()
