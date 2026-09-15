#!/usr/bin/env python3
"""Focused unit tests for the QF_FP differential adapter."""

from __future__ import annotations

import shutil
import sys
import unittest
from pathlib import Path
from random import Random

sys.path.insert(0, str(Path(__file__).resolve().parent))

import smt_fp


class CorpusTests(unittest.TestCase):
    def test_edge_values_cover_ieee_classes(self) -> None:
        for fmt in smt_fp.FORMATS:
            with self.subTest(format=fmt.name):
                values = smt_fp.edge_values(fmt)
                self.assertIn(0, values)
                self.assertIn(fmt.sign_mask, values)
                self.assertIn(1, values)
                self.assertIn(
                    fmt.exponent_mask << fmt.fraction_bits,
                    values,
                )
                self.assertTrue(any(fmt.is_nan(value) for value in values))

    def test_generation_is_deterministic_and_complete(self) -> None:
        first = smt_fp.generate_cases(1234, 2)
        second = smt_fp.generate_cases(1234, 2)
        self.assertEqual(first, second)
        self.assertEqual(len(first), len({case.identifier for case in first}))
        self.assertEqual(
            {case.operation for case in first},
            {"add", "sub", "mul", "div", "sqrt", "fma", "cast"},
        )
        self.assertEqual(
            {case.source.name for case in first},
            {"f16", "f32", "f64"},
        )
        self.assertEqual(
            {case.rounding.protocol for case in first},
            {"rne", "rtz", "rtp", "rtn"},
        )

    def test_random_values_are_distinct_finite_and_outside_edges(self) -> None:
        for fmt in smt_fp.FORMATS:
            with self.subTest(format=fmt.name):
                edges = smt_fp.edge_values(fmt)
                first = smt_fp.random_finite_values(
                    fmt,
                    Random(1234),
                    16,
                    excluded=edges,
                )
                second = smt_fp.random_finite_values(
                    fmt,
                    Random(1234),
                    16,
                    excluded=edges,
                )
                self.assertEqual(first, second)
                self.assertEqual(len(first), 16)
                self.assertEqual(len(set(first)), 16)
                self.assertTrue(all(fmt.is_finite(value) for value in first))
                self.assertTrue(set(first).isdisjoint(edges))

    def test_protocol_uses_source_width_for_operands(self) -> None:
        case = smt_fp.Case(
            "000001",
            "cast",
            smt_fp.F16,
            smt_fp.F64,
            smt_fp.ROUNDINGS[0],
            (1,),
        )
        self.assertEqual(
            case.protocol_line(),
            "000001\tcast\tf16\tf64\trne\t0001",
        )


class SMTTests(unittest.TestCase):
    def test_script_is_qf_fp_and_contains_each_expression_shape(self) -> None:
        cases = [
            smt_fp.Case(
                "000000",
                "add",
                smt_fp.F16,
                smt_fp.F16,
                smt_fp.ROUNDINGS[0],
                (0x3C00, 0x4000),
            ),
            smt_fp.Case(
                "000001",
                "sqrt",
                smt_fp.F32,
                smt_fp.F32,
                smt_fp.ROUNDINGS[1],
                (0x3F800000,),
            ),
            smt_fp.Case(
                "000002",
                "fma",
                smt_fp.F64,
                smt_fp.F64,
                smt_fp.ROUNDINGS[2],
                (0x3FF0000000000000,) * 3,
            ),
            smt_fp.Case(
                "000003",
                "cast",
                smt_fp.F64,
                smt_fp.F16,
                smt_fp.ROUNDINGS[3],
                (0x3FF0000000000000,),
            ),
        ]
        script = smt_fp.build_smtlib(cases, batch_size=2)
        self.assertIn("(set-logic QF_FP)", script)
        self.assertIn("(fp.add RNE", script)
        self.assertIn("(fp.sqrt RTZ", script)
        self.assertIn("(fp.fma RTP", script)
        self.assertIn("((_ to_fp 5 11) RTN", script)
        self.assertNotIn("fp.to_ieee_bv", script)

    def test_decode_all_solver_value_forms(self) -> None:
        finite = ["fp", "#b0", "#b01111", "#b0000000000"]
        self.assertEqual(
            smt_fp.decode_solver_value(finite, smt_fp.F16),
            smt_fp.SolverValue(0x3C00, "finite"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(
                ["fp", "#b0", "#x7f", "#b00000000000000000000000"],
                smt_fp.F32,
            ),
            smt_fp.SolverValue(0x3F800000, "finite"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(["_", "-zero", "5", "11"], smt_fp.F16),
            smt_fp.SolverValue(0x8000, "zero"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(["_", "+oo", "5", "11"], smt_fp.F16),
            smt_fp.SolverValue(0x7C00, "infinity"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(["_", "NaN", "5", "11"], smt_fp.F16),
            smt_fp.SolverValue(None, "nan"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(
                ["fp", "#b1", "#b11111", "#b0000000000"],
                smt_fp.F16,
            ),
            smt_fp.SolverValue(0xFC00, "infinity"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(
                ["fp", "#b0", "#b11111", "#b1000000000"],
                smt_fp.F16,
            ),
            smt_fp.SolverValue(None, "nan"),
        )
        self.assertEqual(
            smt_fp.decode_solver_value(
                ["fp", "#b1", "#b00000", "#b0000000000"],
                smt_fp.F16,
            ),
            smt_fp.SolverValue(0x8000, "zero"),
        )

    @unittest.skipUnless(shutil.which("z3"), "Z3 is not installed")
    def test_z3_evaluates_ground_qf_fp_cases(self) -> None:
        cases = [
            smt_fp.Case(
                "000000",
                "add",
                smt_fp.F16,
                smt_fp.F16,
                smt_fp.ROUNDINGS[0],
                (0x3C00, 0x4000),
            ),
            smt_fp.Case(
                "000001",
                "cast",
                smt_fp.F32,
                smt_fp.F16,
                smt_fp.ROUNDINGS[0],
                (0x3F800000,),
            ),
        ]
        _, stdout, _ = smt_fp.run_z3(
            "z3",
            smt_fp.build_smtlib(cases),
            10,
        )
        values = smt_fp.parse_solver_output(stdout, cases)
        self.assertEqual(values["000000"].bits, 0x4200)
        self.assertEqual(values["000001"].bits, 0x3C00)


class ComparisonTests(unittest.TestCase):
    def test_exact_bits_and_nan_class_are_counted_separately(self) -> None:
        exact = smt_fp.Case(
            "000000",
            "add",
            smt_fp.F16,
            smt_fp.F16,
            smt_fp.ROUNDINGS[0],
            (0x3C00, 0x3C00),
        )
        nan = smt_fp.Case(
            "000001",
            "div",
            smt_fp.F16,
            smt_fp.F16,
            smt_fp.ROUNDINGS[0],
            (0, 0),
        )
        counts, mismatches = smt_fp.compare_results(
            [exact, nan],
            {
                "000000": smt_fp.SolverValue(0x4000, "finite"),
                "000001": smt_fp.SolverValue(None, "nan"),
            },
            {
                "000000": 0x4000,
                "000001": 0x7E00,
            },
        )
        self.assertEqual(counts["exact_bit_cases"], 1)
        self.assertEqual(counts["nan_class_cases"], 1)
        self.assertEqual(counts["bit_mismatches"], 0)
        self.assertEqual(counts["nan_class_mismatches"], 0)
        self.assertEqual(counts["missing_floatlib"], 0)
        self.assertEqual(counts["mismatches"], 0)
        self.assertEqual(mismatches, [])

    def test_protocol_error_row_is_not_also_counted_as_missing(self) -> None:
        case = smt_fp.Case(
            "000000",
            "add",
            smt_fp.F16,
            smt_fp.F16,
            smt_fp.ROUNDINGS[0],
            (0x3C00, 0x3C00),
        )
        values, errors = smt_fp.parse_lean_output(
            "000000\terror\n",
            [case],
        )
        self.assertEqual(values, {})
        self.assertEqual(errors, 1)

    def test_lean_result_requires_the_exact_destination_width(self) -> None:
        case = smt_fp.Case(
            "000000",
            "add",
            smt_fp.F16,
            smt_fp.F16,
            smt_fp.ROUNDINGS[0],
            (0x3C00, 0x3C00),
        )
        for malformed in ("400", "04000", "10000", "-001", "zzzz"):
            with self.subTest(malformed=malformed):
                values, errors = smt_fp.parse_lean_output(
                    f"000000\tok\t{malformed}\n",
                    [case],
                )
                self.assertEqual(values, {})
                self.assertEqual(errors, 1)


if __name__ == "__main__":
    unittest.main()
