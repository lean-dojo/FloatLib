#!/usr/bin/env python3
"""Unit tests for the transcendental MPFR oracle, the known-failure gate, and the corpus.

The oracle tests need `transcendental_mpfr.c` compiled; set FLOATLIB_TRANSCENDENTAL_ORACLE to an
existing build, or let the tests compile it with `cc` and `pkg-config mpfr`. Expected roundings
are computed independently with exact rational arithmetic.
"""

from __future__ import annotations

import atexit
import contextlib
import importlib.util
import io
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FIXTURES = ROOT / "tests" / "FloatLibTests" / "Fixtures" / "Transcendentals.lean"
CORPUS_FILE = HERE / "data" / "transcendental-hard-cases.tsv"
KNOWN_FAILURES_FILE = HERE / "data" / "transcendental-known-failures.tsv"
CENSUS_FILE = HERE / "data" / "transcendental-census.json"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


REPORT = load("transcendental_report", HERE / "transcendental_report.py")
CORPUS = load("transcendental_hard_cases", HERE / "transcendental_hard_cases.py")
Format = REPORT.Format
BINARY16 = REPORT.CATALOG["binary16"]
BFLOAT16 = REPORT.CATALOG["bfloat16"]
BINARY32 = REPORT.CATALOG["binary32"]
BINARY64 = REPORT.CATALOG["binary64"]
BINARY128 = REPORT.CATALOG["binary128"]
WIDE = REPORT.ieee(31, 23)
MODES = REPORT.MODES


def build_oracle() -> Path | None:
    configured = os.environ.get("FLOATLIB_TRANSCENDENTAL_ORACLE")
    if configured:
        return Path(configured)
    compiler = os.environ.get("CC", "cc")
    if shutil.which(compiler) is None or shutil.which("pkg-config") is None:
        return None
    flags = subprocess.run(["pkg-config", "--cflags", "--libs", "mpfr"], capture_output=True,
                           text=True)
    if flags.returncode != 0:
        return None
    directory = Path(tempfile.mkdtemp(prefix="floatlib-transcendental-oracle-"))
    atexit.register(shutil.rmtree, directory, True)
    binary = directory / "transcendental_mpfr"
    subprocess.run([compiler, "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror",
                    str(HERE / "transcendental_mpfr.c"), *flags.stdout.split(), "-o", str(binary)],
                   check=True)
    return binary


ORACLE = build_oracle()
needs_oracle = unittest.skipIf(ORACLE is None, "MPFR development files are not available")


def request(operation: str, mode: str, fmt: Format, arguments: list[int],
            floatlib: int | None = None, ternary: int | None = None) -> str:
    parts = ["case", REPORT.case_id(operation, mode, fmt, arguments), "op", operation, "mode", mode,
             "format", str(fmt.exponent_bits), str(fmt.fraction_bits), str(fmt.bias), fmt.encoding,
             "args", str(len(arguments)), *(fmt.hex(bits) for bits in arguments)]
    if floatlib is not None:
        parts += ["floatlib", fmt.hex(floatlib)]
        if ternary is not None:
            parts += ["ternary", str(ternary)]
    return " ".join(parts)


def run_oracle(lines: list[str]) -> list[str]:
    assert ORACLE is not None
    completed = subprocess.run([str(ORACLE)], input="\n".join(lines) + "\n", capture_output=True,
                               text=True, check=True)
    return [line for line in completed.stdout.splitlines() if not line.startswith("#")]


def evaluate_all(requests: list[tuple[str, str, Format, list[int]]]) -> list[tuple[int, int]]:
    lines = [request(*item) for item in requests]
    results = []
    for line in run_oracle(lines):
        case = REPORT.parse_case_line(line, "oracle output")
        results.append((case.mpfr, case.mpfr_ternary))
    return results


def oracle_fails(line: str) -> bool:
    assert ORACLE is not None
    completed = subprocess.run([str(ORACLE)], input=line + "\n", capture_output=True, text=True)
    return completed.returncode != 0


def encode(fmt: Format, negative: bool, magnitude: Fraction) -> int:
    """Encoding of an exactly representable finite magnitude."""
    sign = fmt.sign_mask if negative else 0
    if magnitude == 0:
        return sign
    exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if Fraction(2) ** exponent > magnitude:
        exponent -= 1
    while Fraction(2) ** (exponent + 1) <= magnitude:
        exponent += 1
    minimum = 1 - fmt.bias
    if exponent < minimum:
        scaled = magnitude / Fraction(2) ** (minimum - fmt.fraction_bits)
        assert scaled.denominator == 1
        return sign | scaled.numerator
    scaled = magnitude / Fraction(2) ** (exponent - fmt.fraction_bits)
    assert scaled.denominator == 1
    field = exponent + fmt.bias
    assert 0 < field < (1 << fmt.exponent_bits) - 1
    return sign | (field << fmt.fraction_bits) | (scaled.numerator - (1 << fmt.fraction_bits))


def binary_exponent(magnitude: Fraction) -> int:
    """floor(log2(magnitude)) of a positive rational."""
    exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if Fraction(2) ** exponent > magnitude:
        exponent -= 1
    return exponent


def round_exact(value: Fraction, fmt: Format, mode: str) -> tuple[int, int]:
    """IEEE rounding of a rational into `fmt` in `mode`: encoding and ternary sign."""
    if value == 0:
        return 0, 0
    negative = value < 0
    magnitude = -value if negative else value
    emax = (1 << fmt.exponent_bits) - 2 - fmt.bias
    quantum_exponent = max(binary_exponent(magnitude), 1 - fmt.bias) - fmt.fraction_bits
    scaled = magnitude / Fraction(2) ** quantum_exponent
    floor = scaled.numerator // scaled.denominator
    remainder = scaled - floor
    if remainder == 0:
        away = False
    elif mode == "RNDN":
        away = remainder > Fraction(1, 2) or (remainder == Fraction(1, 2) and floor % 2 == 1)
    elif mode == "RNDZ":
        away = False
    elif mode == "RNDA":
        away = True
    elif mode == "RNDU":
        away = not negative
    else:
        away = negative
    significand = floor + 1 if away else floor
    if significand.bit_length() - 1 + quantum_exponent > emax:
        to_infinity = (mode in ("RNDN", "RNDA") or (mode == "RNDU" and not negative)
                       or (mode == "RNDD" and negative))
        if to_infinity:
            bits = (fmt.sign_mask if negative else 0) | fmt.exponent_mask
            return bits, -1 if negative else 1
        significand, quantum_exponent = (1 << (fmt.fraction_bits + 1)) - 1, emax - fmt.fraction_bits
    rounded = significand * Fraction(2) ** quantum_exponent
    result = -rounded if negative else rounded
    ternary = (result > value) - (result < value)
    return encode(fmt, negative, rounded), ternary


def pi_fraction(bits: int) -> Fraction:
    return Fraction(CORPUS.pi_scaled(bits), 1 << bits)


class EncodingTests(unittest.TestCase):
    def test_adjacent_values_have_distance_one(self) -> None:
        self.assertEqual(REPORT.ulp_distance(0x3F800000, 0x3F800001, BINARY32), 1)
        self.assertEqual(REPORT.ulp_distance(0xBF800000, 0xBF800001, BINARY32), 1)

    def test_signed_zero_has_zero_distance_but_does_not_match(self) -> None:
        for fmt in (BINARY32, BINARY64, BINARY128):
            with self.subTest(fmt=fmt.name):
                self.assertEqual(REPORT.ulp_distance(0, fmt.sign_mask, fmt), 0)
                self.assertFalse(REPORT.value_matches(fmt.sign_mask, 0, fmt))

    def test_nan_payload_is_value_match_not_bit_match(self) -> None:
        reference = 0x7FF8000000000000
        candidate = 0xFFF8000000000001
        self.assertTrue(REPORT.value_matches(candidate, reference, BINARY64))
        self.assertNotEqual(candidate, reference)

    def test_infinity_is_not_finite(self) -> None:
        self.assertTrue(REPORT.is_infinite(0x7F800000, BINARY32))
        self.assertFalse(REPORT.is_finite(0x7F800000, BINARY32))

    def test_names_and_case_ids(self) -> None:
        self.assertEqual(BINARY128.name, "binary128")
        self.assertEqual(WIDE.name, "ieee31_23")
        self.assertEqual(Format(8, 23, 239).name, "ieee8_23_bias239")
        self.assertEqual(REPORT.case_id("pow", "RNDN", BINARY16, [0x3C00, 0x4000]),
                         "binary16/pow/RNDN/0x3c00/0x4000")
        self.assertEqual(REPORT.case_id("pi", "RNDA", WIDE, []), "ieee31_23/pi/RNDA")
        self.assertEqual(WIDE.hex(1), "0x" + "0" * 13 + "1")

    def test_buckets_and_percentiles(self) -> None:
        pairs = [(0x3F800000 + offset, 0x3F800000) for offset in (0, 1, 3, 15, 16, 256)]
        summary = REPORT.make_summary("candidate", BINARY32, "exp", "RNDN", pairs)
        self.assertEqual((summary.ulp_0, summary.ulp_1, summary.ulp_2_3, summary.ulp_4_15,
                          summary.ulp_16_255, summary.ulp_256_plus), (1, 1, 1, 1, 1, 1))
        self.assertEqual(summary.ulp_max, 256)
        self.assertEqual(summary.ulp_p50, 3)

    def test_signed_zero_mismatches_are_counted(self) -> None:
        summary = REPORT.make_summary("candidate", BINARY32, "sin", "RNDN",
                                      [(0x80000000, 0x00000000), (0, 0)])
        self.assertEqual(summary.zero_sign_mismatch, 1)
        self.assertEqual(summary.bit_exact, 1)


@needs_oracle
class TransportTests(unittest.TestCase):
    """pow(x, 1) = x exactly, so it carries every encoding through MPFR and back."""

    def edge_encodings(self, fmt: Format) -> list[int]:
        fraction = (1 << fmt.fraction_bits) - 1
        top = (1 << fmt.exponent_bits) - 2
        positive = [0, 1, 2, fraction, 1 << fmt.fraction_bits,
                    (top << fmt.fraction_bits) | fraction, fmt.bias << fmt.fraction_bits,
                    (fmt.bias << fmt.fraction_bits) | 1]
        rng = random.Random(fmt.width)
        for _ in range(64):
            field = rng.randrange(0, top + 1)
            positive.append((field << fmt.fraction_bits) | rng.getrandbits(fmt.fraction_bits))
        return positive + [bits | fmt.sign_mask for bits in positive]

    def check_round_trips(self, fmt: Format) -> None:
        one = fmt.bias << fmt.fraction_bits
        inputs = self.edge_encodings(fmt)
        results = evaluate_all([("pow", "RNDN", fmt, [bits, one]) for bits in inputs])
        for bits, (result, ternary) in zip(inputs, results, strict=True):
            self.assertEqual((fmt.hex(result), ternary), (fmt.hex(bits), 0))

    def test_binary128_round_trips(self) -> None:
        self.check_round_trips(BINARY128)

    def test_ieee_31_23_round_trips(self) -> None:
        self.check_round_trips(WIDE)

    def test_small_and_custom_formats_round_trip(self) -> None:
        for fmt in (BINARY16, BFLOAT16, BINARY32, BINARY64, Format(8, 23, 239), Format(2, 1, 1)):
            with self.subTest(fmt=fmt.name):
                self.check_round_trips(fmt)

    def test_infinities_and_nans(self) -> None:
        for fmt in (BINARY16, BINARY128, WIDE):
            with self.subTest(fmt=fmt.name):
                one = fmt.bias << fmt.fraction_bits
                infinity = fmt.exponent_mask
                quiet = infinity | (1 << (fmt.fraction_bits - 1))
                signaling = infinity | 1
                inputs = [infinity, infinity | fmt.sign_mask, quiet, signaling,
                          quiet | fmt.sign_mask | 5]
                results = evaluate_all([("pow", "RNDN", fmt, [bits, one]) for bits in inputs])
                self.assertEqual(results, [(infinity, 0), (infinity | fmt.sign_mask, 0),
                                           (quiet, 0), (quiet, 0), (quiet, 0)])

    def test_rejects_malformed_requests(self) -> None:
        good = request("exp", "RNDN", BINARY32, [0x3F800000])
        self.assertFalse(oracle_fails(good))
        for line in (
            good.replace("format 8 23 127 ieee", "format 8 23 127 finite"),
            good.replace("args 1", "args 2"),
            good.replace("mode RNDN", "mode RNDF"),
            good.replace("0x3f800000", "0x13f800000"),
            good + " extra",
            request("exp", "RNDN", Format(8, 23, 255), [0x3F800000]),
            # A NUL would end the parsed and echoed line early and hide what follows it.
            good + "\0 extra",
            "# comment\0 " + good,
        ):
            with self.subTest(line=line):
                self.assertTrue(oracle_fails(line))


@needs_oracle
class TernaryTests(unittest.TestCase):
    """Result encodings and ternary signs in every mode against exact rational rounding."""

    def check_many(self, cases: list[tuple[str, Format, list[int], Fraction]]) -> None:
        requests = [(operation, mode, fmt, arguments)
                    for operation, fmt, arguments, _ in cases for mode in MODES]
        results = iter(evaluate_all(requests))
        for operation, fmt, arguments, exact in cases:
            for mode in MODES:
                bits, ternary = next(results)
                with self.subTest(operation=operation, fmt=fmt.name, mode=mode,
                                  arguments=[fmt.hex(value) for value in arguments]):
                    expected_bits, expected_ternary = round_exact(exact, fmt, mode)
                    self.assertEqual((fmt.hex(bits), ternary),
                                     (fmt.hex(expected_bits), expected_ternary))

    def check(self, operation: str, fmt: Format, arguments: list[int], exact: Fraction) -> None:
        self.check_many([(operation, fmt, arguments, exact)])

    def test_pi(self) -> None:
        pi = pi_fraction(512)
        for fmt in (BINARY16, BFLOAT16, BINARY32, BINARY64, BINARY128):
            # pi is irrational and 512 bits decide every rounding of these formats.
            self.check("pi", fmt, [], pi)

    def test_negative_logarithm(self) -> None:
        ln2 = Fraction(CORPUS.ln2_scaled(512), 1 << 512)
        for fmt in (BINARY16, BINARY32, BINARY64, BINARY128):
            half = (fmt.bias - 1) << fmt.fraction_bits
            self.check("log", fmt, [half], -ln2)

    def test_exact_results_have_zero_ternary(self) -> None:
        for fmt in (BINARY16, BINARY64, WIDE):
            one = fmt.bias << fmt.fraction_bits
            self.check("exp", fmt, [0], Fraction(1))
            self.check("log", fmt, [one], Fraction(0))
            three, five = encode(fmt, False, Fraction(3)), encode(fmt, False, Fraction(5))
            self.check("pow", fmt, [three, five], Fraction(243))

    def test_signed_zero_results(self) -> None:
        results = evaluate_all([("sin", mode, BINARY32, [0x80000000]) for mode in MODES])
        self.assertEqual(results, [(0x80000000, 0)] * len(MODES))

    def test_overflow_in_every_mode(self) -> None:
        for fmt in (BINARY16, BINARY32, BINARY128):
            emax = (1 << fmt.exponent_bits) - 2 - fmt.bias
            base = Fraction(2) ** (emax // 2 + 1)
            self.check("pow", fmt, [encode(fmt, False, base), encode(fmt, False, Fraction(2))],
                       base * base)
            self.check("pow", fmt, [encode(fmt, True, base), encode(fmt, False, Fraction(3))],
                       -base ** 3)

    def test_subnormal_results_round_once(self) -> None:
        # x^2 and x^3 of small dyadic x land between grid points, on ties and on the grid.
        cases = []
        for fmt in (BINARY16, BINARY32, BINARY64):
            quantum = Fraction(2) ** (1 - fmt.bias - fmt.fraction_bits)
            normal = Fraction(2) ** (1 - fmt.bias)
            for power in (2, 3):
                exponent = encode(fmt, False, Fraction(power))
                for significand in (1, 3, 5, 7, 11, 13):
                    for shift in range(1, 4 * fmt.bias):
                        base = Fraction(significand, 1 << shift)
                        value = base ** power
                        if value < quantum / 4 or (base / quantum).denominator != 1:
                            break
                        if value < normal:
                            cases.append(("pow", fmt, [encode(fmt, False, base), exponent], value))
                            cases.append(("pow", fmt, [encode(fmt, True, base), exponent],
                                          (-base) ** power))
        self.assertGreater(len(cases), 100)
        self.check_many(cases)

    def test_underflow_to_zero_and_to_the_smallest_subnormal(self) -> None:
        for fmt in (BINARY16, BINARY32, BINARY64):
            smallest = Fraction(2) ** (1 - fmt.bias - fmt.fraction_bits)
            self.check("pow", fmt, [encode(fmt, False, smallest), encode(fmt, False, Fraction(2))],
                       smallest * smallest)


class ReportHarness(unittest.TestCase):
    """Writes oracle output, known-failures lists and censuses, and runs the report on them."""

    def setUp(self) -> None:
        self.directory = Path(tempfile.mkdtemp(prefix="floatlib-transcendental-gate-"))
        self.addCleanup(shutil.rmtree, self.directory, True)

    def line(self, operation: str, fmt: Format, arguments: list[int], floatlib: int, mpfr: int,
             ternary: int = 1, floatlib_ternary: int | None = None) -> str:
        return (request(operation, "RNDN", fmt, arguments, floatlib, floatlib_ternary)
                + f" mpfr {fmt.hex(mpfr)} {ternary}")

    @staticmethod
    def shard(lines: list[str], index: int = 0, count: int = 1, requests: int | None = None,
              random_count: int = 0, hard: str = "none", extra: tuple[str, ...] = ()) -> str:
        """One emitter shard of a synthetic invocation."""
        total = len(lines) if requests is None else requests
        manifest = ["emitter test", f"random-count {random_count}", "tier default", f"hard {hard}",
                    "exhaustive16 false", *extra]
        return ("".join(f"# manifest {line}\n" for line in manifest)
                + f"# manifest shard {index}/{count}\n" + "".join(line + "\n" for line in lines)
                + f"# manifest requests {total}\n# emitted {len(lines)}\n")

    def references(self, lines: list[str], text: str | None = None) -> Path:
        path = self.directory / "references.tsv"
        path.write_text(self.shard(lines) if text is None else text, encoding="utf-8")
        return path

    def known(self, rows: list[tuple]) -> Path:
        """A known-failures list of `(id, kind, floatlib[, ternary])` rows."""
        path = self.directory / "known.tsv"
        body = "".join(
            f"{identity}\t{kind}\t"
            f"{REPORT.format_named(identity.split('/')[0]).hex(floatlib)}\t"
            f"{REPORT.ternary_text(ternary[0] if ternary else None)}\tB0\tplanted\n"
            for identity, kind, floatlib, *ternary in rows)
        path.write_text("# test list\n" + body, encoding="utf-8")
        return path

    def empty_census(self) -> Path:
        path = self.directory / "empty-census.json"
        path.write_text(json.dumps({"invocations": {}}), encoding="utf-8")
        return path

    def run_report(self, references: Path, known: Path, census: Path | None = None,
                   *options: str) -> int:
        arguments = ["--input", str(references), "--output-dir", str(self.directory / "out"),
                     "--known-failures", str(known), "--census",
                     str(self.empty_census() if census is None else census), *options]
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return REPORT.main(arguments)

    def run_gate(self, lines: list[str], rows: list[tuple], census: Path | None = None,
                 *options: str, random_count: int = 0, hard: str = "none",
                 extra: tuple[str, ...] = ()) -> int:
        text = self.shard(lines, random_count=random_count, hard=hard, extra=extra)
        return self.run_report(self.references(lines, text), self.known(rows), census, *options)

    # sin(1) in binary32 rounds to 0x3f576aa4; a planted FloatLib result is one ulp off.
    SIN_ONE = (BINARY32, [0x3F800000], 0x3F576AA4)

    def sin_one(self, floatlib: int) -> str:
        fmt, arguments, mpfr = self.SIN_ONE
        return self.line("sin", fmt, arguments, floatlib, mpfr)

    def identity(self) -> str:
        fmt, arguments, _ = self.SIN_ONE
        return REPORT.case_id("sin", "RNDN", fmt, arguments)


class GateTests(ReportHarness):
    def test_matching_run_passes(self) -> None:
        self.assertEqual(self.run_gate([self.sin_one(0x3F576AA4)], []), 0)

    def test_planted_mismatch_fails(self) -> None:
        self.assertEqual(self.run_gate([self.sin_one(0x3F576AA5)], []), 1)

    def test_listed_mismatch_passes(self) -> None:
        listed = [(self.identity(), "value", 0x3F576AA5)]
        self.assertEqual(self.run_gate([self.sin_one(0x3F576AA5)], listed), 0)

    def test_planted_deletion_fails(self) -> None:
        cos_line = self.line("cos", BINARY32, [0x3F800000], 0x3F0A5141, 0x3F0A5140)
        cos_identity = REPORT.case_id("cos", "RNDN", BINARY32, [0x3F800000])
        lines = [self.sin_one(0x3F576AA5), cos_line]
        rows = [(self.identity(), "value", 0x3F576AA5), (cos_identity, "value", 0x3F0A5141)]
        self.assertEqual(self.run_gate(lines, rows), 0)
        self.assertEqual(self.run_gate(lines, rows[:1]), 1)

    def test_listed_failure_that_moves_fails(self) -> None:
        listed = [(self.identity(), "value", 0x3F576AA5)]
        self.assertEqual(self.run_gate([self.sin_one(0x3F576AA6)], listed), 1)
        self.assertEqual(self.run_gate([self.sin_one(0x7F800000)], listed), 1)

    def test_new_nan_from_a_finite_input_fails(self) -> None:
        nan = self.sin_one(0x7FC00000)
        self.assertEqual(self.run_gate([nan], []), 1)
        self.assertEqual(self.run_gate([nan], [(self.identity(), "value", 0x7FC00000)]), 1)
        self.assertEqual(self.run_gate([nan], [(self.identity(), "nan", 0x7FC00000)]), 0)

    def test_stale_entry_fails(self) -> None:
        listed = [(self.identity(), "value", 0x3F576AA5)]
        self.assertEqual(self.run_gate([self.sin_one(0x3F576AA4)], listed), 1)

    def test_unexercised_entry_is_ignored(self) -> None:
        listed = [("binary32/cos/RNDN/0x40000000", "value", 0)]
        self.assertEqual(self.run_gate([self.sin_one(0x3F576AA4)], listed), 0)

    def test_signed_zero_mismatch_fails(self) -> None:
        line = self.line("sin", BINARY32, [0x80000000], 0x00000000, 0x80000000, 0)
        self.assertEqual(self.run_gate([line], []), 1)

    def test_nan_payload_matches_the_reference_nan(self) -> None:
        line = self.line("log", BINARY32, [0xBF800000], 0xFFC00015, 0x7FC00000, 0)
        self.assertEqual(self.run_gate([line], []), 0)

    def test_ternary_mismatch_fails(self) -> None:
        fmt, arguments, mpfr = self.SIN_ONE
        line = self.line("sin", fmt, arguments, mpfr, mpfr, -1, 1)
        self.assertEqual(self.run_gate([line], []), 1)
        self.assertEqual(self.run_gate([line], [(self.identity(), "ternary", mpfr, 1)]), 0)
        self.assertEqual(self.run_gate([line], [(self.identity(), "ternary", mpfr)]), 1)

    # A listed wrong sin(1) whose FloatLib ternary appears or changes; the value mismatch would
    # hide the ternary if the row did not pin it.
    TERNARY_DETERIORATION = ("case binary32/sin/RNDN/0x3f800000 op sin mode RNDN format 8 23 127 "
                             "ieee args 1 0x3f800000 floatlib 0x3f576aa5 ternary 1 "
                             "mpfr 0x3f576aa4 -1")

    def test_listed_failure_whose_ternary_changes_fails(self) -> None:
        line = self.TERNARY_DETERIORATION
        self.assertEqual(self.run_gate([line], [(self.identity(), "value", 0x3F576AA5)]), 1)
        self.assertEqual(self.run_gate([line], [(self.identity(), "value", 0x3F576AA5, -1)]), 1)
        self.assertEqual(self.run_gate([line], [(self.identity(), "value", 0x3F576AA5, 1)]), 0)
        without = self.sin_one(0x3F576AA5)
        self.assertEqual(self.run_gate([without], [(self.identity(), "value", 0x3F576AA5, 1)]),
                         1)

    def test_ternary_difference_in_a_declared_domain_is_handled_by_the_list(self) -> None:
        arguments = [0x40400000, 0x40000000]  # pow(3, 2) = 9 exactly
        identity = REPORT.case_id("pow", "RNDN", BINARY32, arguments)
        line = self.line("pow", BINARY32, arguments, 0x41100000, 0x41100000, 0, 1)
        self.assertEqual(self.run_gate([line], []), 1)
        self.assertEqual(self.run_gate([line], [(identity, "ternary", 0x41100000, 1)]), 0)

    def test_correctly_rounded_domain_fails_even_when_listed(self) -> None:
        # Pi is proved finite and correctly rounded, so neither a wrong finite value nor a
        # nonfinite result may be exempted through the known-failures list.
        pi_identity = REPORT.case_id("pi", "RNDN", BINARY32, [])
        for wrong, kind in ((0x40490FDA, "value"), (0x7FC00000, "nan"),
                            (0x7F800000, "value")):
            with self.subTest(operation="pi", wrong=hex(wrong)):
                line = self.line("pi", BINARY32, [], wrong, 0x40490FDB)
                self.assertEqual(self.run_gate([line], [(pi_identity, kind, wrong)]), 1)
        arguments = [0x40400000, 0x40000000]  # pow(3, 2) = 9
        identity = REPORT.case_id("pow", "RNDN", BINARY32, arguments)
        for wrong in (0x41100001, 0x00000000, 0x7F7FFFFF):
            with self.subTest(wrong=hex(wrong)):
                line = self.line("pow", BINARY32, arguments, wrong, 0x41100000, 0)
                self.assertEqual(self.run_gate([line], [(identity, "value", wrong)]), 1)
        # An infinite result is outside the theorem, a zero of the wrong sign agrees in value,
        # and a custom bias is not an IEEE descriptor; their listed mismatches pass.
        infinite = self.line("pow", BINARY32, arguments, 0x7F800000, 0x41100000, 0)
        self.assertEqual(self.run_gate([infinite], [(identity, "value", 0x7F800000)]), 0)
        tiny = [0x00000001, 0x40000000]
        zero = self.line("pow", BINARY32, tiny, 0x80000000, 0x00000000, -1)
        zero_identity = REPORT.case_id("pow", "RNDN", BINARY32, tiny)
        self.assertEqual(self.run_gate([zero], [(zero_identity, "value", 0x80000000)]), 0)
        custom = Format(8, 23, 239)
        custom_line = self.line("pow", custom, [0x77C00000, 0x78000000], 0x78100001,
                                0x78100000, 0)
        custom_identity = REPORT.case_id("pow", "RNDN", custom, [0x77C00000, 0x78000000])
        self.assertEqual(self.run_gate([custom_line], [(custom_identity, "value", 0x78100001)]),
                         0)
        non_integral = [0x40400000, 0x3FC00000]
        line = self.line("pow", BINARY32, non_integral, 0x40A646E2, 0x40A646E1, -1)
        listed = REPORT.case_id("pow", "RNDN", BINARY32, non_integral)
        self.assertEqual(self.run_gate([line], [(listed, "value", 0x40A646E2)]), 0)

    def test_missing_floatlib_result_is_rejected(self) -> None:
        fmt, arguments, mpfr = self.SIN_ONE
        line = request("sin", "RNDN", fmt, arguments) + f" mpfr {fmt.hex(mpfr)} 1"
        with self.assertRaisesRegex(ValueError, "no FloatLib result"):
            self.run_gate([line], [])

    def test_case_id_must_name_its_content(self) -> None:
        line = self.sin_one(0x3F576AA4).replace(self.identity(), "binary32/sin/RNDN/0x40000000")
        with self.assertRaisesRegex(ValueError, "does not name its content"):
            self.run_gate([line], [])

    def test_duplicates_and_truncation_are_rejected(self) -> None:
        line = self.sin_one(0x3F576AA4)
        with self.assertRaisesRegex(ValueError, "duplicate case"):
            self.run_gate([line, line], [])
        truncated = self.shard([line]).replace("# emitted 1", "# emitted 2")
        with self.assertRaisesRegex(ValueError, "announced 2 cases"):
            REPORT.parse_references(self.references([], truncated))

    def test_every_shard_of_the_run_is_required(self) -> None:
        sin_line = self.sin_one(0x3F576AA4)
        cos_line = self.line("cos", BINARY32, [0x3F800000], 0x3F0A5140, 0x3F0A5140)
        complete = (self.shard([sin_line], 0, 2, requests=2)
                    + self.shard([cos_line], 1, 2, requests=2))
        cases, _, count = REPORT.parse_references(self.references([], complete))
        self.assertEqual((len(cases), count), (2, 2))
        for text, message in (
            (self.shard([sin_line], 0, 2, requests=2), "expected shards 0..1"),
            (self.shard([sin_line], 0, 2, requests=2) + self.shard([cos_line], 0, 2, requests=2),
             "expected shards 0..1"),
            (self.shard([sin_line], 0, 1, requests=2), "selected 2 requests"),
            (self.shard([sin_line], 0, 2, requests=2)
             + self.shard([cos_line], 1, 2, requests=2, random_count=1),
             "different invocations"),
            (sin_line + "\n", "outside a shard block"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    REPORT.parse_references(self.references([], text))

    def test_incomplete_or_repeated_manifests_are_rejected(self) -> None:
        line = self.sin_one(0x3F576AA4)
        complete = self.shard([line])
        for text, message in (
            (complete.replace("# manifest exhaustive16 false\n", ""), "exhaustive16 exactly once"),
            (complete.replace("# manifest tier default\n", "# manifest tier default\n" * 2),
             "repeats a line"),
            (complete.replace("# manifest tier default\n",
                              "# manifest tier default\n# manifest tier slow\n"),
             "tier exactly once"),
            (complete.replace("tier default", "tier fast"), "unknown tier"),
            (complete.replace("exhaustive16 false", "exhaustive16 no"), "true or false"),
            (complete.replace("random-count 0", "random-count 00"), "invalid random count"),
            (self.shard([line], extra=("seed binary32 1", "seed binary32 2")), "seed twice"),
            (complete.replace("# manifest shard 0/1\n", "# manifest shard 0/1\n" * 2),
             "repeated shard line"),
            (complete.replace("# manifest requests 1\n", "# manifest requests 1\n" * 2),
             "repeated request count"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    REPORT.parse_references(self.references([], text))

    def test_details_round_trip(self) -> None:
        lines = [self.TERNARY_DETERIORATION,
                 self.line("cos", BINARY32, [0x3F800000], 0x7FC00000, 0x3F0A5140),
                 self.line("pow", BINARY16, [0x3C00, 0x4000], 0x3C00, 0x3C00, 0)]
        cases, _, _ = REPORT.parse_references(self.references(lines))
        results = {"FloatLib": [case.floatlib for case in cases],
                   "OpenLibm": [0x3F576AA4, 0x3F0A5141, None]}
        path = self.directory / "details.tsv"
        REPORT.write_details(path, cases, results)
        read_cases, read_results = REPORT.read_details(path)
        self.assertEqual(read_results, results)
        self.assertEqual([(case.case_id, case.mpfr, case.mpfr_ternary, case.floatlib)
                          for case in read_cases],
                         [(case.case_id, case.mpfr, case.mpfr_ternary, case.floatlib)
                          for case in cases])
        self.assertEqual(REPORT.summarize(read_cases, read_results),
                         REPORT.summarize(cases, results))
        text = path.read_text(encoding="utf-8")
        rows = text.splitlines(keepends=True)
        self.assertIn("\t1\t0\n", text)
        for broken in (rows[0].replace("OpenLibm_ulp", "Other_ulp") + "".join(rows[1:]),
                       text.replace("0x3f576aa5", "0x3F576AA5"),
                       text.replace("\t1\t0\n", "\t1\t3\n", 1),
                       text + rows[1]):
            with self.subTest(broken=broken):
                path.write_text(broken, encoding="utf-8")
                with self.assertRaises(ValueError):
                    REPORT.read_details(path)

    def test_written_list_makes_the_gate_pass(self) -> None:
        lines = [self.TERNARY_DETERIORATION,
                 self.line("cos", BINARY32, [0x3F800000], 0x7FC00000, 0x3F0A5140)]
        written = self.directory / "written.tsv"
        cases, manifest, _ = REPORT.parse_references(self.references(lines))
        previous = REPORT.parse_known_failures(self.known([("binary32/exp/RNDN/0x40000000",
                                                             "value", 0x40EC7326, -1)]))
        self.assertEqual(REPORT.write_known_failures(written, cases, manifest, previous), 3)
        known = REPORT.parse_known_failures(written)
        self.assertEqual(sorted(entry.kind for entry in known.values()), ["nan", "value", "value"])
        self.assertEqual(known["binary32/exp/RNDN/0x40000000"].floatlib, 0x40EC7326)
        self.assertEqual(known["binary32/exp/RNDN/0x40000000"].floatlib_ternary, -1)
        self.assertEqual(known[self.identity()].floatlib_ternary, 1)
        self.assertIsNone(known["binary32/cos/RNDN/0x3f800000"].floatlib_ternary)
        self.assertTrue(REPORT.gate(cases, known).passed)

    def test_malformed_known_failures_are_rejected(self) -> None:
        for row in ("binary32/sin/RNDN/0x3f800000\tvalue\t0x3f576aa5\t-\tB0",
                    "binary32/sin/RNDN/0x3f800000\tvalue\t0x3f576aa5\tB0\tnote",
                    "binary32/sin/RNDN/0x3f800000\twrong\t0x3f576aa5\t-\tB0\tnote",
                    "binary32/sin/RNDN/0x3f800000\tvalue\t0x3f576aa\t-\tB0\tnote",
                    "binary32/sin/RNDN/0x3f800000\tvalue\t0x3f576aa5\t+1\tB0\tnote",
                    "binary32/sin/RNDN/0x3f800000\tvalue\t0x3f576aa5\t\tB0\tnote",
                    "binary32/sin/RNDN/0x3f80000\tvalue\t0x3f576aa5\t-\tB0\tnote",
                    "binary32/sin/RNDN\tvalue\t0x3f576aa5\t-\tB0\tnote"):
            with self.subTest(row=row):
                path = self.directory / "bad.tsv"
                path.write_text(row + "\n", encoding="utf-8")
                with self.assertRaises(ValueError):
                    REPORT.parse_known_failures(path)


class CensusTests(ReportHarness):
    """A run of a recorded invocation must reproduce the census entry's requests exactly."""

    def lines(self) -> list[str]:
        return [self.sin_one(0x3F576AA4),
                self.line("cos", BINARY32, [0x3F800000], 0x3F0A5140, 0x3F0A5140),
                self.line("exp", BINARY32, [0x3F800000], 0x402DF854, 0x402DF854)]

    def coverage(self, lines: list[str], census: Path, text: str | None = None,
                 unexercised: int = 0):
        cases, manifest, _ = REPORT.parse_references(self.references(lines, text))
        return REPORT.check_coverage(cases, manifest, REPORT.read_census(census), unexercised)

    def test_a_run_missing_a_case_fails(self) -> None:
        census = self.directory / "census.json"
        lines = self.lines()
        self.assertEqual(self.run_gate(lines, [], census, "--write-census", "default"), 0)
        self.assertEqual(REPORT.read_census(census)["default"].requests, 3)
        self.assertEqual(self.run_gate(lines, [], census), 0)
        self.assertEqual(self.coverage(lines, census).status, "checked")
        # One case removed, with shard trailers that agree with what is left.
        self.assertEqual(self.run_gate(lines[1:], [], census), 1)
        coverage = self.coverage(lines[1:], census)
        self.assertEqual((coverage.census, coverage.status), ("default", "failed"))
        self.assertIn("2 requests, census 3", coverage.differences)
        self.assertIn("binary32/sin: 0 requests, census 1", coverage.differences)
        # One case replaced by another of the same format and operation.
        replaced = [self.line("sin", BINARY32, [0x40000000], 0x3F68C7B7, 0x3F68C7B7), *lines[1:]]
        self.assertEqual(self.run_gate(replaced, [], census), 1)
        self.assertEqual(len(self.coverage(replaced, census).differences), 1)
        # The same cases in two shards are the same run.
        split = self.shard(lines[:2], 0, 2, requests=3) + self.shard(lines[2:], 1, 2, requests=3)
        self.assertEqual(self.run_report(self.references([], split), self.known([]), census), 0)

    def test_unrecorded_invocation_is_unchecked(self) -> None:
        census = self.directory / "census.json"
        lines = self.lines()
        self.assertEqual(self.run_gate(lines, [], census, "--write-census", "default"), 0)
        other = self.shard(lines[1:], random_count=1)
        coverage = self.coverage([], census, other)
        self.assertEqual((coverage.census, coverage.status), (None, "unchecked"))
        self.assertEqual(self.run_gate(lines[1:], [], census, random_count=1), 0)

    def test_manifest_and_corpus_are_part_of_the_record(self) -> None:
        corpus = self.directory / "corpus.tsv"
        corpus.write_text("# corpus\n", encoding="utf-8")
        census = self.directory / "census.json"
        lines = self.lines()
        self.assertEqual(self.run_gate(lines, [], census, "--write-census", "default",
                                       hard=str(corpus)), 0)
        self.assertEqual(self.run_gate(lines, [], census, hard=str(corpus)), 0)
        # Another seed, a copy of the corpus, or another name for it differs from the record.
        self.assertEqual(self.run_gate(lines, [], census, hard=str(corpus), extra=("seed b 1",)),
                         1)
        copy = self.directory / "copy.tsv"
        shutil.copyfile(corpus, copy)
        self.assertEqual(self.run_gate(lines, [], census, hard=str(copy)), 1)
        self.assertEqual(self.run_gate(lines, [], census, hard=f"{corpus.parent}/./{corpus.name}"),
                         1)
        self.assertEqual(self.run_gate(lines, [], census), 1)
        # A changed or deleted corpus differs from its recorded sha256.
        corpus.write_text("# another corpus\n", encoding="utf-8")
        self.assertEqual(self.run_gate(lines, [], census, hard=str(corpus)), 1)
        corpus.unlink()
        self.assertEqual(self.run_gate(lines, [], census, hard=str(corpus)), 1)

    def test_qualification_run_must_exercise_every_listed_case(self) -> None:
        lines = [self.sin_one(0x3F576AA5), *self.lines()[1:]]
        listed = [(self.identity(), "value", 0x3F576AA5)]
        more = listed + [("binary32/cos/RNDN/0x40000000", "value", 0)]
        census = self.directory / "census.json"
        self.assertEqual(self.run_gate(lines, listed, census, "--write-census", "qualification"),
                         0)
        self.assertEqual(self.run_gate(lines, listed, census), 0)
        self.assertEqual(self.run_gate(lines, more, census), 1)
        other = self.directory / "other.json"
        self.assertEqual(self.run_gate(lines, more, other, "--write-census", "release"), 0)
        self.assertEqual(self.run_gate(lines, more, other), 0)

    # A one-case run whose manifest claims the qualification invocation; its trailers agree.
    FORGED_QUALIFICATION_RUN = (
        "# manifest emitter transcendentalEmitter\n"
        "# manifest random-count 256\n"
        "# manifest tier slow\n"
        "# manifest hard tests/oracles/data/transcendental-hard-cases.tsv\n"
        "# manifest exhaustive16 true\n"
        "# manifest shard 0/1\n"
        "case binary32/sin/RNDN/0x3f800000 op sin mode RNDN format 8 23 127 ieee args 1 "
        "0x3f800000 floatlib 0x3f576aa4 mpfr 0x3f576aa4 -1\n"
        "# manifest requests 1\n"
        "# emitted 1\n")

    def test_forged_qualification_run_fails(self) -> None:
        references = self.references([], self.FORGED_QUALIFICATION_RUN)
        listed = self.known([("ieee31_23/sin/RNDN/0x2007ffff400000", "nan", 0x3FFFFFFFC00000)])
        self.assertEqual(self.run_report(references, listed, CENSUS_FILE), 1)
        known = REPORT.parse_known_failures(listed)
        cases, manifest, _ = REPORT.parse_references(references)
        result = REPORT.gate(cases, known)
        self.assertTrue(result.passed)
        coverage = REPORT.check_coverage(cases, manifest, REPORT.read_census(CENSUS_FILE),
                                         result.unexercised)
        self.assertEqual((coverage.census, coverage.status), ("qualification", "failed"))
        self.assertIn(f"{len(known)} listed known failures were not exercised",
                      coverage.differences)
        # With the recorded manifest, seeds included, its requests still give it away.
        recorded = REPORT.read_census(CENSUS_FILE)["qualification"].manifest
        forged = ("".join(f"# manifest {line}\n" for line in recorded) + "# manifest shard"
                  + self.FORGED_QUALIFICATION_RUN.split("# manifest shard", 1)[1])
        self.assertEqual(self.run_report(self.references([], forged), listed, CENSUS_FILE), 1)
        coverage = self.coverage([], CENSUS_FILE, forged, result.unexercised)
        self.assertFalse(any(difference.startswith("manifest") for difference in
                             coverage.differences))
        self.assertTrue(any(difference.startswith("1 requests, census") for difference in
                            coverage.differences))

    def test_driver_states_the_invocation(self) -> None:
        census = self.directory / "census.json"
        lines = self.lines()
        self.assertEqual(self.run_gate(lines, [], census, "--write-census", "default"), 0)
        self.assertEqual(self.run_gate(lines, [], census, "--expect-manifest", "random-count 0",
                                       "--expect-manifest", "tier default"), 0)
        with self.assertRaisesRegex(ValueError, "driver asked for `random-count 1`"):
            self.run_gate(lines, [], census, "--expect-manifest", "random-count 1")
        # A required entry must be reproduced; another invocation is no longer unchecked.
        self.assertEqual(self.run_gate(lines, [], census, "--require-census", "default"), 0)
        self.assertEqual(self.run_gate(lines, [], census, "--require-census", "default",
                                       random_count=1), 1)
        with self.assertRaisesRegex(ValueError, "no entry 'release'"):
            self.run_gate(lines, [], census, "--require-census", "release")
        summary = json.loads((self.directory / "out" / "summary.json").read_text())
        self.assertEqual(summary["coverage"]["entry"]["requests"], 3)

    # A one-case run that reports random count 255 instead of the release run's 256.
    MISREPORTED_RELEASE_RUN = FORGED_QUALIFICATION_RUN.replace(
        "random-count 256", "random-count 255").replace("tier slow", "tier default").replace(
        "exhaustive16 true", "exhaustive16 false")

    def test_misreported_release_run_fails_when_the_driver_states_it(self) -> None:
        references = self.references([], self.MISREPORTED_RELEASE_RUN)
        self.assertEqual(self.run_report(references, KNOWN_FAILURES_FILE, CENSUS_FILE), 0)
        self.assertEqual(self.run_report(references, KNOWN_FAILURES_FILE, CENSUS_FILE,
                                         "--require-census", "release"), 1)
        with self.assertRaisesRegex(ValueError, "driver asked for"):
            self.run_report(references, KNOWN_FAILURES_FILE, CENSUS_FILE,
                            "--expect-manifest", "random-count 256")

    def test_entries_record_distinct_invocations(self) -> None:
        census = self.directory / "census.json"
        lines = self.lines()
        self.assertEqual(self.run_gate(lines, [], census, "--write-census", "default"), 0)
        self.assertEqual(self.run_gate(lines, [], census, "--write-census", "default"), 0)
        with self.assertRaisesRegex(ValueError, "already records this invocation"):
            self.run_gate(lines, [], census, "--write-census", "release")
        with self.assertRaisesRegex(ValueError, "invalid census entry name"):
            self.run_gate(lines, [], census, "--write-census", "Release")

    def test_malformed_census_is_rejected(self) -> None:
        census = self.directory / "census.json"
        self.assertEqual(self.run_gate(self.lines(), [], census, "--write-census", "default"), 0)
        entry = json.loads(census.read_text(encoding="utf-8"))["invocations"]["default"]
        for data in (
            {"invocations": {"default": {**entry, "requests": 4}}},
            {"invocations": {"default": {**entry, "case_ids_sha256": "0" * 63}}},
            {"invocations": {"default": {**entry, "manifest": entry["manifest"][::-1]}}},
            {"invocations": {"default": {**entry, "manifest": entry["manifest"][1:]}}},
            {"invocations": {"default": {**entry, "requests_by_operation": {"binary32": 3}}}},
            {"invocations": {"default": {**entry, "extra": 1}}},
            {"invocations": {"Default": entry}},
            {"invocations": {"default": entry, "release": entry}},
            {"invocations": {}, "other": 1},
        ):
            with self.subTest(data=data):
                census.write_text(json.dumps(data), encoding="utf-8")
                with self.assertRaises(ValueError):
                    REPORT.read_census(census)


class CheckedInDataTests(unittest.TestCase):
    def test_known_failures_are_well_formed(self) -> None:
        known = REPORT.parse_known_failures(KNOWN_FAILURES_FILE)
        names = {fmt.name for fmt in (BINARY16, BFLOAT16, BINARY32, BINARY64, BINARY128, WIDE)}
        for identity, entry in known.items():
            self.assertIn(identity.split("/")[0], names, identity)
            self.assertRegex(entry.owner, r"^B\d+$")

    def test_census_records_the_standard_invocations(self) -> None:
        # Counts and digests are checked by the runs themselves; transcendental_compare.sh runs
        # these tests first, so they must not block recording a new census.
        census = REPORT.read_census(CENSUS_FILE)
        hard = "hard tests/oracles/data/transcendental-hard-cases.tsv"
        expected = {"default": ("32", "default", "false"), "release": ("256", "default", "false"),
                    "qualification": ("256", "slow", "true")}
        self.assertEqual(set(census), set(expected))
        for name, (count, tier, exhaustive) in expected.items():
            self.assertEqual(REPORT.census_key(census[name].manifest),
                             (f"exhaustive16 {exhaustive}", f"random-count {count}",
                              f"tier {tier}"), name)
            self.assertIn(hard, census[name].manifest, name)

    def test_corpus_rows_are_well_formed(self) -> None:
        counts: dict[tuple[str, str], int] = {}
        encodings: set[tuple[str, int]] = set()
        for line in CORPUS_FILE.read_text(encoding="utf-8").splitlines():
            if line.startswith("#"):
                continue
            tier, kind, name, operations, arguments, _note = line.split("\t")
            self.assertIn(tier, ("default", "slow"))
            self.assertIn(kind, ("trig-cf", "named", "boundary"))
            fmt = CORPUS.FORMATS[name]
            values = [int(text, 16) for text in arguments.split(",")]
            self.assertTrue(all(0 <= value < 1 << fmt.width for value in values), line)
            for operation in operations.split(","):
                self.assertEqual(REPORT.ARITIES[operation], len(values), line)
            counts[(kind, name)] = counts.get((kind, name), 0) + 1
            if kind == "trig-cf":
                encodings.add((name, values[0]))
        expected = {"binary16": 17, "bfloat16": 129, "binary32": 129, "binary64": 1025,
                    "binary128": 16385}
        for name, count in expected.items():
            self.assertEqual(counts[("trig-cf", name)], count, name)
        b64, b32 = CORPUS.FORMATS["binary64"], CORPUS.FORMATS["binary32"]
        self.assertIn(("binary64", 0x7FE61A3DB8C8D129), encodings)
        self.assertIn(("binary64", b64.encode(6381956970095103, 797)), encodings)
        self.assertIn(("binary32", b32.encode(16367173, 72)), encodings)

    def test_generator_reproduces_the_checked_in_rows(self) -> None:
        trig = ["binary16", "bfloat16", "binary32"]
        regenerated = [tuple(row) for row in CORPUS.trig_rows(trig) + CORPUS.named_rows()
                       + CORPUS.boundary_rows(list(CORPUS.FORMATS))]
        checked_in = [tuple(line.split("\t")) for line in
                      CORPUS_FILE.read_text(encoding="utf-8").splitlines()
                      if not line.startswith("#")]
        selected = [row for row in checked_in if row[1] != "trig-cf" or row[2] in trig]
        self.assertEqual(regenerated, selected)

    def test_sampled_wide_binades_match_the_generator(self) -> None:
        checked_in = {tuple(line.split("\t")) for line in
                      CORPUS_FILE.read_text(encoding="utf-8").splitlines()
                      if not line.startswith("#")}
        for name, stride in (("binary64", 41), ("binary128", 1009)):
            fmt = CORPUS.FORMATS[name]
            for binade in [*range(-1, fmt.emax + 1, stride), fmt.emax]:
                with self.subTest(fmt=name, binade=binade):
                    self.assertIn(CORPUS.trig_row(fmt, binade), checked_in)

    def test_published_hard_cases_are_the_best_in_their_binades(self) -> None:
        self.assertEqual(CORPUS.best_in_binade(CORPUS.FORMATS["binary64"], 849)[0],
                         6381956970095103)
        self.assertEqual(CORPUS.best_in_binade(CORPUS.FORMATS["binary64"], 1023)[0],
                         6221301883130153)
        self.assertEqual(CORPUS.best_in_binade(CORPUS.FORMATS["binary32"], 95)[0], 16367173)


FIXTURE_FORMATS = {
    "binary16": BINARY16, "bfloat16": BFLOAT16, "binary32": BINARY32, "binary64": BINARY64,
    "binary128": BINARY128, "binary256": REPORT.CATALOG["binary256"],
    "ieee20x37": REPORT.ieee(20, 37), "ieee31x23": WIDE,
    "ieee31x52": REPORT.ieee(31, 52), "bias239": Format(8, 23, 239),
}
FIXTURE_ROW = re.compile(
    r"format := \.(\w+),\s*operation := \.(\w+),\s*arguments := \[([^\]]*)\],\s*"
    r"expected := (0x[0-9a-f]+)")


@needs_oracle
class FixtureTests(unittest.TestCase):
    def test_lean_fixtures_are_mpfr_results(self) -> None:
        text = FIXTURES.read_text(encoding="utf-8")
        rows = FIXTURE_ROW.findall(text)
        self.assertEqual(len(rows), text.count("expected := 0x"))
        self.assertGreater(len(rows), 80)
        requests = [(operation, "RNDN", FIXTURE_FORMATS[name],
                     [int(value, 16) for value in arguments.split(",")])
                    for name, operation, arguments, _ in rows]
        results = evaluate_all(requests)
        for (name, operation, arguments, expected), (bits, _) in zip(rows, results, strict=True):
            with self.subTest(fmt=name, operation=operation, arguments=arguments):
                self.assertEqual(bits, int(expected, 16))


def sin_one_scaled(bits: int) -> int:
    """floor(sin(1) * 2^bits) up to one unit, from the alternating series."""
    guard = 32
    one = 1 << (bits + guard)
    total, term, k = 0, one, 1
    while term:
        total += term if k % 4 == 1 else -term
        term = term // ((k + 1) * (k + 2))
        k += 2
    return total >> guard


@needs_oracle
class ContainmentTests(unittest.TestCase):
    def query(self, operation: str, fmt: Format, arguments: list[int], lower: tuple[int, int],
              upper: tuple[int, int]) -> tuple[str, int]:
        line = (f"contain c op {operation} format {fmt.exponent_bits} {fmt.fraction_bits} "
                f"{fmt.bias} ieee args {len(arguments)} "
                + " ".join(fmt.hex(bits) for bits in arguments)
                + f" lower {lower[0]} {lower[1]} upper {upper[0]} {upper[1]}")
        fields = run_oracle([line])[0].split()
        return fields[-3], int(fields[-1])

    def test_narrow_interval_needs_rising_precision(self) -> None:
        scaled = sin_one_scaled(300)
        verdict, precision = self.query("sin", BINARY64, [0x3FF0000000000000],
                                        (scaled - 1, -300), (scaled + 1, -300))
        self.assertEqual(verdict, "inside")
        self.assertGreater(precision, 300)
        verdict, _ = self.query("sin", BINARY64, [0x3FF0000000000000],
                                (scaled + 2, -300), (scaled + 3, -300))
        self.assertEqual(verdict, "outside")

    def test_exact_values_and_domain_errors(self) -> None:
        self.assertEqual(self.query("exp", BINARY32, [0], (1, 0), (1, 0))[0], "inside")
        self.assertEqual(self.query("exp", BINARY32, [0], (2, 0), (3, 0))[0], "outside")
        self.assertEqual(self.query("log", BINARY32, [0xBF800000], (-1, 0), (1, 0))[0], "nan")

    def test_starting_precision_is_capped(self) -> None:
        # A 600,000-bit fraction field would start the search at 1,200,002 bits.
        line = "contain c op exp format 8 600000 127 ieee args 1 0x0 lower 1 0 upper 1 0"
        self.assertEqual(run_oracle([line])[0].split()[-3:], ["inside", "precision", "1048576"])


if __name__ == "__main__":
    unittest.main()
