"""P3109 v4.1 closed functions checked with Fraction and directed MPFR.

The same corpus covers the functions of IEEE 754-2019 clause 9.2 that the report does not
list and FloatLib provides on P3109 formats: Exp10, Exp2MinusOne, Exp10MinusOne, Log10,
Log2OnePlus, Log10OnePlus and Cbrt with one operand, Pow and Powr with an exponent in
Binary8p3se, and Pown, Rootn and Compound with the integers from -3 to 3. Their special cases
are those of IEEE 754-2019 9.2.1 with the conventions of the report: one zero, one NaN, a NaN
operand gives NaN, and a pole at zero gives NaN.

The projection oracle uses the report's logarithmic quantum and fraction
formulas from p3109_comparison. MPFR enclosures must produce a unique output
under every tested policy. Correctly rounded nonexact direct MPFR results
have open endpoints; this matters for expm1(x) near -1 and tanh(x) near 1.
No finite tolerance or nearest-only agreement is accepted.
"""

import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import subprocess

import gmpy2 as g

from p3109_comparison import Format, pow2
from posit_functions import elementary_bounds, enclosure


MODE_COUNT = 27  # Six deterministic modes and all words at widths 0, 1, 2.
PRECISIONS = (192, 384, 768, 1536, 3072)
precision_counts = Counter()
UNARY_NAMES = (
    "Log", "Log2", "LogOnePlus", "Exp", "Exp2", "ExpMinusOne",
    "Sin", "Cos", "Tan", "ArcSin", "ArcCos", "ArcTan", "Sinh", "Cosh",
    "Tanh", "ArcSinh", "ArcCosh", "ArcTanh", "SinPi", "CosPi", "TanPi",
    "ArcSinPi", "ArcCosPi", "ArcTanPi", "Softplus",
    # IEEE 754-2019 9.2 functions that the report does not list (FloatLib extensions).
    "Exp10", "Exp2MinusOne", "Exp10MinusOne", "Log10", "Log2OnePlus", "Log10OnePlus", "Cbrt",
)


def expected_coverage(first, last):
    """Report-valid small descriptors and the producer's stated operand corpus."""
    pairs = set()
    counts = Counter()
    for width in range(first, last):
        for precision in range(1, width + 1):
            for signed in (True, False):
                if signed and precision == width:
                    continue
                for extended in (False, True):
                    source = (str(width), str(precision), str(signed).lower(),
                              str(extended).lower())
                    for target in (source, ("8", "3", "true", "true")):
                        pairs.add(source + target)
                        counts.update({name: 2 ** width for name in UNARY_NAMES})
                        if width <= 4:
                            counts.update({name: 12 * 2 ** width
                                           for name in ("ArcTan2", "ArcTan2Pi", "Pow", "Powr")})
                            counts.update({name: 7 * 2 ** width
                                           for name in ("Pown", "Rootn", "Compound")})
    return pairs, counts


class OracleFormat(Format):
    def __init__(self, *args):
        super().__init__(*args)
        self.by_code = {code: value for value, code in self.values.items()}
        # Every possible discontinuity through the first overflow grid point
        # is a dyadic subdivision of an adjacent finite interval.
        ordered = sorted(self.values)
        last_unit = pow2(max(self.maximum.numerator.bit_length()
                            - self.maximum.denominator.bit_length(), 1 - self.bias)
                        - self.precision + 1)
        ordered.append(self.maximum + last_unit)
        critical = {F(0)}
        for a, b in zip(ordered, ordered[1:]):
            for part in range(17):
                value = a + F(part, 16) * (b - a)
                critical.update((value, -value))
        self.critical = sorted(critical)
        self.critical_set = critical

    def decode(self, word):
        if word == self.nan:
            return "nan"
        if self.extended and word == self.infinity:
            return "+inf"
        negative = self.signed and word >= 2 ** (self.width - 1)
        magnitude = word - 2 ** (self.width - 1) if negative else word
        if negative and self.extended and magnitude == self.infinity:
            return "-inf"
        value = self.by_code[magnitude]
        return -value if negative else value

    def project(self, value):
        if not isinstance(value, str):
            return self.expected(value)[:MODE_COUNT * 3]
        if value == "nan":
            return [self.nan] * (MODE_COUNT * 3)
        negative = value == "-inf"
        endpoint = (self.maximum_code + 2 ** (self.width - 1) if self.signed else 0
                    ) if negative else self.maximum_code
        has_infinity = self.extended and (self.signed or not negative)
        infinity = ((2 ** self.width - 1) if negative else self.infinity
                    ) if has_infinity else self.nan
        return [code for _ in range(MODE_COUNT)
                for code in (endpoint, infinity if has_infinity else endpoint, infinity)]

    def enclose(self, lower, upper, strict):
        lower = F(*(int(part) for part in lower.as_integer_ratio()))
        upper = F(*(int(part) for part in upper.as_integer_ratio()))
        assert lower <= upper
        if strict and lower != upper:
            original_lower, original_upper = lower, upper
            if lower in self.critical_set:
                index = bisect_right(self.critical, lower)
                next_cut = self.critical[index] if index < len(self.critical) else upper
                lower += (min(next_cut, original_upper) - lower) / 2
            if upper in self.critical_set:
                index = bisect_left(self.critical, upper) - 1
                previous_cut = self.critical[index] if index >= 0 else original_lower
                upper -= (upper - max(previous_cut, original_lower)) / 2
        first, last = self.project(lower), self.project(upper)
        return first if first == last else None


@lru_cache(None)
def descriptor(width, precision, signed, extended):
    return OracleFormat(width, precision, signed, extended)


NAMES = {
    "Log": "log", "Log2": "log2", "LogOnePlus": "logp1",
    "Exp": "exp", "Exp2": "exp2", "ExpMinusOne": "expm1",
    "Sin": "sin", "Cos": "cos", "Tan": "tan",
    "ArcSin": "arcSin", "ArcCos": "arcCos", "ArcTan": "arcTan",
    "Sinh": "sinH", "Cosh": "cosH", "Tanh": "tanH",
    "ArcSinh": "arcSinH", "ArcCosh": "arcCosH", "ArcTanh": "arcTanH",
    "SinPi": "sinPi", "CosPi": "cosPi", "TanPi": "tanPi",
    "ArcSinPi": "arcSinPi", "ArcCosPi": "arcCosPi", "ArcTanPi": "arcTanPi",
    "Softplus": "softplus",
    "Exp10": "exp10", "Exp2MinusOne": "exp2Minus1", "Exp10MinusOne": "exp10Minus1",
    "Log10": "log10", "Log2OnePlus": "log2Plus1", "Log10OnePlus": "log10Plus1",
    "Cbrt": "rootn",
}


def angle_bounds(precision, multiple):
    numerator = enclosure(precision, lambda: g.const_pi() * g.mpq(
        multiple.numerator, multiple.denominator))
    # For a negative multiplier the directed expression still encloses the
    # product because MPFR multiplies the rounded pi in the opposite direction.
    if multiple < 0:
        positive = enclosure(precision, lambda: g.const_pi() * g.mpq(
            -multiple.numerator, multiple.denominator))
        return -positive[1], -positive[0]
    return numerator


def real_projection(target, name, x, y=None, angle=None, integer=None):
    for precision in PRECISIONS:
        try:
            if angle is not None:
                lower, upper = angle_bounds(precision, angle)
            elif name == "softplus":
                # Both functions are increasing, so directed composition
                # encloses the exact result. Rational arguments are exact.
                lower, upper = enclosure(precision, lambda: g.log1p(
                    g.exp(g.mpfr(g.mpq(x.numerator, x.denominator)))))
            else:
                lower, upper = elementary_bounds(precision, name, x, y, integer)
        except ArithmeticError:
            continue
        strict = angle is None and "Pi" not in name
        result = target.enclose(lower, upper, strict)
        if result is not None:
            precision_counts[precision] += 1
            return result
    raise ArithmeticError(f"Unresolved directed rounding: {name=} {x=} {y=} {angle=}")


def unary(target, name, x):
    if x == "nan":
        return target.project("nan")
    if isinstance(x, str):
        negative = x == "-inf"
        if name in ("Log", "Log2", "LogOnePlus", "ArcCosh", "Log10", "Log2OnePlus",
                    "Log10OnePlus"):
            return target.project("nan" if negative else "+inf")
        if name in ("Exp", "Exp2", "ExpMinusOne", "Softplus", "Exp10", "Exp2MinusOne",
                    "Exp10MinusOne"):
            return target.project(F(-1 if name.endswith("MinusOne") else 0)
                                  if negative else "+inf")
        if name in ("Sinh", "ArcSinh", "Cbrt"):
            return target.project(x)
        if name == "Cosh":
            return target.project("+inf")
        if name == "Tanh":
            return target.project(F(-1 if negative else 1))
        if name in ("ArcTan", "ArcTanPi"):
            angle = F(-1 if negative else 1, 2)
            return target.project(angle) if name == "ArcTanPi" else real_projection(
                target, "angle", F(0), angle=angle)
        return target.project("nan")
    if name in ("Log", "Log2", "LogOnePlus", "Log10", "Log2OnePlus", "Log10OnePlus"):
        argument = x + name.endswith("OnePlus")
        if argument <= 0:
            return target.project("-inf" if argument == 0 else "nan")
    if name == "Cbrt":
        if x == 0:
            return target.project(F(0))
        return real_projection(target, "rootn", x, integer=3)
    if (name in ("ArcSin", "ArcCos", "ArcSinPi", "ArcCosPi") and abs(x) > 1
            or name == "ArcCosh" and x < 1 or name == "ArcTanh" and abs(x) > 1):
        return target.project("nan")
    if name == "ArcTanh" and abs(x) == 1:
        return target.project("-inf" if x < 0 else "+inf")
    if name in ("SinPi", "CosPi", "TanPi") and (2 * x).denominator == 1:
        phase = int(2 * x) % 4
        if name == "TanPi" and phase % 2:
            return target.project("+inf" if phase == 1 else "-inf")
        exact = {"SinPi": (0, 1, 0, -1), "CosPi": (1, 0, -1, 0),
                 "TanPi": (0, 0, 0, 0)}[name][phase]
        return target.project(F(exact))
    if name == "TanPi" and (4 * x).denominator == 1:
        return target.project(F(1 if int(4 * x) % 4 == 1 else -1))
    if name in ("ArcSinPi", "ArcCosPi", "ArcTanPi") and x in (-1, 0, 1):
        exact = {"ArcSinPi": (F(-1, 2), F(0), F(1, 2)),
                 "ArcCosPi": (F(1), F(1, 2), F(0)),
                 "ArcTanPi": (F(-1, 4), F(0), F(1, 4))}[name][int(x) + 1]
        return target.project(exact)
    return real_projection(target, NAMES[name], x)


def binary(target, scaled, y, x):
    if x == "nan" or y == "nan" or isinstance(x, str) and isinstance(y, str):
        return target.project("nan")
    angle = None
    if isinstance(y, str):
        angle = F(-1 if y == "-inf" else 1, 2)
    elif isinstance(x, str):
        angle = F(0) if x == "+inf" else F(-1 if y < 0 else 1)
    elif x == y == 0:
        return target.project("nan")
    elif x == 0:
        angle = F(-1 if y < 0 else 1, 2)
    elif y == 0:
        angle = F(1 if x < 0 else 0)
    elif abs(x) == abs(y):
        angle = F((1 if x > 0 else 3) * (-1 if y < 0 else 1), 4)
    if angle is not None:
        return target.project(angle) if scaled else real_projection(
            target, "angle", F(0), angle=angle)
    return real_projection(target, "arcTan2Pi" if scaled else "arcTan2", x, y)


def real_power(target, x, y):
    """The projection of x ** y for a positive rational x and a rational y."""
    if y.denominator == 1 and abs(y) <= 64:
        return target.project(x ** int(y))
    # Far beyond every threshold of an eight-bit format the result is projected as any real
    # number on that side: MPFR would overflow or underflow there.
    magnitude = float(y) * math.log2(float(x))
    if magnitude > 256:
        return target.project(F(2) ** 256)
    if magnitude < -256:
        return target.project(F(1, 2 ** 256))
    return real_projection(target, "pow", x, y)


def integer_function(target, name, x, n):
    """Pown, Rootn and Compound (IEEE 754-2019 9.2.1) under the conventions of the report."""
    if x == "nan":
        return target.project("nan")
    if name == "Pown":
        if isinstance(x, str):
            if n == 0:
                return target.project(F(1))
            if n < 0:
                return target.project(F(0))
            return target.project("-inf" if x == "-inf" and n % 2 else "+inf")
        if n == 0:
            return target.project(F(1))
        if x == 0:
            return target.project(F(0) if n > 0 else "nan")
        return target.project(x ** n)
    if name == "Compound":
        if isinstance(x, str):
            if x == "-inf":
                return target.project("nan")
            return target.project(F(1) if n == 0 else "+inf" if n > 0 else F(0))
        if x < -1:
            return target.project("nan")
        if x == -1:
            return target.project(F(1) if n == 0 else F(0) if n > 0 else "nan")
        return target.project((1 + x) ** n)
    assert name == "Rootn"
    if n == 0:
        return target.project("nan")
    if isinstance(x, str):
        if x == "-inf" and n % 2 == 0:
            return target.project("nan")
        return target.project(F(0) if n < 0 else x)
    if x == 0:
        return target.project(F(0) if n > 0 else "nan")
    if x < 0 and n % 2 == 0:
        return target.project("nan")
    return real_projection(target, "rootn", x, integer=n)


def power_function(target, name, x, y):
    """Pow and Powr (IEEE 754-2019 9.2.1) under the conventions of the report."""
    if x == "nan" or y == "nan":
        return target.project("nan")
    if name == "Pow":
        if isinstance(y, str):
            if isinstance(x, str):
                return target.project(F(0) if y == "-inf" else "+inf")
            if abs(x) == 1:
                return target.project(F(1))
            return target.project("+inf" if (abs(x) > 1) == (y == "+inf") else F(0))
        if isinstance(x, str):
            if y == 0:
                return target.project(F(1))
            if y < 0:
                return target.project(F(0))
            odd = y.denominator == 1 and y.numerator % 2 == 1
            return target.project("-inf" if x == "-inf" and odd else "+inf")
        if y == 0:
            return target.project(F(1))
        if x == 0:
            return target.project(F(0) if y > 0 else "nan")
        if x > 0:
            return real_power(target, x, y)
        if y.denominator != 1:
            return target.project("nan")
        magnitude = real_power(target, -x, y)
        if y.numerator % 2 == 0:
            return magnitude
        return real_power_negated(target, -x, y)
    assert name == "Powr"
    if isinstance(y, str):
        if isinstance(x, str):
            if x == "-inf":
                return target.project("nan")
            return target.project(F(0) if y == "-inf" else "+inf")
        if x < 0 or x == 1:
            return target.project("nan")
        return target.project("+inf" if (x > 1) == (y == "+inf") else F(0))
    if isinstance(x, str):
        if x == "-inf" or y == 0:
            return target.project("nan")
        return target.project("+inf" if y > 0 else F(0))
    if x > 0:
        return real_power(target, x, y)
    return target.project(F(0) if x == 0 and y > 0 else "nan")


def real_power_negated(target, x, y):
    """The projection of -(x ** y) for a positive rational x and an integral rational y."""
    if abs(y) <= 64:
        return target.project(-(x ** int(y)))
    magnitude = float(y) * math.log2(float(x))
    return target.project(-(F(2) ** 256) if magnitude > 0 else -F(1, 2 ** 256))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("producer", type=Path)
    parser.add_argument("report", type=Path)
    parser.add_argument("--first", type=int, default=3)
    parser.add_argument("--last", type=int, default=4)
    args = parser.parse_args()
    if not 3 <= args.first < args.last <= 8:
        parser.error("the small-format corpus requires 3 <= first < last <= 8")
    expected_pairs, expected_counts = expected_coverage(args.first, args.last)
    command = [str(args.producer.resolve()), str(args.first), str(args.last)]
    process = subprocess.Popen(command, stdout=subprocess.PIPE)
    digest = hashlib.sha256()
    counts = Counter()
    mismatches = []
    pairs = set()
    observations = set()
    current = None
    try:
        for raw in process.stdout:
            digest.update(raw)
            assert raw.endswith(b"\n"), "Truncated producer record."
            row = raw.decode().strip().split(",")
            if row[0] == "F":
                current = tuple(row[1:])
                assert current in expected_pairs and current not in pairs, current
                def read(start):
                    return descriptor(int(row[start]), int(row[start + 1]),
                                      row[start + 2] == "true", row[start + 3] == "true")
                source, target = read(1), read(5)
                pairs.add(current)
                continue
            assert current is not None, "Observation before descriptor."
            identity = (current, *row[:3 if row[0] == "U" else 4])
            assert identity not in observations, identity
            observations.add(identity)
            if row[0] == "U":
                name = row[2]
                assert name in UNARY_NAMES and 0 <= int(row[1]) < 2 ** source.width
                expected = unary(target, name, source.decode(int(row[1])))
                actual = list(map(int, row[3:]))
            elif row[0] == "P":
                name = row[3]
                assert name in ("Pow", "Powr") and source.width <= 4
                assert 0 <= int(row[1]) < 2 ** source.width
                assert int(row[2]) in (0, 1, 32, 63, 64, 65, 96, 127, 128, 129, 192, 255)
                expected = power_function(target, name, source.decode(int(row[1])),
                                          descriptor(8, 3, True, True).decode(int(row[2])))
                actual = list(map(int, row[4:]))
            elif row[0] == "I":
                name = row[3]
                assert name in ("Pown", "Rootn", "Compound") and source.width <= 4
                assert 0 <= int(row[1]) < 2 ** source.width and -3 <= int(row[2]) <= 3
                expected = integer_function(target, name, source.decode(int(row[1])),
                                            int(row[2]))
                actual = list(map(int, row[4:]))
            else:
                assert row[0] == "B"
                assert source.width <= 4 and 0 <= int(row[1]) < 2 ** source.width
                assert int(row[2]) in (0, 1, 32, 63, 64, 65, 96, 127, 128, 129, 192, 255)
                assert row[3] in ("true", "false")
                name = "ArcTan2Pi" if row[3] == "true" else "ArcTan2"
                expected = binary(target, row[3] == "true", source.decode(int(row[1])),
                                  descriptor(8, 3, True, True).decode(int(row[2])))
                actual = list(map(int, row[4:]))
            assert len(actual) == MODE_COUNT * 3
            counts[name] += 1
            if actual != expected and len(mismatches) < 20:
                mismatches.append({"source": [source.width, source.precision, source.signed, source.extended],
                                   "target": [target.width, target.precision, target.signed, target.extended],
                                   "input": row[:3 if row[0] == "U" else 4],
                                   "differences": [[i, a, b] for i, (a, b) in enumerate(
                                       zip(actual, expected)) if a != b]})
    except BaseException:
        process.terminate()
        process.wait()
        raise
    code = process.wait()
    coverage_complete = pairs == expected_pairs and counts == expected_counts
    report = {"document": "P3109 v4.1, 14 September 2026, unapproved",
              "clauses": ["4.10.9", "4.10.10", "4.10.11", "4.10.12", "4.10.13",
                          "4.10.15", "4.10.16"],
              "extensions": "IEEE 754-2019 9.2: exp10, exp2m1, exp10m1, log10, log2p1, log10p1, cbrt, "
                            "pow, powr, pown, rootn, compound",
              "reference": "directed MPFR plus independent Fraction projection formulas",
              "source_widths": list(range(args.first, args.last)),
              "descriptor_pairs": len(pairs), "function_inputs": dict(counts),
              "projections": sum(counts.values()) * MODE_COUNT * 3,
              "mode_count": MODE_COUNT, "saturation_count": 3,
              "coverage_complete": coverage_complete,
              "expected_function_inputs": dict(expected_counts),
              "mpfr_precisions": dict(precision_counts), "producer_exit": code,
              "first_mismatches": mismatches, "sha256": digest.hexdigest(),
              "status": "pass" if code == 0 and not mismatches and coverage_complete else "fail"}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if report["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
