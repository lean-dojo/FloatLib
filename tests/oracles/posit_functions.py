"""Independent Posit Standard (2022) §4.1, §5 function and quire oracle.

The decoder reads regime/exponent/fraction fields. Rounding compares against
the standard's appended-one (n+1)-bit cuts, not arithmetic midpoints.
Rational operations use Fraction. Elementary results are enclosed with MPFR
directed rounding; a result is accepted only when both bounds round alike.
"""

import argparse
from bisect import bisect_left
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path

import gmpy2 as g


UNARY = [
    "negate", "abs", "sign", "nearestInt", "ceil", "floor", "next", "prior",
    "sqrt", "rSqrt", "exp", "expm1", "exp2", "exp2Minus1",
    "exp10", "exp10Minus1", "log", "logp1", "log2", "log2Plus1",
    "log10", "log10Plus1", "sin", "sinPi", "cos", "cosPi", "tan", "tanPi",
    "arcSin", "arcSinPi", "arcCos", "arcCosPi", "arcTan", "arcTanPi",
    "sinH", "cosH", "tanH", "arcSinH", "arcCosH", "arcTanH",
]
BINARY = ["hypot", "pow", "arcTan2", "arcTan2Pi"]
PRECISIONS = (192, 384, 768, 1536)
precision_counts = Counter()


@lru_cache(None)
def decode(width, word):
    """Decode a standard es=2 word, using two's-complement sign symmetry."""
    mask = 1 << (width - 1)
    if word == mask:
        return None
    if word == 0:
        return Fraction(0)
    if word > mask:
        return -decode(width, (1 << width) - word)
    position = width - 2
    regime_bit = (word >> position) & 1
    run = 0
    while position >= 0 and ((word >> position) & 1) == regime_bit:
        run += 1
        position -= 1
    regime = run - 1 if regime_bit else -run
    position -= 1  # Skip the terminator, if present.
    exponent = 0
    for _ in range(2):
        exponent = 2 * exponent + (((word >> position) & 1) if position >= 0 else 0)
        position -= 1
    fraction_bits = max(0, position + 1)
    significand = Fraction((1 << fraction_bits) + (word & ((1 << fraction_bits) - 1)),
                           1 << fraction_bits)
    power = 4 * regime + exponent
    return significand * (Fraction(2) ** power)


def rational(value):
    return g.mpq(value.numerator, value.denominator)


@lru_cache(None)
def lattice(width):
    mask = 1 << (width - 1)
    values = [rational(decode(width, word)) for word in range(mask)]
    cuts = [rational(decode(width + 1, 2 * word + 1)) for word in range(1, mask - 1)]
    return values, cuts


def rounded(width, value):
    if value is None:
        return 1 << (width - 1)
    if isinstance(value, Fraction):
        value = rational(value)
    if g.is_nan(value):
        raise ValueError("Unexpected MPFR NaN outside an adjudicated real-domain case")
    if value < 0:
        return (-rounded(width, -value)) % (1 << width)
    if value == 0:
        return 0
    values, cuts = lattice(width)
    if value <= values[1]:
        return 1
    if value >= values[-1]:
        return len(values) - 1
    upper = bisect_left(values, value)
    if value == values[upper]:
        return upper
    lower = upper - 1
    cut = cuts[lower - 1]
    return lower if value < cut or (value == cut and lower % 2 == 0) else upper


def directed(precision, mode, function):
    with g.context(precision=precision, round=mode):
        return function()


def enclosure(precision, function):
    return (directed(precision, g.RoundDown, function),
            directed(precision, g.RoundUp, function))


def quotient(precision, numerator, denominator):
    if denominator[0] <= 0 <= denominator[1]:
        raise ArithmeticError("Interval division crosses zero")
    pairs = list(itertools.product(numerator, denominator))
    return (min(directed(precision, g.RoundDown, lambda a=a, b=b: a / b)
                for a, b in pairs),
            max(directed(precision, g.RoundUp, lambda a=a, b=b: a / b)
                for a, b in pairs))


def trig_pi(precision, name, value):
    # Reduction modulo two is exact before multiplying by the pi enclosure.
    reduced = rational(value % 2)
    argument = enclosure(precision, lambda: g.mpfr(reduced) * g.const_pi())
    midpoint = directed(precision, g.RoundToNearest,
                        lambda: (argument[0] + argument[1]) / 2)
    radius = directed(precision, g.RoundUp,
                      lambda: max(midpoint - argument[0], argument[1] - midpoint))

    def lipschitz(function):
        return (directed(precision, g.RoundDown, lambda: function(midpoint) - radius),
                directed(precision, g.RoundUp, lambda: function(midpoint) + radius))

    if name == "sinPi":
        return lipschitz(g.sin)
    if name == "cosPi":
        return lipschitz(g.cos)
    return quotient(precision, lipschitz(g.sin), lipschitz(g.cos))


def elementary_bounds(precision, name, x, y=None, integer=None):
    # All source rationals here are small dyadics and convert exactly at 192 bits.
    a = directed(precision, g.RoundToNearest, lambda: g.mpfr(rational(x)))
    b = None if y is None else directed(
        precision, g.RoundToNearest, lambda: g.mpfr(rational(y)))
    simple = {
        "sqrt": g.sqrt, "exp": g.exp, "expm1": g.expm1,
        "exp2": g.exp2, "exp10": g.exp10, "log": g.log, "log2": g.log2,
        "log10": g.log10, "sin": g.sin, "cos": g.cos, "tan": g.tan,
        "arcSin": g.asin, "arcCos": g.acos, "arcTan": g.atan,
        "sinH": g.sinh, "cosH": g.cosh, "tanH": g.tanh,
        "arcSinH": g.asinh, "arcCosH": g.acosh, "arcTanH": g.atanh,
    }
    if name in simple:
        return enclosure(precision, lambda: simple[name](a))
    if name == "rSqrt":
        return quotient(precision, (g.mpfr(1), g.mpfr(1)),
                        enclosure(precision, lambda: g.sqrt(a)))
    if name in ("exp2Minus1", "exp10Minus1"):
        function = g.exp2 if name == "exp2Minus1" else g.exp10
        return enclosure(precision, lambda: function(a) - 1)
    if name in ("logp1", "log2Plus1", "log10Plus1"):
        function = {"logp1": g.log, "log2Plus1": g.log2, "log10Plus1": g.log10}[name]
        # x+1 remains exactly representable in the smallest configured precision.
        return enclosure(precision, lambda: function(g.mpfr(rational(x + 1))))
    if name in ("sinPi", "cosPi", "tanPi"):
        return trig_pi(precision, name, x)
    if name in ("arcSinPi", "arcCosPi", "arcTanPi", "arcTan2Pi"):
        if name == "arcTan2Pi":
            numerator = enclosure(precision, lambda: g.atan2(b, a))
        else:
            function = {"arcSinPi": g.asin, "arcCosPi": g.acos, "arcTanPi": g.atan}[name]
            numerator = enclosure(precision, lambda: function(a))
        return quotient(precision, numerator, enclosure(precision, g.const_pi))
    if name == "arcTan2":
        return enclosure(precision, lambda: g.atan2(b, a))
    if name == "hypot":
        return enclosure(precision, lambda: g.hypot(a, b))
    if name == "pow":
        return enclosure(precision, lambda: a ** b)
    if name == "rootn":
        result = enclosure(precision, lambda: g.rootn(a, abs(integer)))
        return result if integer > 0 else quotient(
            precision, (g.mpfr(1), g.mpfr(1)), result)
    raise ValueError(name)


def real_result(width, name, x, y=None, integer=None):
    for precision in PRECISIONS:
        try:
            lower, upper = elementary_bounds(precision, name, x, y, integer)
        except ArithmeticError:
            continue
        if lower > upper:
            raise AssertionError("Reversed MPFR enclosure")
        first, last = rounded(width, lower), rounded(width, upper)
        if first == last:
            precision_counts[precision] += 1
            return first
    raise ArithmeticError(f"Unresolved rounding: {width=} {name=} {x=} {y=} {integer=}")


def unary(width, word, name):
    modulus, nar = 1 << width, 1 << (width - 1)
    if name in ("next", "prior"):
        return (word + (1 if name == "next" else -1)) % modulus
    x = decode(width, word)
    if x is None:
        return nar
    if name == "negate":
        return (-word) % modulus
    if name == "abs":
        return rounded(width, abs(x))
    if name == "sign":
        return rounded(width, Fraction((x > 0) - (x < 0)))
    if name in ("nearestInt", "ceil", "floor"):
        integer = {"nearestInt": round, "ceil": math.ceil, "floor": math.floor}[name](x)
        return rounded(width, Fraction(integer))
    if ((name == "sqrt" and x < 0) or (name == "rSqrt" and x <= 0)
            or (name in ("log", "log2", "log10") and x <= 0)
            or (name in ("logp1", "log2Plus1", "log10Plus1") and x <= -1)
            or (name in ("arcSin", "arcSinPi", "arcCos", "arcCosPi") and abs(x) > 1)
            or (name == "arcCosH" and x < 1) or (name == "arcTanH" and abs(x) >= 1)):
        return nar
    if name in ("sinPi", "cosPi", "tanPi") and (2 * x).denominator == 1:
        phase = int(2 * x) % 4
        if name == "tanPi" and phase % 2:
            return nar
        exact = {"sinPi": (0, 1, 0, -1), "cosPi": (1, 0, -1, 0),
                 "tanPi": (0, 0, 0, 0)}[name][phase]
        return rounded(width, Fraction(exact))
    if name in ("arcSinPi", "arcCosPi", "arcTanPi") and x in (-1, 0, 1):
        index = int(x) + 1
        exact = {"arcSinPi": (Fraction(-1, 2), Fraction(0), Fraction(1, 2)),
                 "arcCosPi": (Fraction(1), Fraction(1, 2), Fraction(0)),
                 "arcTanPi": (Fraction(-1, 4), Fraction(0), Fraction(1, 4))}[name][index]
        return rounded(width, exact)
    return real_result(width, name, x)


def binary(width, a, b, name):
    x, y, nar = decode(width, a), decode(width, b), 1 << (width - 1)
    if x is None or y is None:
        return nar
    if name == "pow":
        if (x == 0 and y <= 0) or (x < 0 and y.denominator != 1):
            return nar
    if name in ("arcTan2", "arcTan2Pi"):
        if x == 0 and y == 0:
            return nar
        if name == "arcTan2Pi" and (x == 0 or y == 0 or abs(x) == abs(y)):
            if y == 0:
                exact = Fraction(1 if x < 0 else 0)
            elif x == 0:
                exact = Fraction(1 if y > 0 else -1, 2)
            else:
                exact = Fraction((1 if x > 0 else 3) * (1 if y > 0 else -1), 4)
            return rounded(width, exact)
    return real_result(width, name, x, y)


def integer_operation(width, a, exponent, name):
    x, nar = decode(width, a), 1 << (width - 1)
    if x is None:
        return nar
    if name == "compound":
        return nar if x == -1 and exponent < 0 else rounded(width, (1 + x) ** exponent)
    if exponent == 0 or (x < 0 and exponent % 2 == 0) or (x == 0 and exponent < 0):
        return nar
    return real_result(width, name, x, integer=exponent)


def quire_words(width):
    midpoint = 1 << (16 * width - 1)
    return [0, 1, midpoint - 1, midpoint, midpoint + 1, 2 * midpoint - 2,
            2 * midpoint - 1, midpoint // 2, midpoint + midpoint // 2]


def quire_decode(width, word):
    midpoint = 1 << (16 * width - 1)
    if word == midpoint:
        return None
    coefficient = word if word < midpoint else word - 2 * midpoint
    return Fraction(coefficient) * Fraction(2) ** (16 - 8 * width)


def quire_encode(width, value):
    midpoint = 1 << (16 * width - 1)
    if value is None:
        return midpoint
    coefficient = value / (Fraction(2) ** (16 - 8 * width))
    if coefficient.denominator != 1:
        raise AssertionError("A posit or exact posit product failed quire alignment")
    integer = coefficient.numerator
    return integer % (2 * midpoint) if -midpoint < integer < midpoint else midpoint


def expected_rows(kind):
    """Generate every expected input in the producer's exact order."""
    maximum = {"T": 5, "B": 6}.get(kind, 8)
    for width in range(2, maximum + 1):
        words = range(1 << width)
        if kind != "Q":
            for a in words:
                if kind == "U":
                    yield ["U", width, a], UNARY, [unary(width, a, op) for op in UNARY]
                elif kind == "B":
                    for b in words:
                        yield ["B", width, a, b], BINARY, [
                            binary(width, a, b, op) for op in BINARY]
                elif kind == "T":
                    for b in words:
                        for c in words:
                            inputs = [decode(width, w) for w in (a, b, c)]
                            exact = None if None in inputs else math.prod(inputs)
                            yield ["T", width, a, b, c], ["fMM"], [rounded(width, exact)]
                elif kind == "I":
                    for exponent in range(-5, 6):
                        names = ["compound", "rootn"]
                        yield ["I", width, a, exponent], names, [
                            integer_operation(width, a, exponent, op) for op in names]
            continue
        for a in words:
            yield ["P", width, a], ["pToQ"], [quire_encode(width, decode(width, a))]
        for qw in quire_words(width):
            q = quire_decode(width, qw)
            yield ["Q", width, qw], ["qNegate", "qAbs", "qToP"], [
                quire_encode(width, None if q is None else -q),
                quire_encode(width, None if q is None else abs(q)), rounded(width, q)]
            for rw in quire_words(width):
                r = quire_decode(width, rw)
                yield ["QQ", width, qw, rw], ["qAddQ", "qSubQ"], [
                    quire_encode(width, None if q is None or r is None else q + sign * r)
                    for sign in (1, -1)]
            for a in words:
                x = decode(width, a)
                yield ["QP", width, qw, a], ["qAddP", "qSubP"], [
                    quire_encode(width, None if q is None or x is None else q + sign * x)
                    for sign in (1, -1)]
                if width <= 6:
                    for b in words:
                        y = decode(width, b)
                        yield ["QPP", width, qw, a, b], ["qMulAdd", "qMulSub"], [
                            quire_encode(width, None if None in (q, x, y) else q + sign * x * y)
                            for sign in (1, -1)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("kind", choices=["U", "B", "T", "I", "Q"])
    parser.add_argument("observations", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    counts, mismatches, digest = Counter(), [], hashlib.sha256()
    with args.observations.open("rb") as stream:
        for prefix, names, expected in expected_rows(args.kind):
            raw = stream.readline()
            digest.update(raw)
            row = raw.decode().strip().split(",")
            if row[:len(prefix)] != list(map(str, prefix)):
                raise ValueError(f"Missing, duplicate or reordered input: expected {prefix}, got {row}")
            actual = list(map(int, row[len(prefix):]))
            if len(actual) != len(expected):
                raise ValueError(f"Wrong number of outputs at {prefix}")
            for name, observed, reference in zip(names, actual, expected):
                counts[name] += 1
                if observed != reference:
                    if len(mismatches) < 30:
                        mismatches.append({"input": prefix, "operation": name,
                                           "actual": observed, "expected": reference})
                    counts["mismatches"] += 1
        if stream.read(1):
            raise ValueError("Unexpected extra observation")
    result = {
        "status": "fail" if mismatches else "pass",
        "document": "Posit Standard (2022), §§3.3–3.4, 4.1, 5.1–5.8, 5.11",
        "reference": f"Python Fraction; gmpy2 {g.version()}, {g.mpfr_version()}",
        "kind": args.kind, "cases": dict(counts),
        "mpfr_precision_counts": dict(precision_counts),
        "observations_sha256": digest.hexdigest(), "first_mismatches": mismatches,
        "limitations": [
            "Standard es=2 only; this test does not establish a theorem.",
            "Unary and integer inputs exhaust posit widths 2–8; integers range from -5 to 5.",
            "Binary inputs exhaust widths 2–6; triple products exhaust widths 2–5.",
            "Quire tests use nine boundary words, every posit through width 8, and pairs through 6.",
            "Every MPFR enclosure must resolve rounding; unresolved cases fail closed.",
        ],
    }
    args.result.parent.mkdir(parents=True, exist_ok=True)
    args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
