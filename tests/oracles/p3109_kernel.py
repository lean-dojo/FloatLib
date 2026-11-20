"""P3109 kernel operations on encodings against the interim report on `Fraction`.

The kernel path of FloatLib evaluates the operations of P3109 Interim Report v4.1 (14 September
2026, an unapproved draft), §§4.10 to 4.13 and 4.16, on natural-number encodings. This script
computes each operation independently: it decodes the operands to exact values, applies the
operation of the report on `Fraction` with its rules for infinities and NaN, and projects the
exact result with the `Fraction` reference of `p3109_comparison.py` (the logarithmic quantum and
the scaled-fraction formulas of §§4.7.4 to 4.7.6). A square root is rounded from integer square
roots of scaled radicands, with no floating-point arithmetic. An infinite result is saturated by
the table of §4.7.5. The encodings are then compared, in every rounding mode of the comparison
(the six deterministic modes, and the three stochastic modes with every random word of zero to
three bits) and every saturation mode.

Compared: `convert`, `negate`, `abs`, `add`, `sub`, `mul`, `div`, `recip`, `copysign`, `sqrt`,
`rsqrt`, `hypot`, the ten extrema, the five comparisons, the classification queries and the two
neighbours on every code of every descriptor of three to five bits, the operations of two
operands on every pair of codes of the descriptors of three and four bits and on a seeded sample
of pairs at five bits, all of them again on seeded samples of codes with operands and
destination of different descriptors of three to eight bits, and `fma`, `faa` and `clamp` on
seeded samples of triples.

`convertbinary` is the conversion of a word of a binary interchange format into a P3109 format:
the word is decoded here from its fields, for IEEE formats and for the three encodings without an
infinity, on every word of the formats of up to nine bits and on seeded samples of binary16,
bfloat16, binary32 and binary64 with their special values.

It needs the `oracle` executable of the test workspace.
"""

import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path
import random
import subprocess

from p3109_comparison import Format, MODES, log2floor, nearest_even, pow2

SATURATIONS = ("finite", "propagate", "none")
NAN = ("nan",)
POSITIVE_INFINITY = ("inf", False)
NEGATIVE_INFINITY = ("inf", True)


class Descriptor(Format):
    """A descriptor with the decoding of every code."""

    def __init__(self, width, precision, signed, extended):
        super().__init__(width, precision, signed, extended)
        self.key = (width, precision, int(signed), int(extended))
        self.minimum_normal = pow2(1 - self.bias)
        boundary = 2 ** (width - 1)
        positive = {code: value for value, code in self.values.items()}
        self.data = {}
        for code in range(2 ** width):
            if code == self.nan:
                datum = NAN
            elif extended and code == self.infinity:
                datum = POSITIVE_INFINITY
            elif extended and signed and code == 2 ** width - 1:
                datum = NEGATIVE_INFINITY
            elif signed and code > boundary:
                datum = ("fin", -positive[code - boundary])
            else:
                datum = ("fin", positive[code])
            self.data[code] = datum
        ordered = sorted((code for code in self.data if self.data[code] != NAN),
                         key=lambda code: order_key(self.data[code]))
        self.above = {code: after for code, after in zip(ordered, ordered[1:])}
        self.below = {after: code for code, after in zip(ordered, ordered[1:])}

    def saturated(self, mode, saturation, above):
        """The code of a finite result beyond the finite range (§4.7.5)."""
        if above:
            if saturation != "none" or mode in ("zero", "down"):
                return self.maximum_code
            return self.infinity if self.extended else self.nan
        if saturation != "none" or mode in ("zero", "up"):
            return self.maximum_code + 2 ** (self.width - 1) if self.signed else 0
        return 2 ** self.width - 1 if self.signed and self.extended else self.nan

    def infinite(self, negative):
        """The codes of an infinite result in every mode and saturation mode (§4.7.5)."""
        row = []
        for _ in MODES:
            for saturation in SATURATIONS:
                if not negative:
                    if saturation != "finite" and self.extended:
                        code = self.infinity
                    else:
                        code = self.maximum_code if saturation != "none" else self.nan
                elif saturation != "finite" and self.extended and self.signed:
                    code = 2 ** self.width - 1
                elif saturation != "none":
                    code = self.maximum_code + 2 ** (self.width - 1) if self.signed else 0
                else:
                    code = self.nan
                row.append(code)
        return row

    def project(self, datum):
        if datum == NAN:
            return [self.nan] * (len(MODES) * 3)
        if datum[0] == "inf":
            return self.infinite(datum[1])
        return self.expected(datum[1])

    def project_root(self, radicand):
        """The codes of the square root of a datum, rounded once (§4.10.8)."""
        if radicand == NAN or radicand == NEGATIVE_INFINITY:
            return self.project(NAN)
        if radicand == POSITIVE_INFINITY:
            return self.infinite(False)
        value = radicand[1]
        if value < 0:
            return self.project(NAN)
        if value == 0:
            return [0] * (len(MODES) * 3)
        quantum = max(log2floor(value) // 2, 1 - self.bias) - self.precision + 1
        unit = pow2(quantum)
        scaled = value / (unit * unit)
        lower = math.isqrt(scaled.numerator // scaled.denominator)
        exact = scaled == lower * lower
        even = lower % 2 == 0 if self.precision > 1 else (
            lower == 0 or (quantum + self.bias) % 2 == 0)

        def floor_fraction(bits):
            """The floor of the fraction of the root times `2 ** bits`."""
            shifted = scaled * 4 ** bits
            return math.isqrt(shifted.numerator // shifted.denominator) - lower * 2 ** bits

        def nearest_fraction(bits):
            """The fraction of the root times `2 ** bits`, to the nearest integer, ties to even."""
            shifted = scaled * 4 ** bits
            whole = math.isqrt(shifted.numerator // shifted.denominator)
            below = whole - lower * 2 ** bits
            middle = (2 * whole + 1) ** 2
            return below + (4 * shifted > middle or (4 * shifted == middle and below % 2 == 1))

        row = []
        for mode, bits, word in MODES:
            if exact or mode in ("zero", "down"):
                up = False
            elif mode == "up":
                up = True
            elif mode == "away":
                up = 4 * scaled >= (2 * lower + 1) ** 2
            elif mode == "even":
                middle = (2 * lower + 1) ** 2
                up = 4 * scaled > middle or (4 * scaled == middle and not even)
            elif mode == "odd":
                up = even
            elif mode == "A":
                up = floor_fraction(bits) + word >= 2 ** bits
            elif mode == "B":
                up = floor_fraction(bits + 1) + 2 * word + 1 >= 2 ** (bits + 1)
            else:
                up = nearest_fraction(bits) + word >= 2 ** bits
            rounded = (lower + up) * unit
            for saturation in SATURATIONS:
                if rounded > self.maximum:
                    row.append(self.saturated(mode, saturation, True))
                else:
                    row.append(self.values[rounded])
        return row


def order_key(datum):
    if datum[0] == "inf":
        return (-1, 0) if datum[1] else (1, 0)
    return (0, datum[1])


def less(left, right):
    return left != NAN and right != NAN and order_key(left) < order_key(right)


def equal(left, right):
    return left != NAN and right != NAN and order_key(left) == order_key(right)


def negate(datum):
    if datum == NAN:
        return NAN
    if datum[0] == "inf":
        return ("inf", not datum[1])
    return ("fin", -datum[1])


def magnitude(datum):
    if datum == NAN:
        return NAN
    if datum[0] == "inf":
        return POSITIVE_INFINITY
    return ("fin", abs(datum[1]))


def add(left, right):
    if NAN in (left, right):
        return NAN
    if left[0] == "inf" and right[0] == "inf":
        return left if left == right else NAN
    if left[0] == "inf":
        return left
    if right[0] == "inf":
        return right
    return ("fin", left[1] + right[1])


def multiply(left, right):
    if NAN in (left, right):
        return NAN
    if left[0] == "inf" and right[0] == "inf":
        return ("inf", left[1] != right[1])
    for infinite, finite in ((left, right), (right, left)):
        if infinite[0] == "inf":
            return NAN if finite[1] == 0 else ("inf", infinite[1] != (finite[1] < 0))
    return ("fin", left[1] * right[1])


def divide(left, right):
    if NAN in (left, right):
        return NAN
    if right[0] == "inf":
        return NAN if left[0] == "inf" else ("fin", F(0))
    if right[1] == 0:
        return NAN
    if left[0] == "inf":
        return ("inf", left[1] != (right[1] < 0))
    return ("fin", left[1] / right[1])


def copy_sign(value, sign):
    if NAN in (value, sign):
        return NAN
    negative = sign == NEGATIVE_INFINITY or (sign[0] == "fin" and sign[1] < 0)
    return negate(magnitude(value)) if negative else magnitude(value)


def reciprocal_root_radicand(datum):
    if datum in (NAN, NEGATIVE_INFINITY):
        return NAN
    if datum == POSITIVE_INFINITY:
        return ("fin", F(0))
    return NAN if datum[1] <= 0 else ("fin", 1 / datum[1])


def hypotenuse_radicand(left, right):
    if NAN in (left, right):
        return NAN
    if "inf" in (left[0], right[0]):
        return POSITIVE_INFINITY
    return ("fin", left[1] * left[1] + right[1] * right[1])


def minimum(left, right):
    if NAN in (left, right):
        return NAN
    return left if less(left, right) else right


def maximum(left, right):
    if NAN in (left, right):
        return NAN
    return right if less(left, right) else left


def by_magnitude(order, smaller):
    def extremum(left, right):
        if NAN in (left, right):
            return NAN
        if less(magnitude(left), magnitude(right)):
            return left if smaller else right
        if less(magnitude(right), magnitude(left)):
            return right if smaller else left
        return order(left, right)
    return extremum


def number(extremum):
    def variant(left, right):
        if left == NAN:
            return right
        if right == NAN:
            return left
        return extremum(left, right)
    return variant


def finite(extremum):
    def variant(left, right):
        if left[0] == "fin" and right[0] == "inf":
            return left
        if left[0] == "inf" and right[0] == "fin":
            return right
        return extremum(left, right)
    return variant


def clamp(value, lower, upper):
    if less(upper, lower):
        return NAN
    return minimum(maximum(value, lower), upper)


BINARY = {
    "add": add,
    "sub": lambda left, right: add(left, negate(right)),
    "mul": multiply,
    "div": divide,
    "copysign": copy_sign,
    "min": minimum,
    "max": maximum,
    "minnum": number(minimum),
    "maxnum": number(maximum),
    "minmag": by_magnitude(minimum, True),
    "maxmag": by_magnitude(maximum, False),
    "minmagnum": number(by_magnitude(minimum, True)),
    "maxmagnum": number(by_magnitude(maximum, False)),
    "minfinite": finite(number(minimum)),
    "maxfinite": finite(number(maximum)),
}
UNARY = {
    "convert": lambda datum: datum,
    "negate": negate,
    "abs": magnitude,
    "recip": lambda datum: divide(("fin", F(1)), datum),
}
TERNARY = {
    "fma": lambda left, right, addend: add(multiply(left, right), addend),
    "faa": lambda left, middle, right: add(add(left, middle), right),
    "clamp": clamp,
}
COMPARISONS = {
    "less": less,
    "equal": equal,
    "lessequal": lambda left, right: less(left, right) or equal(left, right),
}
QUERIES = ("iszero", "isnan", "isinf", "isfinite", "issignminus", "isone", "isnormal",
           "issubnormal", "nextup", "nextdown")


def query(name, descriptor, code):
    datum = descriptor.data[code]
    is_finite = datum[0] == "fin"
    if name == "iszero":
        return int(is_finite and datum[1] == 0)
    if name == "isnan":
        return int(datum == NAN)
    if name == "isinf":
        return int(datum[0] == "inf")
    if name == "isfinite":
        return int(is_finite)
    if name == "issignminus":
        return int(datum == NEGATIVE_INFINITY or (is_finite and datum[1] < 0))
    if name == "isone":
        return int(is_finite and datum[1] == 1)
    if name == "isnormal":
        return int(is_finite and abs(datum[1]) >= descriptor.minimum_normal)
    if name == "issubnormal":
        return int(is_finite and 0 < abs(datum[1]) < descriptor.minimum_normal)
    if datum == NAN:
        return descriptor.nan
    neighbours = descriptor.above if name == "nextup" else descriptor.below
    return neighbours.get(code, descriptor.nan)


class Binary:
    """A binary interchange format: IEEE (0), a NaN at the largest pattern (1), a NaN at the
    negative zero with the bias one more (2), or finite only (3)."""

    def __init__(self, exp_width, frac_width, encoding):
        self.exp_width, self.frac_width, self.encoding = exp_width, frac_width, encoding
        self.width = exp_width + frac_width + 1
        self.key = (exp_width, frac_width, encoding, 0)
        self.bias = 2 ** (exp_width - 1) - 1 + (encoding == 2)

    def datum(self, word):
        sign = word >> (self.width - 1)
        fields = word & (2 ** (self.width - 1) - 1)
        exponent, fraction = fields >> self.frac_width, fields & (2 ** self.frac_width - 1)
        if self.encoding == 0 and exponent == 2 ** self.exp_width - 1:
            return ("inf", bool(sign)) if fraction == 0 else NAN
        if self.encoding == 1 and fields == 2 ** (self.width - 1) - 1:
            return NAN
        if self.encoding == 2 and sign == 1 and fields == 0:
            return NAN
        significand = fraction if exponent == 0 else 2 ** self.frac_width + fraction
        value = significand * pow2(max(exponent, 1) - self.bias - self.frac_width)
        return ("fin", -value if sign else value)

    def special_words(self):
        """Zeros, the least and the largest fields, the infinities and NaNs of an IEEE format."""
        top = 2 ** (self.width - 1)
        fields = [0, 1, 2 ** self.frac_width - 1, 2 ** self.frac_width, top - 1, top - 2,
                  (2 ** self.exp_width - 1) << self.frac_width,
                  ((2 ** self.exp_width - 1) << self.frac_width) + 1,
                  ((2 ** self.exp_width - 2) << self.frac_width) + 2 ** self.frac_width - 1,
                  (2 ** (self.exp_width - 1) - 1) << self.frac_width]
        return [sign * top + field for sign in (0, 1) for field in fields]


def expected(name, formats, target, codes):
    if name == "convertbinary":
        return target.project(formats[0].datum(codes[0]))
    data = [descriptor.data[code] for descriptor, code in zip(formats, codes)]
    if name in UNARY:
        return target.project(UNARY[name](data[0]))
    if name in BINARY:
        return target.project(BINARY[name](data[0], data[1]))
    if name in TERNARY:
        return target.project(TERNARY[name](*data))
    if name == "sqrt":
        return target.project_root(data[0])
    if name == "rsqrt":
        return target.project_root(reciprocal_root_radicand(data[0]))
    if name == "hypot":
        return target.project_root(hypotenuse_radicand(data[0], data[1]))
    if name in COMPARISONS:
        return [int(COMPARISONS[name](data[0], data[1]))]
    return [query(name, formats[0], codes[0])]


def request(name, formats, target, codes):
    fields = []
    for descriptor in list(formats) + [formats[-1]] * (3 - len(formats)) + [target]:
        fields += descriptor.key
    fields += list(codes) + [0] * (3 - len(codes))
    return name + " " + " ".join(format(field, "x") for field in fields)


def descriptors(widths):
    result = []
    for width in widths:
        for signed in (True, False):
            for precision in range(1, width if signed else width + 1):
                for extended in (False, True):
                    result.append(Descriptor(width, precision, signed, extended))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=300)
    parser.add_argument("--seed", type=int, default=20261119)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    small = descriptors((3, 4, 5))
    wide = descriptors((6, 8))
    unary = list(UNARY) + ["sqrt", "rsqrt"] + list(QUERIES)
    binary = list(BINARY) + ["hypot"] + list(COMPARISONS)
    cases = []
    for descriptor in small:
        codes = range(2 ** descriptor.width)
        for name in unary:
            cases += [(name, (descriptor,), descriptor, (code,)) for code in codes]
        pairs = [(a, b) for a in codes for b in codes]
        if descriptor.width == 5:
            pairs = rng.sample(pairs, 48)
        for name in binary:
            cases += [(name, (descriptor, descriptor), descriptor, pair) for pair in pairs]
        for name in TERNARY:
            cases += [(name, (descriptor,) * 3, descriptor,
                       tuple(rng.randrange(2 ** descriptor.width) for _ in range(3)))
                      for _ in range(64)]
    everything = small + wide
    for _ in range(args.samples):
        formats = [rng.choice(everything) for _ in range(3)]
        target = rng.choice(everything)
        codes = tuple(rng.randrange(2 ** descriptor.width) for descriptor in formats)
        for name in unary:
            cases.append((name, formats[:1], target, codes[:1]))
        for name in binary:
            cases.append((name, formats[:2], target, codes[:2]))
        for name in TERNARY:
            cases.append((name, formats, target, codes))
    sources = [Binary(e, f, 0) for e, f in ((2, 1), (3, 2), (4, 3), (3, 5), (5, 3))] + [
        Binary(4, 3, 1), Binary(4, 3, 2), Binary(5, 2, 2), Binary(3, 4, 3), Binary(2, 2, 1)]
    targets = rng.sample(everything, 24)
    for source in sources:
        for word in range(2 ** source.width):
            for target in rng.sample(targets, 6):
                cases.append(("convertbinary", (source,), target, (word,)))
    for source in (Binary(5, 10, 0), Binary(8, 7, 0), Binary(8, 23, 0), Binary(11, 52, 0),
                   Binary(8, 23, 1), Binary(11, 52, 2), Binary(8, 23, 3)):
        words = source.special_words() + [rng.randrange(2 ** source.width)
                                          for _ in range(args.samples)]
        # Words near one, where a destination of a few bits has its finite values.
        one = (2 ** (source.exp_width - 1) - 1 + (source.encoding == 2)) << source.frac_width
        words += [(rng.randrange(2) << (source.width - 1)) +
                  one + rng.randrange(-(8 << source.frac_width), 8 << source.frac_width)
                  for _ in range(args.samples)]
        for word in words:
            cases.append(("convertbinary", (source,), rng.choice(everything), (word,)))
    lines = [request(*case) for case in cases]
    done = subprocess.run([args.oracle, "p3109-kernel"], input="\n".join(lines) + "\n",
                          capture_output=True, text=True)
    if done.returncode:
        raise RuntimeError(f"oracle exited {done.returncode}: {done.stderr[:500]}")
    answers = done.stdout.splitlines()
    if len(answers) != len(lines):
        raise RuntimeError(f"{len(answers)} answers for {len(lines)} requests")
    counts = {}
    for case, answer in zip(cases, answers, strict=True):
        name, formats, target, codes = case
        want = expected(name, formats, target, codes)
        got = [int(field) for field in answer.split()]
        count = counts.setdefault(name, {"requests": 0, "results": 0, "mismatches": 0,
                                         "first": []})
        count["requests"] += 1
        count["results"] += len(want)
        if want != got:
            count["mismatches"] += 1
            if len(count["first"]) < 5:
                count["first"].append({
                    "operands": [descriptor.key for descriptor in formats],
                    "destination": target.key, "codes": list(codes),
                    "differences": [[index, a, b] for index, (a, b)
                                    in enumerate(zip(got, want)) if a != b][:6]})
    mismatches = sum(count["mismatches"] for count in counts.values())
    result = {
        "document": "P3109 Interim Report v4.1, 14 September 2026, unapproved draft",
        "reference": "independent Python Fraction: the operations of §§4.10 to 4.13 and 4.16, "
                     "the projection of p3109_comparison.py, integer square roots",
        "seed": args.seed, "samples": args.samples,
        "descriptors": {"exhaustive": len(small), "sampled": len(everything)},
        "modes_per_result": len(MODES), "saturations_per_mode": len(SATURATIONS),
        "operations": {name: {key: value for key, value in count.items() if key != "first"}
                       for name, count in counts.items()},
        "requests": sum(count["requests"] for count in counts.values()),
        "results": sum(count["results"] for count in counts.values()),
        "mismatches": mismatches,
        "first_mismatches": {name: count["first"] for name, count in counts.items()
                             if count["first"]},
        "status": "pass" if mismatches == 0 else "fail",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    summary = {key: value for key, value in result.items() if key != "operations"}
    print(json.dumps(summary, indent=2))
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
