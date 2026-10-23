#!/usr/bin/env python3
"""Generate the hard-case corpus for the transcendental comparison.

Writes `tests/oracles/data/transcendental-hard-cases.tsv`. Each data row is

    tier  set  format  operations  arguments  note

with comma-separated operations and argument encodings (hexadecimal). The emitter evaluates
`trig-cf` rows with both signs and both neighbouring encodings; other rows as written. Rows in the
`slow` tier run only with `transcendental_compare.sh --slow`.

Sets:

* `trig-cf`: for every binade 2^e with e >= -1 of binary16, bfloat16, binary32, binary64 and
  binary128, the significand m whose x = m * 2^(e - fracWidth) is closest to a multiple of pi/2
  among convergent and semiconvergent multiples of the continued fraction of frac(2^E * 2/pi).
  These are hard cases for argument reduction, not certified worst cases.
* `named`: published and previously misrounded inputs, stored by exact encoding.
* `boundary`: for exp, log, sinh, cosh and tanh, the overflow and underflow thresholds +-4 ulps,
  1 +- k ulps, 1/2 +- 1 ulp, the tanh saturation threshold and its binade, tiny arguments whose
  exp lies within x^2 of a rounding midpoint, and the arguments where the first Taylor
  correction of sin, sinh, tanh, cos and cosh crosses half an ulp.

Encodings are chosen by integer arithmetic: pi comes from Machin's formula, 2/pi from pi by
integer division and ln 2 from the series of 2 atanh(1/3), each a guarded integer approximation,
and continued-fraction candidates are ranked by their integer distances. Only the note column is
a rounded float.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

GENERATOR_VERSION = 1
# Fractional bits of 2/pi: binary128's largest binade needs E + K = 16271 + 539 bits plus guard.
TWO_OVER_PI_BITS = 17600
# Continued-fraction window: K = 3p + 200 bits of frac(2^E * 2/pi).
WINDOW_EXTRA_BITS = 200
# Semiconvergent search: multipliers t from max(1, 2^(p-1) // q) over this many values, and
# offsets s * q_previous for s in this range.
MULTIPLIER_COUNT = 3
OFFSET_RANGE = range(-2, 3)
# Bits of the distance computation beyond the significand width.
DISTANCE_EXTRA_BITS = 400
# Binades of binary128 kept in the default tier: every 64th, the edges, and the binades where
# the earlier fixed-precision reduction failed.
BINARY128_DEFAULT_STRIDE = 64
BINARY128_DEFAULT_RANGES = ((-1, 63), (3990, 4110), (16320, 16383))


@dataclass(frozen=True)
class Format:
    name: str
    exponent_bits: int
    fraction_bits: int

    @property
    def bias(self) -> int:
        return (1 << (self.exponent_bits - 1)) - 1

    @property
    def precision(self) -> int:
        return self.fraction_bits + 1

    @property
    def emax(self) -> int:
        return (1 << self.exponent_bits) - 2 - self.bias

    @property
    def emin(self) -> int:
        return 1 - self.bias

    @property
    def min_subnormal_exponent(self) -> int:
        return self.emin - self.fraction_bits

    @property
    def width(self) -> int:
        return 1 + self.exponent_bits + self.fraction_bits

    @property
    def sign_bit(self) -> int:
        return 1 << (self.width - 1)

    def hex(self, bits: int) -> str:
        return f"0x{bits:0{(self.width + 3) // 4}x}"

    def encode(self, significand: int, exponent: int) -> int:
        """Encoding of the exactly representable positive value significand * 2^exponent."""
        if significand <= 0:
            raise ValueError("positive values only")
        while significand % 2 == 0:
            significand //= 2
            exponent += 1
        leading = exponent + significand.bit_length() - 1
        if leading > self.emax:
            raise ValueError("value overflows the format")
        if leading < self.emin:
            quantum = self.min_subnormal_exponent
            field = 0
        else:
            quantum = leading - self.fraction_bits
            field = leading + self.bias
        if exponent < quantum:
            raise ValueError("value is not representable")
        scaled = significand << (exponent - quantum)
        if field:
            scaled -= 1 << self.fraction_bits
        return (field << self.fraction_bits) | scaled


FORMATS = {
    fmt.name: fmt
    for fmt in (
        Format("binary16", 5, 10),
        Format("bfloat16", 8, 7),
        Format("binary32", 8, 23),
        Format("binary64", 11, 52),
        Format("binary128", 15, 112),
        Format("ieee31_23", 31, 23),
    )
}
TRIG_FORMATS = ("binary16", "bfloat16", "binary32", "binary64", "binary128")


def arctan_inverse(n: int, bits: int) -> int:
    """floor-ish atan(1/n) * 2^bits, accurate to a few units, by the alternating series."""
    guard = 32
    one = 1 << (bits + guard)
    term = one // n
    square = n * n
    total = 0
    k = 1
    sign = 1
    while term:
        total += sign * (term // k)
        term //= square
        k += 2
        sign = -sign
    return total >> guard


def pi_scaled(bits: int) -> int:
    """pi * 2^bits from Machin's formula, within a few units."""
    return 16 * arctan_inverse(5, bits) - 4 * arctan_inverse(239, bits)


PI_GUARD = 64
PI = pi_scaled(TWO_OVER_PI_BITS + PI_GUARD)
# floor(2/pi * 2^TWO_OVER_PI_BITS), up to the few-unit error of PI shifted away by the guard.
TWO_OVER_PI = (1 << (2 * (TWO_OVER_PI_BITS + PI_GUARD) + 1)) // PI >> PI_GUARD


def fraction_bits_of_two_over_pi(exponent: int, window: int) -> int:
    """floor(frac(2^exponent * 2/pi) * 2^window)."""
    shift = TWO_OVER_PI_BITS - exponent - window
    if shift < 8:
        raise ValueError("TWO_OVER_PI_BITS is too small for this binade")
    return (TWO_OVER_PI >> shift) % (1 << window)


def convergent_denominators(numerator: int, denominator: int, bound: int) -> list[int]:
    result = []
    q_previous, q = 1, 0
    n, d = numerator, denominator
    while d and q <= bound:
        quotient = n // d
        n, d = d, n - quotient * d
        q_previous, q = q, quotient * q + q_previous
        result.append(q)
    return result


def distance_to_quarter_turns(significand: int, exponent: int, bits: int) -> int:
    """|m * 2^E * 2/pi - nearest integer| * 2^bits, from the truncated 2/pi."""
    alpha = fraction_bits_of_two_over_pi(exponent, bits)
    value = significand * alpha % (1 << bits)
    return min(value, (1 << bits) - value)


def best_in_binade(fmt: Format, binade: int) -> tuple[int, float]:
    """The candidate significand of binade 2^binade closest to a multiple of pi/2, and
    log2 |x mod pi/2| for the note."""
    exponent = binade - fmt.fraction_bits
    low, high = 1 << fmt.fraction_bits, 1 << fmt.precision
    window = 3 * fmt.precision + WINDOW_EXTRA_BITS
    alpha = fraction_bits_of_two_over_pi(exponent, window)
    denominators = [q for q in convergent_denominators(alpha, 1 << window, high) if 0 < q < high]
    candidates: set[int] = set()
    for index, q in enumerate(denominators):
        q_previous = denominators[index - 1] if index > 0 else 0
        first = max(1, low // q)
        for multiplier in range(first, first + MULTIPLIER_COUNT):
            for offset in OFFSET_RANGE:
                m = multiplier * q + offset * q_previous
                if low <= m < high:
                    candidates.add(m)
            m = q + multiplier * q_previous if q_previous else q
            if low <= m < high:
                candidates.add(m)
    # Every candidate has `precision` bits, so all distances share the scale 2^-bits and compare
    # exactly as integers.
    bits = DISTANCE_EXTRA_BITS + fmt.precision
    best: tuple[int, int] | None = None
    for m in sorted(candidates):
        distance = distance_to_quarter_turns(m, exponent, bits)
        if best is None or distance < best[0]:
            best = (distance, m)
    if best is None:
        raise ValueError(f"no candidate in binade {binade} of {fmt.name}")
    distance, m = best
    log_distance = math.log2(distance) - bits if distance else -math.inf
    # |x mod pi/2| = (pi/2) * distance(x * 2/pi, Z)
    return m, log_distance + math.log2(math.pi / 2)


def binary128_tier(binade: int) -> str:
    if binade % BINARY128_DEFAULT_STRIDE == 0:
        return "default"
    if any(low <= binade <= high for low, high in BINARY128_DEFAULT_RANGES):
        return "default"
    return "slow"


def trig_row(fmt: Format, binade: int) -> tuple[str, ...]:
    """The continued-fraction row of one binade."""
    m, log_distance = best_in_binade(fmt, binade)
    tier = binary128_tier(binade) if fmt.name == "binary128" else "default"
    bits = fmt.encode(m, binade - fmt.fraction_bits)
    return (tier, "trig-cf", fmt.name, "sin,cos", fmt.hex(bits),
            f"log2|x mod pi/2|={log_distance:.2f}")


def trig_rows(format_names: list[str]) -> list[tuple[str, ...]]:
    return [trig_row(FORMATS[name], binade)
            for name in format_names for binade in range(-1, FORMATS[name].emax + 1)]


def named_rows() -> list[tuple[str, ...]]:
    """Published hard cases and inputs earlier kernels misrounded, by exact encoding."""
    b16, b32, b64, b128 = (FORMATS[name] for name in ("binary16", "binary32", "binary64",
                                                       "binary128"))
    wide = FORMATS["ieee31_23"]
    rows: list[tuple[str, ...]] = []

    def named(fmt: Format, operations: str, arguments: list[int], note: str) -> None:
        rows.append(("default", "named", fmt.name, operations,
                     ",".join(fmt.hex(bits) for bits in arguments), note))

    trig = [
        (b64, b64.encode(6221301883130153, 971), "6221301883130153*2^971, sin once 2.6e6 ulps off"),
        (b64, b64.encode(6381956970095103, 797), "6381956970095103*2^797, a published hard case"),
        (b32, b32.encode(16367173, 72), "16367173*2^72, a published hard case"),
        (b64, 0x7F8B1C15D78E7C7C, "earlier cos misrounding"),
        (b64, 0x7EF36BF9A50C0440, "earlier cos misrounding"),
        (b64, 0x7EA7F6A4D2DF7D7F, "earlier cos misrounding"),
        (b128, 0x4FFF116DDFDB67E63123E7050F2CC6AB, "earlier sin misrounding"),
        (b128, 0x4FCCA4D58C542C80C4CEA222BCF86C15, "earlier cos misrounding"),
        (b128, 0x5000F7C5FD03B4406D52F997B02AE816, "earlier NaN beyond 2^4097"),
        (b128, 0x5387E612DBA772A00F53C0C0C1856739, "earlier cos misrounding"),
        (b128, 0x7FFE7D1F5C209F1C120539D262B4DD19, "earlier cos misrounding"),
        (b128, 0x4FFF8000000000000000000000000000, "1.5*2^4096"),
    ]
    for fmt, bits, note in trig:
        named(fmt, "sin,cos", [bits], note)
        named(fmt, "sin,cos", [bits | fmt.sign_bit], note + ", negated")
    # ieee 31 23 arguments near 2^(2^20), reduced with the 2^20- and 2^21-bit levels of 2/pi.
    for exponent in (1048000, 1048575, 1048600):
        named(wide, "sin,cos", [wide.encode(3, exponent - 1)], f"1.5*2^{exponent}")
    tanh16 = [0x2743, 0x2893, 0x2BD5, 0x2F20, 0x319B, 0x3654, 0x3719, 0x379B]
    for bits in tanh16:
        named(b16, "tanh", [bits], "earlier tanh truncation below 1/2")
        named(b16, "tanh", [bits | b16.sign_bit], "earlier tanh truncation below 1/2")
    for bits in (0x35BA, 0x37ED):
        named(b16, "sinh", [bits], "earlier short sinh series")
        named(b16, "sinh", [bits | b16.sign_bit], "earlier short sinh series")
    named(b32, "tanh", [0x3E891F41], "earlier tanh truncation below 1/2")
    named(b32, "tanh", [0x3ED2F3A2], "earlier tanh truncation below 1/2")
    named(b64, "tanh", [0xBFD90A0C65F8EAF0], "earlier tanh truncation below 1/2")
    named(b64, "tanh", [0x3FC8DBB98C62E406], "earlier tanh truncation below 1/2")
    named(b128, "tanh", [0x3FFDA12F7F534A76C000000000000000], "earlier tanh truncation")
    named(wide, "exp", [0x2000000E3141B9], "earlier wide-exponent exp")
    named(wide, "sinh", [0x2000000E302B96], "earlier wide-exponent sinh")
    one64 = b64.encode(1, 0)
    named(b64, "pow", [b64.encode(9, 0), b64.encode(1, -1)], "pow(9, 0.5) = 3")
    named(b64, "pow", [b64.encode(2, 0), b64.encode(1, -1)], "pow(2, 0.5)")
    named(b64, "pow", [0x401D9E6BDE20A780, 0x4074A37EFC2BC320], "large non-integral pow")
    named(b64, "pow", [one64 + 1, b64.encode(1, 60)], "pow(1 + ulp, 2^60)")
    named(b32, "pow", [b32.encode(5, 0), b32.encode(3, -1)], "pow(5, 1.5)")
    named(b32, "pow", [0x411D6E74, 0x41EFFC97], "large non-integral pow")
    return rows


def ln2_scaled(bits: int) -> int:
    """ln 2 * 2^bits within a few units: 2 * atanh(1/3)."""
    guard = 32
    one = 1 << (bits + guard)
    total = 0
    k = 0
    power = one // 3
    while power:
        total += power // (2 * k + 1)
        power //= 9
        k += 1
    return (2 * total) >> guard


def log1m_scaled(numerator: int, shift: int, bits: int) -> int:
    """ln(1 - numerator / 2^shift) * 2^bits for a small ratio, within a few units."""
    guard = 32
    scale = bits + guard
    u = (numerator << scale) >> shift  # u * 2^scale
    total = 0
    power = u
    k = 1
    while power:
        total += power // k
        power = power * u >> scale
        k += 1
    return -(total >> guard)


def nearest_encoding(fmt: Format, scaled: int, bits: int) -> int:
    """Encoding of the float nearest to scaled * 2^-bits (positive), ties to even."""
    if scaled <= 0:
        raise ValueError("positive values only")
    leading = scaled.bit_length() - 1 - bits
    quantum = max(leading, fmt.emin) - fmt.fraction_bits
    shift = bits + quantum
    if shift > 0:
        q, r = divmod(scaled, 1 << shift)
        half = 1 << (shift - 1)
        if r > half or (r == half and q % 2 == 1):
            q += 1
    else:
        q = scaled << (-shift)
    return fmt.encode(q, quantum)


def neighbourhood(fmt: Format, center: int, radius: int, negative: bool = False) -> list[int]:
    sign = fmt.sign_bit if negative else 0
    return [sign | bits for bits in range(max(1, center - radius), center + radius + 1)]


def integer_root(value: int, degree: int) -> int:
    """floor(value^(1/degree))."""
    if value < 2:
        return value
    guess = 1 << ((value.bit_length() + degree - 1) // degree)
    while True:
        better = ((degree - 1) * guess + value // guess ** (degree - 1)) // degree
        if better >= guess:
            break
        guess = better
    while guess ** degree > value:
        guess -= 1
    while (guess + 1) ** degree <= value:
        guess += 1
    return guess


def boundary_rows(format_names: list[str]) -> list[tuple[str, ...]]:
    rows: list[tuple[str, ...]] = []
    for name in format_names:
        fmt = FORMATS[name]
        p = fmt.precision
        fw = fmt.fraction_bits
        bits = p + 96 + max(1, fmt.emax.bit_length())
        ln2 = ln2_scaled(bits)

        def add(operations: str, inputs: list[int], note: str) -> None:
            for code in inputs:
                rows.append(("default", "boundary", name, operations, fmt.hex(code), note))

        def both(inputs: list[int]) -> list[int]:
            return inputs + [code | fmt.sign_bit for code in inputs]

        one = fmt.encode(1, 0)
        half = fmt.encode(1, -1)
        everything = "exp,log,sinh,cosh,tanh"
        steps = sorted({1, 2, 3, 4, 8, 16, 256, 1 << (fw // 2)})
        near_one = [one + k for k in steps] + [one - k for k in steps]
        add(everything, near_one, "1 +- k ulps")
        add(everything, both(neighbourhood(fmt, half, 1)), "1/2 +- 1 ulp")
        add(everything, both(neighbourhood(fmt, fmt.encode(1, 1), 1)), "2 +- 1 ulp")

        # exp overflows at ln((2 - 2^-p) 2^emax) in nearest-even and at ln(max finite) for
        # directed rounding.
        overflow = (fmt.emax + 1) * ln2 + log1m_scaled(1, p + 1, bits)
        overflow_directed = (fmt.emax + 1) * ln2 + log1m_scaled(1, p, bits)
        add("exp", neighbourhood(fmt, nearest_encoding(fmt, overflow, bits), 4),
            "exp overflow threshold +-4 ulps")
        add("exp", neighbourhood(fmt, nearest_encoding(fmt, overflow_directed, bits), 2),
            "exp largest-finite threshold +-2 ulps")
        # exp underflows to zero below 2^(minSub - 1) and leaves the normal range below 2^emin.
        zero_threshold = -(fmt.min_subnormal_exponent - 1) * ln2
        normal_threshold = -fmt.emin * ln2
        add("exp", neighbourhood(fmt, nearest_encoding(fmt, zero_threshold, bits), 4, True),
            "exp underflow-to-zero threshold +-4 ulps")
        add("exp", neighbourhood(fmt, nearest_encoding(fmt, normal_threshold, bits), 4, True),
            "exp subnormal threshold +-4 ulps")
        # sinh and cosh overflow at ln(2 (2 - 2^-p) 2^emax); e^-x is negligible there.
        hyperbolic = overflow + ln2
        add("sinh,cosh", both(neighbourhood(fmt, nearest_encoding(fmt, hyperbolic, bits), 4)),
            "sinh/cosh overflow threshold +-4 ulps")
        # tanh rounds to one from atanh(1 - 2^-(p+1)) = ln(2^(p+2) - 1) / 2.
        saturation = ((p + 2) * ln2 + log1m_scaled(1, p + 2, bits)) // 2
        saturation_code = nearest_encoding(fmt, saturation, bits)
        add("tanh", both(neighbourhood(fmt, saturation_code, 4)),
            "tanh saturation threshold +-4 ulps")
        binade = saturation_code >> fw << fw
        add("tanh", both(neighbourhood(fmt, binade, 1)), "tanh saturation binade +-1 ulp")

        # exp(x) - 1 - x is about x^2/2: these results lie within x^2 of a rounding midpoint.
        midpoint_inputs = [fmt.encode(2 * k + 1, -p) for k in range(4)]
        midpoint_negative = [fmt.encode(2 * k + 1, -p - 1) | fmt.sign_bit for k in range(4)]
        add("exp", midpoint_inputs + midpoint_negative, "exp within x^2 of a midpoint")

        # Arguments where the first Taylor correction of each function crosses half an ulp.
        def relative_transition(reciprocal: int, degree: int) -> list[int]:
            """Inputs x = m 2^(e-fw) near x^degree / reciprocal = ulp(x) / 2, that is
            m^degree = reciprocal 2^((degree-1)(fw-e) - 1), in every binade where m fits."""
            inputs = []
            for e in range(-1, -4 * p, -1):
                m = integer_root(reciprocal << ((degree - 1) * (fw - e) - 1), degree)
                if (1 << fw) <= m < (1 << p):
                    inputs += neighbourhood(fmt, fmt.encode(m, e - fw), 2)
            return both(inputs)

        def square_transition(exponent: int) -> list[int]:
            """Inputs near x = 2^(exponent/2), where x^2/2 = 2^(exponent-1)."""
            for e in range(-1, -4 * p, -1):
                power = 2 * (fw - e) + exponent
                m = integer_root(1 << power, 2) if power >= 0 else 0
                if (1 << fw) <= m < (1 << p):
                    return both(neighbourhood(fmt, fmt.encode(m, e - fw), 2))
            raise ValueError("no binade holds the transition")

        # sinh x = x + x^3/6 and sin x = x - x^3/6; tanh x = x - x^3/3.
        add("sin,sinh", relative_transition(6, 3), "x^3/6 crosses half an ulp")
        add("tanh", relative_transition(3, 3), "x^3/3 crosses half an ulp")
        # cos x = 1 - x^2/2 meets the midpoint 1 - 2^-(p+1); cosh x = 1 + x^2/2 meets 1 + 2^-p.
        add("cos", square_transition(-p), "x^2/2 crosses half an ulp below one")
        add("cosh", square_transition(1 - p), "x^2/2 crosses half an ulp above one")
    return rows


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("data") / "transcendental-hard-cases.tsv")
    parser.add_argument("--trig-formats", default=",".join(TRIG_FORMATS),
                        help="formats of the continued-fraction set (default: all five)")
    return parser.parse_args(argv)


def header(trig_formats: list[str]) -> list[str]:
    return [
        "# Hard cases for FloatLib's transcendental comparison, generated by",
        "# tests/oracles/transcendental_hard_cases.py; do not edit by hand.",
        f"# generator version {GENERATOR_VERSION}",
        f"# parameters two-over-pi-bits={TWO_OVER_PI_BITS} window=3p+{WINDOW_EXTRA_BITS} "
        f"multipliers={MULTIPLIER_COUNT} offsets={OFFSET_RANGE.start}..{OFFSET_RANGE.stop - 1} "
        f"distance-bits=p+{DISTANCE_EXTRA_BITS}",
        f"# trig-cf formats {','.join(trig_formats)}; binary128 default tier: every "
        f"{BINARY128_DEFAULT_STRIDE}th binade and binades "
        + ", ".join(f"{low}..{high}" for low, high in BINARY128_DEFAULT_RANGES),
        "# columns: tier set format operations arguments note",
    ]


def generate(trig_formats: list[str]) -> list[str]:
    rows = trig_rows(trig_formats) + named_rows() + boundary_rows(list(FORMATS))
    return header(trig_formats) + ["\t".join(row) for row in rows]


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    trig_formats = [name for name in args.trig_formats.split(",") if name]
    for name in trig_formats:
        if name not in TRIG_FORMATS:
            raise SystemExit(f"unknown trig format: {name}")
    lines = generate(trig_formats)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {len(lines)} lines to {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
