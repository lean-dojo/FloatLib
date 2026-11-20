#!/usr/bin/env python3
"""Compare FloatLib's complex elementary functions with GNU MPC, through gmpy2.

The Lean executable `oracle complex` answers one request per line (see
`tests/FloatLibTests/Oracle/Complex.lean`). This driver generates arguments for an IEEE binary
format, asks the oracle for each function and rounding direction, and compares every answer with
a reference computed here:

* MPC evaluates the function at a working precision far above the format's and returns, with
  each part rounded to nearest, a ternary value that says whether the part is above, below or
  equal to the exact one. The exact part then lies in an interval that holds no rounding boundary
  of the format, and the integer code in this file rounds it to the format in the requested
  direction, with gradual underflow and the overflow results of IEEE 754-2019, clause 7.4. The
  reference is accepted when two precisions give the same word, and a case where they differ is
  reported as undecided, not as a failure.
* `rsqrt`, `expm1` and `log1p` have no MPC function. They are computed from several MPC
  operations at two precisions, and a directed rounding of a value that comes out representable
  is left undecided, since such a formula can hide a remainder, unless it is `rsqrt` and the
  value satisfies `w² z = 1` in rational arithmetic, which makes it the exact result.
* `pow` takes a base and an exponent (`--functions pow`): MPC's `mpc_pow` is bracketed the same
  way. The oracle marks each result as certified or not. A certified result that differs from
  the reference is a failure, a result without a certificate is counted apart with the number of
  them that equal the reference, and the sign of an exactly zero part is not compared.
* For `asin`, `acos` and `acosh` at an argument `x + i y` off the real axis with
  `x^2 - y^2 = 1`, and for `asinh` off the imaginary axis with `y^2 - x^2 = 1` (for example
  `asin(1.25 + 0.75 i)`), the reference is mpmath's value at two precisions, with the same rule
  for representable values as the composite functions.
* A zero, infinite or NaN part of MPC's result is compared as a class and, for zeros and
  infinities, by sign. A result that is a zero or a least subnormal where the reference is one
  of them with another sign is counted apart, as `tiny`: the reference does not decide the sign
  of a part that underflows its own exponent range.

The reference shares no code with FloatLib. It trusts MPC's directed high-precision values, not
MPC's final rounding to the format. Usage:

    python3 tests/oracles/complex_mpc.py --oracle PATH --format binary32 --samples 2000
"""

import argparse
import random
import subprocess
import sys
import time
from fractions import Fraction

import gmpy2
import mpmath
from gmpy2 import mpc, mpfr

MODES = ["nearest", "nearestAway", "towardZero", "up", "down", "away"]

FORMATS = {
    "binary16": (5, 10),
    "bfloat16": (8, 7),
    "binary32": (8, 23),
    "binary64": (11, 52),
    "binary128": (15, 112),
    "tiny8": (4, 3),
    "tiny6": (3, 2),
}


class Format:
    """An IEEE binary interchange layout by its exponent and fraction widths."""

    def __init__(self, exp_width, frac_width):
        self.exp_width = exp_width
        self.frac_width = frac_width
        self.precision = frac_width + 1
        self.bias = (1 << (exp_width - 1)) - 1
        self.emax = self.bias
        self.emin = 1 - self.bias
        self.exp_all_ones = (1 << exp_width) - 1
        self.sign_shift = exp_width + frac_width
        self.words = 1 << (self.sign_shift + 1)
        self.max_finite = Fraction((1 << self.precision) - 1) * Fraction(2) ** (self.emax - frac_width)

    def fields(self, word):
        sign = (word >> self.sign_shift) & 1
        exponent = (word >> self.frac_width) & self.exp_all_ones
        fraction = word & ((1 << self.frac_width) - 1)
        return sign, exponent, fraction

    def classify(self, word):
        """Return (kind, sign, value) with kind in nan, inf, finite."""
        sign, exponent, fraction = self.fields(word)
        if exponent == self.exp_all_ones:
            return ("nan" if fraction else "inf", sign, None)
        if exponent == 0:
            magnitude = Fraction(fraction) * Fraction(2) ** (self.emin - self.frac_width)
        else:
            magnitude = Fraction((1 << self.frac_width) + fraction) * Fraction(2) ** (
                exponent - self.bias - self.frac_width)
        return ("finite", sign, -magnitude if sign else magnitude)

    def zero(self, sign):
        return sign << self.sign_shift

    def infinity(self, sign):
        return (sign << self.sign_shift) | (self.exp_all_ones << self.frac_width)

    def largest(self, sign):
        return (sign << self.sign_shift) | (((self.exp_all_ones - 1) << self.frac_width)
                                            | ((1 << self.frac_width) - 1))

    def round(self, value, mode):
        """Round a nonzero exact rational to a storage word in the direction `mode`."""
        sign = 1 if value < 0 else 0
        magnitude = -value if sign else value
        leading = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
        if Fraction(2) ** leading > magnitude:
            leading -= 1
        quantum = max(leading - self.frac_width, self.emin - self.frac_width)
        scaled = magnitude / Fraction(2) ** quantum
        mantissa = scaled.numerator // scaled.denominator
        remainder = scaled - mantissa
        half = Fraction(1, 2)
        if remainder == 0:
            increment = False
        elif mode == "nearest":
            increment = remainder > half or (remainder == half and mantissa % 2 == 1)
        elif mode == "nearestAway":
            increment = remainder >= half
        elif mode == "towardZero":
            increment = False
        elif mode == "up":
            increment = sign == 0
        elif mode == "down":
            increment = sign == 1
        elif mode == "away":
            increment = True
        else:
            raise ValueError(mode)
        if increment:
            mantissa += 1
        if mantissa == 1 << self.precision:
            mantissa >>= 1
            quantum += 1
        if Fraction(mantissa) * Fraction(2) ** quantum > self.max_finite:
            to_infinity = mode in ("nearest", "nearestAway", "away") or (
                mode == "up" and sign == 0) or (mode == "down" and sign == 1)
            return self.infinity(sign) if to_infinity else self.largest(sign)
        if mantissa < (1 << self.frac_width):
            return (sign << self.sign_shift) | mantissa
        exponent = quantum + self.frac_width + self.bias
        return (sign << self.sign_shift) | (exponent << self.frac_width) | (
            mantissa - (1 << self.frac_width))


def to_mpfr(fmt, word, precision):
    kind, sign, value = fmt.classify(word)
    with gmpy2.context(gmpy2.get_context(), precision=precision):
        if kind == "nan":
            return mpfr("nan")
        if kind == "inf":
            return mpfr("-inf") if sign else mpfr("inf")
        if value == 0:
            return mpfr("-0") if sign else mpfr("0")
        return mpfr(gmpy2.mpq(value.numerator, value.denominator))


def reference_function(name):
    """The MPC evaluation of each function, at the precision of the current context."""
    one = lambda: mpc(1, 0)
    table = {
        "sqrt": gmpy2.sqrt,
        "rsqrt": lambda z: one() / gmpy2.sqrt(z),
        "exp": gmpy2.exp,
        "expm1": lambda z: gmpy2.exp(z) - 1,
        "log": gmpy2.log,
        "log1p": lambda z: gmpy2.log(1 + z),
        "sin": gmpy2.sin,
        "cos": gmpy2.cos,
        "tan": gmpy2.tan,
        "sinh": gmpy2.sinh,
        "cosh": gmpy2.cosh,
        "tanh": gmpy2.tanh,
        "asin": gmpy2.asin,
        "acos": gmpy2.acos,
        "atan": gmpy2.atan,
        "asinh": gmpy2.asinh,
        "acosh": gmpy2.acosh,
        "atanh": gmpy2.atanh,
    }
    return table[name]


# Functions computed here from several MPC operations: the sign of an exactly zero part is an
# artifact of that formula, so it is not compared.
COMPOSITE = {"rsqrt", "expm1", "log1p"}


def overflow_word(fmt, sign, mode):
    """The result of a value beyond every format: IEEE 754-2019, clause 7.4."""
    to_infinity = mode in ("nearest", "nearestAway", "away") or (
        mode == "up" and sign == 0) or (mode == "down" and sign == 1)
    return fmt.infinity(sign) if to_infinity else fmt.largest(sign)


def tiny_word(fmt, sign, mode):
    """The result of a nonzero value below every format, as a word or a signed zero."""
    away = mode == "away" or (mode == "up" and sign == 0) or (mode == "down" and sign == 1)
    return ("word", (sign << fmt.sign_shift) | 1) if away else ("zero", sign)


def to_fraction(part):
    numerator, denominator = part.as_integer_ratio()
    return Fraction(int(numerator), int(denominator))


def extreme_word(fmt, part, mode):
    """The rounding of a nonzero part far outside the format's range, without its exact value.

    MPFR's exponent range is much wider than any format's, and the exact rational of such a part
    would have billions of digits. A part at or beyond `2 ^ (emax + 2)` overflows, and one below
    a quarter of the least subnormal rounds to a zero or to the least subnormal.
    """
    mantissa, exponent = part.as_mantissa_exp()
    magnitude = int(exponent) + int(abs(mantissa)).bit_length() - 1
    sign = 1 if part < 0 else 0
    if magnitude > fmt.emax + 1:
        return ("word", overflow_word(fmt, sign, mode))
    if magnitude < fmt.emin - fmt.frac_width - 2:
        return tiny_word(fmt, sign, mode)
    return None


def part_word(fmt, part, ternary, mode, precision):
    """Round one part of MPC's value to the format, using its ternary value.

    MPC rounds each part to nearest at `precision` bits and reports whether the returned part is
    above (+1) or below (-1) the exact one, or equal to it (0). An inexact part therefore lies
    strictly between the returned value and the midpoint to its neighbour on that side. With a
    precision three bits above the format's, no rounding boundary of the format is inside that
    interval, so the exact part rounds as a point inside it does.
    """
    if gmpy2.is_nan(part):
        return ("nan", None)
    if gmpy2.is_infinite(part):
        return ("word", overflow_word(fmt, 1 if part < 0 else 0, mode))
    if part == 0:
        if ternary == 0:
            return ("zero", 1 if gmpy2.is_signed(part) else 0)
        # An inexact zero: the exact part lies strictly on the other side of it.
        return tiny_word(fmt, 1 if ternary > 0 else 0, mode)
    extreme = extreme_word(fmt, part, mode)
    if extreme is not None:
        return extreme
    exact = to_fraction(part)
    if ternary == 0:
        return ("word", fmt.round(exact, mode))
    mantissa, exponent = part.as_mantissa_exp()
    unit = Fraction(2) ** (int(exponent) + int(abs(mantissa)).bit_length() - precision)
    inside = exact - unit / 8 if ternary > 0 else exact + unit / 8
    return ("word", fmt.round(inside, mode))


def evaluate(fmt, name, re_word, im_word, precision):
    with gmpy2.context(gmpy2.get_context(), precision=precision, emax=gmpy2.get_emax_max(),
                       emin=gmpy2.get_emin_min()) as context:
        z = mpc(to_mpfr(fmt, re_word, precision), to_mpfr(fmt, im_word, precision))
        context.clear_flags()
        w = reference_function(name)(z)
        return w, w.rc, context.underflow


def ternary_reference(fmt, name, re_word, im_word, mode, precision):
    """Round each part of MPC's value with its ternary value."""
    value, ternary, _ = evaluate(fmt, name, re_word, im_word, precision)
    return (part_word(fmt, value.real, ternary[0], mode, precision),
            part_word(fmt, value.imag, ternary[1], mode, precision))


def trig_sign(fmt, im_word, function):
    """The sign of `cos y` or `sin y` at the imaginary argument, as -1, 0 or 1.

    MPFR evaluates `function` (`gmpy2.cos` or `gmpy2.sin`) at a precision that holds `y`.
    """
    y = fmt.classify(im_word)[2]
    if y == 0:
        return 1 if function is gmpy2.cos else 0
    magnitude = abs(y)
    precision = 256 + magnitude.numerator.bit_length() + magnitude.denominator.bit_length()
    with gmpy2.context(gmpy2.get_context(), precision=precision):
        value = function(mpfr(gmpy2.mpq(y.numerator, y.denominator)))
    return 1 if value > 0 else -1


def same_rounding(fmt, first, second):
    """Whether two expected results are equal, a zero word and a signed zero being the same."""
    def canonical(part):
        kind, payload = part
        if kind == "word" and payload & ~(1 << fmt.sign_shift) == 0:
            return ("zero", payload >> fmt.sign_shift)
        return part
    return tuple(map(canonical, first)) == tuple(map(canonical, second))


def exact_rsqrt(fmt, re_word, im_word, w):
    """Whether the computed `w` is `1 / sqrt z` exactly: `w² z = 1` in rational arithmetic."""
    parts = (w.real, w.imag)
    if not all(gmpy2.is_finite(part) and (part == 0 or extreme_word(fmt, part, "nearest") is None)
               for part in parts):
        return False
    a, b = (to_fraction(part) for part in parts)
    x, y = fmt.classify(re_word)[2], fmt.classify(im_word)[2]
    square_re, square_im = a * a - b * b, 2 * a * b
    return square_re * x - square_im * y == 1 and square_re * y + square_im * x == 0


def composite_reference(fmt, name, re_word, im_word, mode, precision):
    """Round a value computed from several MPC operations at two precisions."""
    answers = []
    for working in (precision, 4 * precision):
        w, _, underflow = evaluate(fmt, name, re_word, im_word, working)
        exact_value = name == "rsqrt" and exact_rsqrt(fmt, re_word, im_word, w)
        parts = []
        for index, part in enumerate((w.real, w.imag)):
            if name == "expm1" and index == 0 and part == -1:
                # `exp x` is below the working precision: the real part is `-1 + exp x cos y`.
                direction = trig_sign(fmt, im_word, gmpy2.cos)
                shift = direction * Fraction(1, 2 ** (8 * fmt.precision))
                parts.append(("word", fmt.round(Fraction(-1) + shift, mode)))
                continue
            if gmpy2.is_nan(part):
                parts.append(("nan", None))
            elif gmpy2.is_infinite(part):
                parts.append(("word", overflow_word(fmt, 1 if part < 0 else 0, mode)))
            elif name == "expm1" and index == 1 and part == 0 and underflow:
                # `exp x` is below MPFR's range: the imaginary part is `exp x sin y`, an exact
                # zero with the sign of `y` at `y = 0`, and elsewhere a value below every format
                # with the sign of `sin y`.
                direction = trig_sign(fmt, im_word, gmpy2.sin)
                parts.append(("zero", fmt.classify(im_word)[1]) if direction == 0
                             else tiny_word(fmt, 1 if direction < 0 else 0, mode))
            elif part == 0:
                sign = 1 if gmpy2.is_signed(part) else 0
                parts.append(tiny_word(fmt, sign, mode) if underflow else ("zero", sign))
            elif extreme_word(fmt, part, mode) is not None:
                parts.append(extreme_word(fmt, part, mode))
            else:
                exact = to_fraction(part)
                if mode not in ("nearest", "nearestAway") and not exact_value and (
                        fmt.round(exact, "up") == fmt.round(exact, "down")):
                    # A representable value of a composite formula may hide a remainder.
                    return None
                parts.append(("word", fmt.round(exact, mode)))
        answers.append(tuple(parts))
    return answers[0] if same_rounding(fmt, answers[0], answers[1]) else None


def uses_mpmath(name, x, y):
    """Arguments whose reference is mpmath's value: `1 - z^2` or `1 + z^2` is imaginary."""
    if name in ("asin", "acos", "acosh"):
        return y != 0 and x * x - y * y == 1
    if name == "asinh":
        return x != 0 and y * y - x * x == 1
    return False


def mpmath_reference(fmt, name, x, y, mode, precision):
    """Round mpmath's value at two precisions. None when they differ or may hide a remainder."""
    answers = []
    for working in (precision, 4 * precision):
        with mpmath.workprec(working):
            z = mpmath.mpc(mpmath.mpf(x.numerator) / x.denominator,
                           mpmath.mpf(y.numerator) / y.denominator)
            w = getattr(mpmath, name)(z)
            parts = []
            for part in (w.real, w.imag):
                sign, mantissa, exponent, _ = part._mpf_
                exact = Fraction(-int(mantissa) if sign else int(mantissa)) * Fraction(2) ** exponent
                if exact == 0:
                    parts.append(("zero", None))
                elif mode not in ("nearest", "nearestAway") and (
                        fmt.round(exact, "up") == fmt.round(exact, "down")):
                    return None
                else:
                    parts.append(("word", fmt.round(exact, mode)))
        answers.append(tuple(parts))
    return answers[0] if same_rounding(fmt, answers[0], answers[1]) else None


def saturated_tanh(fmt, a, b, mode):
    """`tanh (a + i b)` for `|a| > 2 ^ 14`, where MPC's directed rounding is too slow.

    With `u = exp(-2|a|)` far below the format, the real part is `±(1 - 2 u cos 2b)` to first
    order and the imaginary part `4 u sin 2b` underflows, so only the signs of `cos 2b` and
    `sin 2b` matter. They come from MPFR at a precision that holds `2 b` exactly.
    """
    magnitude = abs(b)
    precision = 256 + (magnitude.numerator.bit_length() + magnitude.denominator.bit_length()
                       if b != 0 else 0)
    with gmpy2.context(gmpy2.get_context(), precision=precision):
        angle = 2 * mpfr(gmpy2.mpq(b.numerator, b.denominator))
        cosine, sine = gmpy2.cos(angle), gmpy2.sin(angle)
    sign = -1 if a < 0 else 1
    shift = Fraction(1, 2 ** (4 * fmt.precision))
    real = sign * (1 - shift if cosine > 0 else 1 + shift)
    if sine == 0:
        imaginary = ("zero", 1 if b < 0 or (b == 0 and False) else 0)
    else:
        imaginary = tiny_word(fmt, 1 if sine < 0 else 0, mode)
    return (("word", fmt.round(real, mode)), imaginary)


def reference(fmt, name, re_word, im_word, mode, spread):
    """The rounded exact result, or None when MPC does not decide it."""
    x = fmt.classify(re_word)[2]
    y = fmt.classify(im_word)[2]
    if name == "tanh" and abs(x) > 2 ** 14 and y != 0:
        return saturated_tanh(fmt, x, y, mode)
    if name == "tanh" and abs(x) > 2 ** 14:
        # tanh (x ± 0 i) = tanh x ± 0 i.
        return (saturated_tanh(fmt, x, Fraction(0), mode)[0], ("zero", fmt.classify(im_word)[1]))
    if name == "tan" and abs(y) > 2 ** 14 and x == 0:
        # tan (±0 + i y) = ±0 + i tanh y.
        return (("zero", fmt.classify(re_word)[1]), saturated_tanh(fmt, y, Fraction(0), mode)[0])
    if name == "tan" and abs(y) > 2 ** 14 and x != 0:
        # tan z = -i tanh (i z): i z = -y + i x, and -i (u + i v) = v - i u.
        mirrored = "up" if mode == "down" else "down" if mode == "up" else mode
        u, _ = saturated_tanh(fmt, -y, x, mirrored)
        _, v = saturated_tanh(fmt, -y, x, mode)
        kind, payload = u
        negated = (kind, payload ^ (1 << fmt.sign_shift) if kind == "word" else 1 - payload)
        return (v, negated)
    precision = 2 * fmt.precision + 64 + spread
    if uses_mpmath(name, x, y):
        return mpmath_reference(fmt, name, x, y, mode, precision)
    if name in COMPOSITE:
        # `exp z - 1` and `log (1 + z)` differ from a tiny `z` in its square, and the real part
        # `cos y - 1` of `exp (i y) - 1` from `-y² / 2` in the fourth power.
        return composite_reference(fmt, name, re_word, im_word, mode, precision + 3 * spread)
    first = ternary_reference(fmt, name, re_word, im_word, mode, precision)
    second = ternary_reference(fmt, name, re_word, im_word, mode, 2 * precision)
    return first if same_rounding(fmt, first, second) else None


def pow_reference(fmt, words, mode, precision):
    """Round each part of MPC's `z ** w` with its ternary value."""
    with gmpy2.context(gmpy2.get_context(), precision=precision, emax=gmpy2.get_emax_max(),
                       emin=gmpy2.get_emin_min()):
        z = mpc(to_mpfr(fmt, words[0], precision), to_mpfr(fmt, words[1], precision))
        w = mpc(to_mpfr(fmt, words[2], precision), to_mpfr(fmt, words[3], precision))
        value = z ** w
        ternary = value.rc
    return (part_word(fmt, value.real, ternary[0], mode, precision),
            part_word(fmt, value.imag, ternary[1], mode, precision))


def pow_arguments(fmt, args, rng):
    """Bases and exponents: small integers and halves, moderate values and wide bases."""
    def exact(value):
        return fmt.round(Fraction(value), "nearest")
    special = [exact(v) for v in (0, 1, -1, 2, -2, 3, Fraction(1, 2), Fraction(-1, 2),
                                  Fraction(1, 4), Fraction(3, 2), 5, -3, 10, 100)]
    quadruples = []
    strict = set()
    if args.hard:
        bases = [exact(v) for v in (1, -1, 2, -4, Fraction(1, 2), Fraction(-1, 4), 0, 3)]
        zeros = [0, 1 << fmt.sign_shift]
        for re in bases:
            for im in bases[:6] + zeros:
                for c in special[:9]:
                    for d in (0, exact(1), exact(Fraction(-1, 2))):
                        quadruples.append((re, im, c, d))
        # Bases with a complex rational root, and their neighbours without one, at exponents
        # `n / 2 ^ k`: the powers that `gaussRatPow?` forms exactly.
        roots = [(16, 0), (-64, 0), (-7, 24), (-7, -24), (-3, 4), (0, 2), (0, -8),
                 (Fraction(1, 16), 0), (Fraction(-1, 4), 0), (81, 0), (2, 0), (-119, 120)]
        for x, y in roots:
            for c in (Fraction(1, 4), Fraction(-1, 4), Fraction(3, 4), Fraction(1, 8),
                      Fraction(3, 2), Fraction(-3, 2), Fraction(5, 2), Fraction(3, 8)):
                quadruples.append((exact(x), exact(y), exact(c), 0))
        # Bases next to an axis, at real exponents whose power lies next to an axis again: the
        # part next to zero keeps its relative accuracy only with the angle from that axis.
        offsets = [Fraction(1, 2 ** k) for k in (fmt.frac_width + 10, 3 * fmt.frac_width,
                                                 fmt.bias - 2)]
        for scale in (1, Fraction(3, 2), Fraction(1, 1024), 1 << 10):
            for offset in offsets:
                for x, y in ((-scale, offset), (-scale, -offset), (scale, offset),
                             (offset, scale), (-offset, scale), (offset, -scale)):
                    for c in (2, 3, 7, 100, -7, Fraction(3, 2), Fraction(5, 2), Fraction(-3, 2),
                              Fraction(7, 2)):
                        quadruples.append((exact(x), exact(y), exact(c), 0))
        # Perfect powers with a perturbation of one part: the power lies next to a
        # representable number, at a distance of the square of the perturbation.
        for x, c in ((4, Fraction(3, 2)), (16, Fraction(3, 4)), (9, Fraction(5, 2)),
                     (Fraction(1, 4), Fraction(3, 2)), (-4, Fraction(3, 2)), (-9, Fraction(5, 2)),
                     (16, Fraction(-5, 4)), (-16, Fraction(3, 2))):
            for offset in offsets:
                for y in (offset, -offset):
                    quadruples.append((exact(x), exact(y), exact(c), 0))
                    quadruples.append((exact(y), exact(x), exact(c), 0))
        # Bases whose parts have the least ratio of the format, at exponents whose power of the
        # larger part is representable: the power lies at a relative distance of the square
        # of that ratio from a representable number.
        top = Fraction(2) ** (4 * ((fmt.emax - 3) // 4))
        least = Fraction(2) ** (fmt.emin - fmt.frac_width)
        for x, y in ((top, least), (-top, least), (top, -least), (least, top), (-least, top),
                     (1 / top, least), (top, 3 * least), (-top, -least)):
            for c in (Fraction(3, 4), Fraction(3, 2), Fraction(-3, 4), Fraction(5, 4),
                      Fraction(1, 4), Fraction(-1, 4), Fraction(5, 2), Fraction(7, 4)):
                quadruples.append((exact(x), exact(y), exact(c), 0))
        # Powers far outside the range of the format, and integer powers too long to form. No
        # part of these is zero, except at an even integer exponent of the base on the diagonal,
        # so a result below the format is compared with its sign.
        for x, y in ((1, 1), (3, -2), (Fraction(1, 2), Fraction(1, 3)), (-5, 1)):
            for c in (10 ** 7 + Fraction(1, 2), -(10 ** 7) - Fraction(1, 2), 2 ** 40,
                      Fraction(10 ** 5 + 1, 4), 100001, -100001, 2 ** 70 + 2 ** 30,
                      -(2 ** 90) - 2 ** 40):
                for d in (0, exact(Fraction(1, 2)), exact(-(2 ** 45))):
                    quadruple = (exact(x), exact(y), exact(c), d)
                    quadruples.append(quadruple)
                    rounded = fmt.classify(quadruple[2])[2]
                    if rounded is not None and not (
                            x == y and d == 0 and rounded.denominator == 1 and rounded % 2 == 0):
                        strict.add(quadruple)
        # Bases on a diagonal at even integer exponents: the power lies on an axis, at any size
        # of the exponent.
        for x in (1, -1, 3, Fraction(-1, 2), Fraction(5, 8)):
            for y in (x, -x):
                for c in (2, 6, -4, 100, 2046, -2148, 10 ** 6, 100002, 200004, -100006,
                          2 ** 40, -(2 ** 40)):
                    quadruples.append((exact(x), exact(y), exact(c), 0))
    styles = ["moderate", "near_one", "wide", "moderate"]
    for index in range(args.samples):
        style = styles[index % len(styles)]
        re, im = random_word(fmt, rng, style), random_word(fmt, rng, style)
        kind = index % 5
        if kind == 0:
            c, d = rng.choice(special), 0
        elif kind == 1:
            c, d = random_word(fmt, rng, "moderate"), 0
        elif kind == 2:
            c, d = random_word(fmt, rng, "moderate"), random_word(fmt, rng, "moderate")
        elif kind == 3:
            c, d = random_word(fmt, rng, "near_one"), random_word(fmt, rng, "near_one")
        else:
            c, d = exact(rng.randint(-40, 40)), rng.choice([0, exact(rng.randint(-3, 3))])
        quadruples.append((re, im, c, d))
    return [q for q in quadruples if all(is_finite(fmt, word) for word in q)
            and not (fmt.classify(q[0])[2] == 0 and fmt.classify(q[1])[2] == 0)], strict


def run_pow(args, fmt, modes, rng):
    """Compare `pow` with MPC on bases and exponents. Returns the number of failures."""
    cases, strict = pow_arguments(fmt, args, rng)
    total_failures = 0
    for mode in modes:
        requests = [f"pow {fmt.exp_width} {fmt.frac_width} {mode} {re} {im} {c} {d}"
                    for re, im, c, d in cases]
        answers, elapsed = ask(args.oracle, requests)
        failures = undecided = uncertified = uncertified_equal = 0
        for words, answer in zip(cases, answers):
            precision = 2 * fmt.precision + 64 + exponent_spread(fmt, words)
            expected = pow_reference(fmt, words, mode, precision)
            if expected != pow_reference(fmt, words, mode, 2 * precision):
                expected = None
            fields = answer.split()
            if len(fields) != 3 or fields[0] == "error":
                failures += 1
                if failures <= args.show:
                    print(f"  FAIL pow {mode} {words}: got {answer}")
                continue
            certified = fields[2] == "1"
            if expected is None:
                undecided += 1
                uncertified += 0 if certified else 1
                if args.show_uncertified and undecided <= args.show:
                    values = [fmt.classify(word)[2] for word in words]
                    print(f"  UNDECIDED pow {mode} base {float(values[0])!r} "
                          f"{float(values[1])!r} exponent {float(values[2])!r} "
                          f"{float(values[3])!r}: got {answer}")
                continue
            if words in strict:
                ok = all(matches(fmt, "strict", expected[k], int(fields[k])) for k in (0, 1))
            else:
                ok = all(matches(fmt, "pow", expected[k], int(fields[k])) or (
                    is_tiny(fmt, expected[k]) and is_tiny(fmt, ("word", int(fields[k]))))
                    for k in (0, 1))
            if not certified:
                uncertified += 1
                uncertified_equal += 1 if ok else 0
                if args.show_uncertified and uncertified <= args.show:
                    values = [fmt.classify(word)[2] for word in words]
                    print(f"  UNCERTIFIED pow {mode} base {float(values[0])!r} "
                          f"{float(values[1])!r} exponent {float(values[2])!r} "
                          f"{float(values[3])!r}: got {answer}, MPC {expected}")
            elif not ok:
                failures += 1
                if failures <= args.show:
                    print(f"  FAIL pow {mode} {words}: got {answer}, expected {expected}")
        total_failures += failures
        per_call = 1e3 * elapsed / max(1, len(cases))
        print(f"pow    {mode:11} {args.format}: {len(cases)} cases, {failures} failures, "
              f"{undecided} undecided, {uncertified} without certificate "
              f"({uncertified_equal} of them equal to MPC), {per_call:.3f} ms per call in Lean")
        sys.stdout.flush()
    return total_failures


def exponent_spread(fmt, words):
    """Bits needed to hold `1 + z` and similar exact sums of the parts."""
    exponents = [0]
    for word in words:
        kind, _, value = fmt.classify(word)
        if kind == "finite" and value != 0:
            magnitude = abs(value)
            exponents.append(magnitude.numerator.bit_length() - magnitude.denominator.bit_length())
    return max(exponents) - min(exponents)


def matches(fmt, name, expected, actual_word):
    kind, payload = expected
    actual_kind, actual_sign, actual_value = fmt.classify(actual_word)
    if kind == "nan":
        return actual_kind == "nan"
    if kind == "zero":
        if actual_kind != "finite" or actual_value != 0:
            return False
        return name in COMPOSITE or name == "pow" or payload is None or actual_sign == payload
    return actual_word == payload


def is_tiny(fmt, expected):
    """A zero or a least subnormal of either sign."""
    kind, payload = expected
    if kind == "zero":
        return True
    return kind == "word" and (payload & ~(1 << fmt.sign_shift)) in (0, 1)


def random_word(fmt, rng, style):
    if style == "bits":
        return rng.randrange(fmt.words)
    if style == "moderate":
        exponent = fmt.bias + rng.randint(-6, 6)
    elif style == "near_one":
        exponent = fmt.bias + rng.choice([-1, 0])
    elif style == "small":
        exponent = rng.randint(0, fmt.bias - 5)
    else:
        exponent = rng.randint(0, fmt.exp_all_ones - 1)
    fraction = rng.randrange(1 << fmt.frac_width)
    if style == "near_one" and rng.random() < 0.5:
        fraction = rng.choice([0, 1, (1 << fmt.frac_width) - 1]) if exponent == fmt.bias else (
            (1 << fmt.frac_width) - 1 - rng.randrange(4))
    return (rng.getrandbits(1) << fmt.sign_shift) | (exponent << fmt.frac_width) | fraction


def hard_words(fmt):
    """Signed zeros, the subnormal range, powers of two, values around one and the extremes."""
    one = fmt.bias << fmt.frac_width
    positive = [
        0, 1, 2, (1 << fmt.frac_width) - 1, 1 << fmt.frac_width, (1 << fmt.frac_width) + 1,
        one - 1, one, one + 1, one + (1 << (fmt.frac_width - 1)),
        (fmt.bias - 1) << fmt.frac_width, (fmt.bias + 1) << fmt.frac_width,
        ((fmt.bias + 1) << fmt.frac_width) + (1 << (fmt.frac_width - 1)),
        (fmt.bias + 2) << fmt.frac_width, fmt.largest(0),
        ((fmt.exp_all_ones - 1) << fmt.frac_width),
    ]
    return positive + [word | (1 << fmt.sign_shift) for word in positive]


def is_finite(fmt, word):
    return fmt.classify(word)[0] == "finite"


def excluded(fmt, name, re_word, im_word):
    """Poles and arguments outside this comparison: non-finite inputs are tested in Lean."""
    if not (is_finite(fmt, re_word) and is_finite(fmt, im_word)):
        return True
    x = fmt.classify(re_word)[2]
    y = fmt.classify(im_word)[2]
    if name in ("log", "rsqrt") and x == 0 and y == 0:
        return True
    if name == "log1p" and ((x == -1 and y == 0) or (x == 0 and y == 0)):
        return True
    if name == "expm1" and x == 0 and y == 0:
        return True
    if name == "atanh" and abs(x) == 1 and y == 0:
        return True
    if name == "atan" and x == 0 and abs(y) == 1:
        return True
    return False


def ask(oracle, requests):
    payload = "".join(line + "\n" for line in requests)
    started = time.monotonic()
    completed = subprocess.run([oracle, "complex"], input=payload, capture_output=True,
                               text=True, check=True)
    elapsed = time.monotonic() - started
    answers = completed.stdout.splitlines()
    if len(answers) != len(requests):
        raise RuntimeError(f"oracle returned {len(answers)} answers for {len(requests)} requests")
    return answers, elapsed


def arguments(fmt, args, rng):
    pairs = []
    if args.exhaustive:
        return [(re, im) for re in range(fmt.words) for im in range(fmt.words)]
    if args.axes:
        return [(word, 0) for word in range(fmt.words)] + [(0, word) for word in range(fmt.words)]
    if args.hard:
        words = hard_words(fmt)
        pairs.extend((re, im) for re in words for im in words)
    styles = args.styles.split(",")
    for index in range(args.samples):
        style = styles[index % len(styles)]
        pairs.append((random_word(fmt, rng, style), random_word(fmt, rng, style)))
    return pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--oracle", required=True, help="path of the built `oracle` executable")
    parser.add_argument("--format", default="binary32",
                        help="a named format or EXPWIDTH,FRACWIDTH")
    parser.add_argument("--functions", default="sqrt,rsqrt,log,log1p,atanh,atan")
    parser.add_argument("--modes", default="nearest")
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=20261116)
    parser.add_argument("--styles", default="bits,moderate,near_one,wide",
                        help="kinds of random arguments, in turn: bits (any encoding), moderate "
                             "(exponents within six of zero), near_one, wide (any exponent), "
                             "small (magnitudes below one sixteenth, subnormal numbers included)")
    parser.add_argument("--hard", action="store_true", help="add the grid of hard arguments")
    parser.add_argument("--exhaustive", action="store_true", help="every pair of encodings")
    parser.add_argument("--axes", action="store_true",
                        help="every encoding on the real axis and on the imaginary axis")
    parser.add_argument("--show", type=int, default=10, help="failures printed per function")
    parser.add_argument("--show-uncertified", action="store_true",
                        help="print the powers returned without a certificate")
    parser.add_argument("--show-tiny", action="store_true",
                        help="print the tiny results whose sign differs from MPC's")
    args = parser.parse_args()

    if args.format in FORMATS:
        fmt = Format(*FORMATS[args.format])
    else:
        fmt = Format(*(int(width) for width in args.format.split(",")))
    modes = MODES if args.modes == "all" else args.modes.split(",")
    rng = random.Random(args.seed)
    pairs = arguments(fmt, args, rng)

    total_failures = 0
    for name in args.functions.split(","):
        if name == "pow":
            total_failures += run_pow(args, fmt, modes, rng)
            continue
        cases = [(re, im) for re, im in pairs if not excluded(fmt, name, re, im)]
        for mode in modes:
            requests = [f"{name} {fmt.exp_width} {fmt.frac_width} {mode} {re} {im}"
                        for re, im in cases]
            answers, elapsed = ask(args.oracle, requests)
            failures = undecided = tiny = 0
            for (re, im), answer in zip(cases, answers):
                expected = reference(fmt, name, re, im, mode, exponent_spread(fmt, [re, im]))
                if expected is None:
                    undecided += 1
                    continue
                fields = answer.split()
                if len(fields) != 2 or fields[0] == "error":
                    ok = [False, False]
                else:
                    ok = [matches(fmt, name, expected[k], int(fields[k])) for k in (0, 1)]
                    for k in (0, 1):
                        if not ok[k] and is_tiny(fmt, expected[k]) and is_tiny(
                                fmt, ("word", int(fields[k]))):
                            ok[k] = True
                            tiny += 1
                            if args.show_tiny and tiny <= args.show:
                                print(f"  TINY {name} {mode} re={re} im={im}: got {answer}, "
                                      f"MPC {expected}")
                if not all(ok):
                    failures += 1
                    if failures <= args.show:
                        print(f"  FAIL {name} {mode} re={re} im={im}: got {answer}, "
                              f"expected {expected}")
            total_failures += failures
            per_call = 1e3 * elapsed / max(1, len(cases))
            print(f"{name:6} {mode:11} {args.format}: {len(cases)} cases, {failures} failures, "
                  f"{undecided} undecided, {tiny} tiny, {per_call:.3f} ms per call in Lean")
            sys.stdout.flush()
    return 1 if total_failures else 0


if __name__ == "__main__":
    sys.exit(main())
