#!/usr/bin/env python3
"""Reference results for the functions of IEEE 754-2019 clause 9.2 on binary formats.

usage: functions.py PACKAGES COUNT SEED

PACKAGES is a directory that holds the Python package `mpmath` (for example the target of
`pip install --target PACKAGES mpmath`). The script writes one case per line for
`oracle ieee2019 check`:

    fun NAME FORMAT MODE X Y EXPECTED FLAGS

NAME is the name of the function in the standard (`cbrt` is `rootn` of degree three). FORMAT is
`e3f2`, `e4f3`, `e5m2`, `e4m3`, `e4m3fnuz`, `e5m2fnuz`, `e2m1`, `binary16`, `binary32` or
`binary64`. MODE is the rounding direction: `E` to nearest with ties to even, `A` to nearest
with ties away from zero, `Z` toward zero, `U` toward positive and `D` toward negative
infinity. X is the encoding of the first operand in hexadecimal. Y is `-` for a function of one
operand, the encoding of the second operand for `atan2`, `atan2Pi`, `powr`, `pow` and `hypot`
(in the order of the call: `atan2 y x`, `powr x y`, `pow x y`), and the integer `n` for
`compound`, `rootn` and `pown`.
EXPECTED is the encoding of the result, or `nan` for any quiet NaN. FLAGS is the sum of
invalid 1, divideByZero 2, overflow 4, underflow 8 and inexact 16.

The formats. `e3f2` and `e4f3` are IEEE formats of six and eight bits. `e5m2` and `e4m3` are
the two formats of the OCP 8-bit Floating Point Specification (OFP8) revision 1.0, 5.1: E5M2 is
an IEEE format, and E4M3 has no infinity, uses its largest exponent for finite values, and has
the NaN `S.1111.111`. `e4m3fnuz` and `e5m2fnuz` are the ONNX formats with bias 8 and 16, one
zero and the single NaN `0x80`. `e2m1` is the four-bit format of the OCP Microscaling Formats
Specification 1.0, 5.3.3, in which every encoding is finite. A format without an infinity
delivers its NaN where an IEEE format delivers an infinity (a pole, or an overflow in a
direction that rounds away), and a format without a NaN delivers its largest finite value of
that sign there and `+0` for an invalid operation. A format with one zero delivers it for a
zero of either sign.

The cases are: every encoding of each small format for each function of one operand in each of
the five directions, with eight degrees for `rootn` and eight exponents for `pown`; every pair
of encodings of `e3f2` and of `e2m1` for the functions of two operands in each direction and
50 * COUNT pseudo-random pairs of each eight-bit format; every encoding of `e3f2` with thirteen
exponents for `compound` in each direction; and COUNT pseudo-random operands for each function
in each of binary16, binary32 and binary64, in a pseudo-random direction. For `sin`, `cos` and
`tan` the pseudo-random operands are below `2^400`, and with COUNT at least 100 three binary64
operands beyond that are added, each of which takes FloatLib about a minute.

How the expected results are computed. The results at NaNs, infinities, zeros and outside the
domains are written here from the special cases of ISO/IEC 9899:2024 F.10.1 to F.10.4, for
the infinite operands of `powr` from its formula `exp (y * log x)`, and for `pow`, `rSqrt`,
`hypot`, `rootn` and `pown` from IEEE 754-2019 9.2.1. Every other result is the
value that `mpmath` computes with a working precision far above the format (at least 300 bits
more than three times the largest exponent of an operand, so that `sin x` and `x` differ
visibly for the smallest subnormal `x`), rounded here in the direction of the case with exact
rational arithmetic. `compound` and `pown` are computed exactly with rationals, and so are the
roots of `rSqrt`, `rootn` and `hypot`: a root is exact when integer roots of the numerator and
the denominator are, and otherwise integers bracket it between two neighbours of a grid finer
than the format, whatever the sizes of the two terms of `x^2 + y^2`. Any other result is taken
to be exact when the high-precision value is itself a value of the format. `tanh`, `expm1`, `exp2m1`
and `exp10m1` approach a representable limit faster than any fixed precision, so their
precision grows with the operand, and a result that is the limit itself is inexact, since no
finite operand reaches it.
"""
import random
import sys
from fractions import Fraction

sys.path.insert(0, sys.argv[1])
import mpmath  # noqa: E402

FORMATS = {"e3f2": (3, 2, "ieee"), "e4f3": (4, 3, "ieee"), "e5m2": (5, 2, "ieee"),
           "e4m3": (4, 3, "maxnan"), "e4m3fnuz": (4, 3, "fnuz"), "e5m2fnuz": (5, 2, "fnuz"),
           "e2m1": (2, 1, "finite"), "binary16": (5, 10, "ieee"), "binary32": (8, 23, "ieee"),
           "binary64": (11, 52, "ieee")}
INVALID, DIVIDE_BY_ZERO, OVERFLOW, UNDERFLOW, INEXACT = 1, 2, 4, 8, 16


class Format:
    """A binary format: `ieee` (infinities and NaNs in the largest exponent), `maxnan` (no
    infinity, the largest encoding of each sign is a NaN), `fnuz` (bias one more, no infinity,
    one zero, the encoding of minus zero is the NaN) or `finite` (every encoding is finite)."""

    def __init__(self, name):
        self.name = name
        self.mode = "E"
        self.ew, self.fw, self.kind = FORMATS[name]
        self.bias = (1 << (self.ew - 1)) - (0 if self.kind == "fnuz" else 1)
        self.emin = 1 - self.bias
        self.width = 1 + self.ew + self.fw
        top = (1 << self.ew) - 1
        if self.kind == "ieee":
            largest = ((top - 1) << self.fw) | ((1 << self.fw) - 1)
        elif self.kind == "maxnan":
            largest = (top << self.fw) | ((1 << self.fw) - 2)
        else:
            largest = (top << self.fw) | ((1 << self.fw) - 1)
        self.largest = largest
        self.max_finite = self.decode(largest)[2]

    def decode(self, bits):
        """('nan', signaling), ('inf', negative) or ('fin', negative, value)."""
        negative = bool(bits >> (self.ew + self.fw))
        exponent = (bits >> self.fw) & ((1 << self.ew) - 1)
        fraction = bits & ((1 << self.fw) - 1)
        top = (1 << self.ew) - 1
        if self.kind == "ieee" and exponent == top:
            if fraction == 0:
                return ("inf", negative)
            return ("nan", not (fraction >> (self.fw - 1)))
        if self.kind == "maxnan" and exponent == top and fraction == (1 << self.fw) - 1:
            return ("nan", False)
        if self.kind == "fnuz" and bits == 1 << (self.ew + self.fw):
            return ("nan", False)
        if exponent == 0:
            magnitude = Fraction(fraction) * Fraction(2) ** (self.emin - self.fw)
        else:
            magnitude = Fraction((1 << self.fw) + fraction) * Fraction(2) ** (exponent - self.bias - self.fw)
        return ("fin", negative, -magnitude if negative else magnitude)

    def zero(self, negative):
        if self.kind == "fnuz":
            return 0
        return int(negative) << (self.ew + self.fw)

    def infinity(self, negative):
        """What the format delivers for an infinite result: its infinity, its NaN, or its
        largest finite value of that sign."""
        if self.kind == "ieee":
            return (int(negative) << (self.ew + self.fw)) | (((1 << self.ew) - 1) << self.fw)
        if self.kind == "finite":
            return (int(negative) << (self.ew + self.fw)) | self.largest
        return "nan"

    def round(self, value, mode=None, zero_negative=False):
        """Encoding and flags of the rounding of a rational in the direction `mode`, which is the
        direction of the current case when it is not given."""
        mode = mode or self.mode
        if value == 0:
            return self.zero(zero_negative), 0
        negative = value < 0
        magnitude = abs(value)
        exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
        if Fraction(2) ** exponent > magnitude:
            exponent -= 1
        if Fraction(2) ** (exponent + 1) <= magnitude:
            exponent += 1
        # Whether the direction rounds this magnitude up when it lies strictly between two values.
        upward = (mode == "U" and not negative) or (mode == "D" and negative)

        def rounded_at(grid_exponent):
            unit = Fraction(2) ** (grid_exponent - self.fw)
            scaled = magnitude / unit
            floor = scaled.numerator // scaled.denominator
            rest = scaled - floor
            if mode == "E":
                up = rest > Fraction(1, 2) or (rest == Fraction(1, 2) and floor % 2 == 1)
            elif mode == "A":
                up = rest >= Fraction(1, 2)
            else:
                up = upward and rest > 0
            return (floor + 1 if up else floor) * unit

        unbounded = rounded_at(exponent)
        tiny = unbounded < Fraction(2) ** self.emin
        rounded = rounded_at(max(exponent, self.emin))
        inexact = rounded != magnitude
        if unbounded > self.max_finite:
            # An overflow: what the format has for an infinity, or the largest finite value when
            # the direction rounds this magnitude down.
            if mode in ("E", "A") or upward:
                return self.infinity(negative), OVERFLOW | INEXACT
            return (int(negative) << (self.ew + self.fw)) | self.largest, OVERFLOW | INEXACT
        flags = (INEXACT if inexact else 0) | (UNDERFLOW if tiny and inexact else 0)
        if rounded == 0:
            return self.zero(negative), flags
        exponent = rounded.numerator.bit_length() - rounded.denominator.bit_length()
        if Fraction(2) ** exponent > rounded:
            exponent -= 1
        if exponent < self.emin:
            field, fraction = 0, int(rounded / Fraction(2) ** (self.emin - self.fw))
        else:
            field = exponent + self.bias
            fraction = int(rounded / Fraction(2) ** (exponent - self.fw)) - (1 << self.fw)
        return (int(negative) << (self.ew + self.fw)) | (field << self.fw) | fraction, flags


def to_fraction(value):
    sign, mantissa, exponent, _ = mpmath.mpf(value)._mpf_
    result = Fraction(int(mantissa)) * Fraction(2) ** int(exponent)
    return -result if sign else result


def to_mpf(value):
    return mpmath.mpf(value.numerator) / mpmath.mpf(value.denominator)


def exponent_of(value):
    if value == 0:
        return 0
    return abs(abs(value).numerator.bit_length() - abs(value).denominator.bit_length())


def half_turn_tangent(x):
    return mpmath.sinpi(x) / mpmath.cospi(x)


REAL = {
    "exp": mpmath.exp, "expm1": mpmath.expm1, "log": mpmath.log, "logp1": mpmath.log1p,
    "exp2": lambda x: mpmath.power(2, x), "exp2m1": lambda x: mpmath.power(2, x) - 1,
    "exp10": lambda x: mpmath.power(10, x), "exp10m1": lambda x: mpmath.power(10, x) - 1,
    "log2": lambda x: mpmath.log(x, 2), "log10": lambda x: mpmath.log(x, 10),
    "log2p1": lambda x: mpmath.log(1 + x, 2), "log10p1": lambda x: mpmath.log(1 + x, 10),
    "sin": mpmath.sin, "cos": mpmath.cos, "tan": mpmath.tan,
    "sinPi": mpmath.sinpi, "cosPi": mpmath.cospi, "tanPi": half_turn_tangent,
    "asin": mpmath.asin, "acos": mpmath.acos, "atan": mpmath.atan,
    "asinPi": lambda x: mpmath.asin(x) / mpmath.pi, "acosPi": lambda x: mpmath.acos(x) / mpmath.pi,
    "atanPi": lambda x: mpmath.atan(x) / mpmath.pi,
    "sinh": mpmath.sinh, "cosh": mpmath.cosh, "tanh": mpmath.tanh,
    "asinh": mpmath.asinh, "acosh": mpmath.acosh, "atanh": mpmath.atanh,
}
UNARY = list(REAL) + ["rSqrt", "cbrt"]
ODD_AT_ZERO = {"expm1", "exp2m1", "exp10m1", "logp1", "log2p1", "log10p1", "sin", "tan", "sinPi", "tanPi", "asin",
               "atan", "asinPi", "atanPi", "sinh", "tanh", "asinh", "atanh"}
SATURATING = {"tanh", "expm1", "exp2m1", "exp10m1"}
DEGREES = (-3, -2, -1, 0, 1, 2, 3, 5)
EXPONENTS = (-3, -2, -1, 0, 1, 2, 3, 7)


def exact_value(fmt, function, operands, name=""):
    """`function(*operands)` (exact rationals) at high precision, as a rational. A value beyond
    the range of the format is replaced by one that rounds like it in every direction."""
    largest = max(exponent_of(q) for q in operands)
    precision = 300 + fmt.fw + 3 * largest
    if name in SATURATING:
        precision += 4 * min(int(abs(operands[0])), 1 << 14) + 8
    with mpmath.workprec(precision):
        value = function(*[to_mpf(q) for q in operands])
        sign, mantissa, exponent, bits = mpmath.mpf(value)._mpf_
        if mantissa != 0 and exponent + bits > fmt.bias + 4:
            return (-1 if sign else 1) * Fraction(2) ** (fmt.bias + 3)
        if mantissa != 0 and exponent + bits < fmt.emin - fmt.fw - 4:
            return (-1 if sign else 1) * Fraction(2) ** (fmt.emin - fmt.fw - 5)
        return to_fraction(value)


def evaluate(fmt, function, operands, name=""):
    """Round `function(*operands)` into the format: encoding and flags."""
    return fmt.round(exact_value(fmt, function, operands, name))


def power_of(base, value):
    """The integer `k` with `value = base ^ k`, for a positive rational, or None."""
    k = 0
    if value >= 1:
        while value > 1 and k < 5000:
            value /= base
            k += 1
        return k if value == 1 else None
    while value < 1 and k > -5000:
        value *= base
        k -= 1
    return k if value == 1 else None


def exact_unary(fmt, name, q):
    """The exact rational value of a function at `q` when it is rational and cheap to form."""
    if name in ("exp2", "exp10", "exp2m1", "exp10m1") and q.denominator == 1 and abs(q) <= 4 * fmt.bias + 64:
        power = Fraction(2 if name in ("exp2", "exp2m1") else 10) ** q.numerator
        return power - 1 if name.endswith("m1") else power
    if name in ("log2", "log10", "log2p1", "log10p1"):
        argument = q + 1 if name.endswith("p1") else q
        if argument > 0:
            k = power_of(Fraction(2 if name.startswith("log2") else 10), argument)
            if k is not None:
                return Fraction(k)
    if name == "asinPi" and abs(q) == 1:
        return q / 2
    if name == "acosPi" and q in (-1, 0, 1):
        return Fraction(1 - q, 2)
    if name == "atanPi" and abs(q) == 1:
        return q / 4
    if name == "tanPi" and q.denominator == 4:
        return Fraction(1 if q.numerator % 4 == 1 else -1)
    if name == "sinPi" and q.denominator == 2:
        return Fraction(1 if q.numerator % 4 == 1 else -1)
    if name == "cosPi" and q.denominator == 1:
        return Fraction(1 if q.numerator % 2 == 0 else -1)
    return None


def nan():
    return "nan"


def floor_root(value, degree):
    """The largest integer `r` with `r ^ degree <= value`, for a nonnegative integer."""
    if value < 2:
        return value
    low, high = 0, 1 << (value.bit_length() // degree + 1)
    while low < high:
        middle = (low + high + 1) // 2
        if middle ** degree <= value:
            low = middle
        else:
            high = middle - 1
    return low


def integer_root(value, degree):
    """The nonnegative integer `r` with `r ^ degree = value`, or None."""
    root = floor_root(value, degree)
    return root if root ** degree == value else None


def root_value(fmt, radicand, degree):
    """A rational that rounds like the positive `degree`-th root of a positive rational in
    every direction: the root itself when it is rational. An irrational root lies strictly
    between two neighbours of a binary grid that has every value of the format near the root
    and every midpoint of two of them, with the unbounded exponent range too, so the midpoint
    of the two neighbours rounds like the root. The neighbours are found with integers, so the
    radicand `x^2 + y^2` of `hypot` keeps a term of any size."""
    numerator = integer_root(radicand.numerator, degree)
    denominator = integer_root(radicand.denominator, degree)
    if numerator is not None and denominator is not None:
        return Fraction(numerator, denominator)
    magnitude = radicand.numerator.bit_length() - radicand.denominator.bit_length()
    shift = max(0, fmt.fw + 8 - magnitude // degree)
    below = floor_root((radicand.numerator << (degree * shift)) // radicand.denominator, degree)
    return Fraction(2 * below + 1, 1 << (shift + 1))


def rsqrt(fmt, operand):
    if operand[0] == "nan":
        return nan(), INVALID if operand[1] else 0
    if operand[0] == "inf":
        return (nan(), INVALID) if operand[1] else (fmt.zero(False), 0)
    _, negative, q = operand
    if q == 0:
        return fmt.infinity(negative), DIVIDE_BY_ZERO
    if q < 0:
        return nan(), INVALID
    return fmt.round(root_value(fmt, 1 / q, 2))


def rootn(fmt, operand, degree):
    if operand[0] == "nan":
        return nan(), INVALID if operand[1] else 0
    if degree == 0:
        return nan(), INVALID
    odd = degree % 2 == 1
    negative = operand[1] and odd
    if operand[0] == "inf":
        if operand[1] and not odd:
            return nan(), INVALID
        return (fmt.zero(negative), 0) if degree < 0 else (fmt.infinity(negative), 0)
    q = operand[2]
    if q == 0:
        return (fmt.infinity(negative), DIVIDE_BY_ZERO) if degree < 0 else (fmt.zero(negative), 0)
    if q < 0 and not odd:
        return nan(), INVALID
    magnitude = root_value(fmt, 1 / abs(q) if degree < 0 else abs(q), abs(degree))
    return fmt.round(-magnitude if q < 0 else magnitude)


def pown(fmt, operand, exponent):
    if operand[0] == "nan":
        if exponent == 0 and not operand[1]:
            return fmt.round(Fraction(1))
        return nan(), INVALID if operand[1] else 0
    if exponent == 0:
        return fmt.round(Fraction(1))
    negative = operand[1] and exponent % 2 == 1
    if operand[0] == "inf":
        return (fmt.zero(negative), 0) if exponent < 0 else (fmt.infinity(negative), 0)
    q = operand[2]
    if q == 0:
        return (fmt.infinity(negative), DIVIDE_BY_ZERO) if exponent < 0 else (fmt.zero(negative), 0)
    return fmt.round(q ** exponent)


def hypot(fmt, x, y):
    if (x[0] == "nan" and x[1]) or (y[0] == "nan" and y[1]):
        return nan(), INVALID
    if x[0] == "inf" or y[0] == "inf":
        return fmt.infinity(False), 0
    if x[0] == "nan" or y[0] == "nan":
        return nan(), 0
    if x[2] == 0 and y[2] == 0:
        return fmt.zero(False), 0
    return fmt.round(root_value(fmt, x[2] * x[2] + y[2] * y[2], 2))


def unary(fmt, name, operand):
    """Expected (result, flags) of a function of one operand."""
    if name == "rSqrt":
        return rsqrt(fmt, operand)
    if name == "cbrt":
        return rootn(fmt, operand, 3)
    if operand[0] == "nan":
        return nan(), INVALID if operand[1] else 0
    if operand[0] == "inf":
        negative = operand[1]
        if name in ("exp", "exp2", "exp10"):
            return (fmt.zero(False), 0) if negative else (fmt.infinity(False), 0)
        if name in ("expm1", "exp2m1", "exp10m1"):
            return fmt.round(Fraction(-1)) if negative else (fmt.infinity(False), 0)
        if name in ("log", "log2", "log10", "logp1", "log2p1", "log10p1", "acosh"):
            return (nan(), INVALID) if negative else (fmt.infinity(False), 0)
        if name in ("sinh", "asinh"):
            return fmt.infinity(negative), 0
        if name == "cosh":
            return fmt.infinity(False), 0
        if name == "tanh":
            return fmt.round(Fraction(-1 if negative else 1))
        if name == "atan":
            with mpmath.workprec(400 + fmt.fw):
                return fmt.round(to_fraction(-mpmath.pi / 2 if negative else mpmath.pi / 2))
        if name == "atanPi":
            return fmt.round(Fraction(-1 if negative else 1, 2))
        return nan(), INVALID
    _, negative, q = operand
    if q == 0 and name in ODD_AT_ZERO:
        return fmt.zero(negative), 0
    if name in ("log", "log2", "log10"):
        if q == 0:
            return fmt.infinity(True), DIVIDE_BY_ZERO
        if q < 0:
            return nan(), INVALID
    if name in ("logp1", "log2p1", "log10p1"):
        if q == -1:
            return fmt.infinity(True), DIVIDE_BY_ZERO
        if q < -1:
            return nan(), INVALID
    if name in ("asin", "acos", "asinPi", "acosPi") and abs(q) > 1:
        return nan(), INVALID
    if name == "acosh" and q < 1:
        return nan(), INVALID
    if name == "atanh":
        if abs(q) == 1:
            return fmt.infinity(q < 0), DIVIDE_BY_ZERO
        if abs(q) > 1:
            return nan(), INVALID
    if name == "sinPi" and q.denominator == 1:
        return fmt.zero(negative), 0
    if name == "cosPi" and q.denominator == 2:
        return fmt.zero(False), 0
    if name == "tanPi":
        if q.denominator == 1:
            n = q.numerator
            return fmt.zero((n > 0) == (n % 2 == 1)), 0
        if q.denominator == 2:
            n = (q.numerator - 1) // 2
            return fmt.infinity(n % 2 == 1), DIVIDE_BY_ZERO
    exact = exact_unary(fmt, name, q)
    if exact is not None:
        return fmt.round(exact)
    value = exact_value(fmt, REAL[name], [q], name)
    # No finite operand reaches the limits: `tanh x` is never 1 or -1, and `2 ^ x - 1` and
    # `10 ^ x - 1` are never -1. When the working precision no longer shows the difference, the
    # value is moved strictly inside the limit, so that it rounds like the true value.
    if name in SATURATING and abs(value) == 1 and (name == "tanh" or q < 0):
        value *= 1 - Fraction(1, 1 << (fmt.fw + 16))
    return fmt.round(value)


def sign_of(operand):
    return operand[1]


def is_zero(operand):
    return operand[0] == "fin" and operand[2] == 0


def angle(fmt, half_turns, y, x):
    """atan2 (y, x) or atan2Pi (y, x)."""
    if y[0] == "nan" or x[0] == "nan":
        return nan(), INVALID if (y[0] == "nan" and y[1]) or (x[0] == "nan" and x[1]) else 0

    def of_pi(numerator, denominator, negative):
        factor = Fraction(-numerator if negative else numerator, denominator)
        if half_turns:
            return fmt.round(factor)
        with mpmath.workprec(400 + fmt.fw):
            return fmt.round(to_fraction(mpmath.pi * factor.numerator / factor.denominator))

    negative = sign_of(y)
    x_negative = sign_of(x) if (x[0] == "inf" or is_zero(x)) else x[2] < 0
    if is_zero(y):
        return of_pi(1, 1, negative) if x_negative else (fmt.zero(negative), 0)
    if is_zero(x):
        return of_pi(1, 2, negative)
    if y[0] == "inf":
        if x[0] == "inf":
            return of_pi(3, 4, negative) if x_negative else of_pi(1, 4, negative)
        return of_pi(1, 2, negative)
    if x[0] == "inf":
        return of_pi(1, 1, negative) if x_negative else (fmt.zero(negative), 0)
    if half_turns:
        if abs(y[2]) == abs(x[2]):
            return of_pi(3 if x[2] < 0 else 1, 4, negative)
        return evaluate(fmt, lambda b, a: mpmath.atan2(b, a) / mpmath.pi, [y[2], x[2]])
    return evaluate(fmt, mpmath.atan2, [y[2], x[2]])


def powr(fmt, x, y):
    if x[0] == "nan" or y[0] == "nan":
        return nan(), INVALID if (x[0] == "nan" and x[1]) or (y[0] == "nan" and y[1]) else 0
    y_negative = sign_of(y) if (y[0] == "inf" or is_zero(y)) else y[2] < 0
    if x[0] == "inf":
        if sign_of(x) or is_zero(y):
            return nan(), INVALID
        return (fmt.zero(False), 0) if y_negative else (fmt.infinity(False), 0)
    base = x[2]
    if base < 0:
        return nan(), INVALID
    if base == 0:
        if is_zero(y):
            return nan(), INVALID
        if y[0] == "inf":
            return (fmt.infinity(False), 0) if y_negative else (fmt.zero(False), 0)
        return (fmt.infinity(False), DIVIDE_BY_ZERO) if y_negative else (fmt.zero(False), 0)
    if y[0] == "inf":
        if base == 1:
            return nan(), INVALID
        return (fmt.infinity(False), 0) if (base > 1) != y_negative else (fmt.zero(False), 0)
    return fmt.round(positive_power(fmt, base, y[2]))


def positive_power(fmt, base, exponent):
    """A rational that rounds like `base ^ exponent` in every direction, for a positive base."""
    value = exact_value(fmt, mpmath.power, [base, exponent])
    # `base ^ (a / 2^j)` is a value `r` of the format exactly when `base ^ a = r ^ (2^j)`. The
    # candidate is the value nearest to the computed power.
    j = exponent.denominator.bit_length() - 1
    nearest, flags = fmt.round(value, "E")
    # An overflow is not a value of the format, and a format without an infinity has no encoding
    # to decode for it.
    if (flags & OVERFLOW) == 0 and j <= 12 and abs(exponent.numerator) <= 4096:
        candidate = fmt.decode(nearest)
        if candidate[0] == "fin" and candidate[2] > 0 and \
                base ** exponent.numerator == candidate[2] ** (1 << j):
            return candidate[2]
    return value


def power(fmt, x, y):
    """pow (x, y) with the special cases of IEEE 754-2019 9.2.1."""
    x_signaling = x[0] == "nan" and x[1]
    y_signaling = y[0] == "nan" and y[1]
    if is_zero(y) and not x_signaling:
        return fmt.round(Fraction(1))
    if x[0] == "fin" and x[2] == 1 and not y_signaling:
        return fmt.round(Fraction(1))
    if x[0] == "nan" or y[0] == "nan":
        return nan(), INVALID if x_signaling or y_signaling else 0
    y_negative = sign_of(y) if y[0] == "inf" else y[2] < 0
    y_odd = y[0] == "fin" and y[2].denominator == 1 and y[2].numerator % 2 == 1
    if x[0] == "inf":
        negative = sign_of(x) and y_odd
        return (fmt.zero(negative), 0) if y_negative else (fmt.infinity(negative), 0)
    base = x[2]
    if base == 0:
        if y[0] == "inf":
            return (fmt.infinity(False), 0) if y_negative else (fmt.zero(False), 0)
        negative = sign_of(x) and y_odd
        return (fmt.infinity(negative), DIVIDE_BY_ZERO) if y_negative else (fmt.zero(negative), 0)
    if y[0] == "inf":
        if abs(base) == 1:
            return fmt.round(Fraction(1))
        return (fmt.infinity(False), 0) if (abs(base) > 1) != y_negative else (fmt.zero(False), 0)
    if base > 0:
        return fmt.round(positive_power(fmt, base, y[2]))
    if y[2].denominator != 1:
        return nan(), INVALID
    magnitude = positive_power(fmt, -base, y[2])
    return fmt.round(-magnitude if y_odd else magnitude)


def compound(fmt, x, n):
    if x[0] == "nan":
        if n == 0 and not x[1]:
            return fmt.round(Fraction(1))
        return nan(), INVALID if x[1] else 0
    if x[0] == "inf":
        if sign_of(x):
            return nan(), INVALID
        if n == 0:
            return fmt.round(Fraction(1))
        return (fmt.infinity(False), 0) if n > 0 else (fmt.zero(False), 0)
    rate = x[2]
    if rate < -1:
        return nan(), INVALID
    if rate == -1:
        if n == 0:
            return fmt.round(Fraction(1))
        return (fmt.infinity(False), DIVIDE_BY_ZERO) if n < 0 else (fmt.zero(False), 0)
    return fmt.round((1 + rate) ** n)


def show(result):
    return result if result == "nan" else format(result, "x")


def emit(name, fmt, x, y, expected):
    result, flags = expected
    if result == "nan" and fmt.kind == "finite":
        # A format without a NaN delivers `+0` for an invalid operation.
        result = 0
    print(f"fun {name} {fmt.name} {fmt.mode} {x:x} {y} {show(result)} {flags}")


def random_operand(rng, fmt, moderate, limit=None):
    """A pseudo-random encoding: any encoding, or a value of moderate magnitude. With `limit`,
    an encoding whose magnitude is `2 ^ limit` or more is replaced by a moderate one."""
    if not moderate:
        bits = rng.getrandbits(fmt.width)
        exponent = (bits >> fmt.fw) & ((1 << fmt.ew) - 1)
        if limit is None or exponent - fmt.bias < limit:
            return bits
    exponent = fmt.bias + rng.randint(-min(8, fmt.bias - 1), min(8, fmt.bias))
    return (rng.getrandbits(1) << (fmt.ew + fmt.fw)) | (exponent << fmt.fw) | rng.getrandbits(fmt.fw)


# binary64 operands of magnitude about 2^586, 2^800 and the largest finite value.
LARGE = (0x6490000000000000, 0xF1F123456789ABCD, 0x7FEFFFFFFFFFFFFF)


def binary_cases(fmt, a, b):
    """The functions of two operands at one pair of encodings."""
    x, y = fmt.decode(a), fmt.decode(b)
    emit("atan2", fmt, a, format(b, "x"), angle(fmt, False, x, y))
    emit("atan2Pi", fmt, a, format(b, "x"), angle(fmt, True, x, y))
    emit("powr", fmt, a, format(b, "x"), powr(fmt, x, y))
    emit("pow", fmt, a, format(b, "x"), power(fmt, x, y))
    emit("hypot", fmt, a, format(b, "x"), hypot(fmt, x, y))


def integer_cases(fmt, bits):
    """`rootn` and `pown` at one encoding."""
    for degree in DEGREES:
        emit("rootn", fmt, bits, degree, rootn(fmt, fmt.decode(bits), degree))
    for exponent in EXPONENTS:
        emit("pown", fmt, bits, exponent, pown(fmt, fmt.decode(bits), exponent))


def main():
    count, seed = int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    tiny = Format("e3f2")
    small = [Format(name) for name in ("e4f3", "e5m2", "e4m3", "e4m3fnuz", "e5m2fnuz", "e2m1")]
    for mode in "EAZUD":
        tiny.mode = mode
        for fmt in small:
            fmt.mode = mode
            for bits in range(1 << fmt.width):
                for name in UNARY:
                    emit(name, fmt, bits, "-", unary(fmt, name, fmt.decode(bits)))
                integer_cases(fmt, bits)
        for fmt in (tiny, small[-1]):
            fmt.mode = mode
            for a in range(1 << fmt.width):
                for b in range(1 << fmt.width):
                    binary_cases(fmt, a, b)
        for a in range(1 << tiny.width):
            integer_cases(tiny, a)
            for n in (-40, -7, -3, -2, -1, 0, 1, 2, 3, 5, 8, 21, 60):
                emit("compound", tiny, a, n, compound(tiny, tiny.decode(a), n))
    for fmt in small[:-1]:
        for index in range(50 * count):
            fmt.mode = "EAZUD"[rng.randrange(5)]
            binary_cases(fmt, rng.getrandbits(fmt.width), rng.getrandbits(fmt.width))
            a = rng.getrandbits(fmt.width)
            n = rng.randint(-12, 12)
            emit("compound", fmt, a, n, compound(fmt, fmt.decode(a), n))
    for format_name in ("binary16", "binary32", "binary64"):
        fmt = Format(format_name)
        for name in UNARY:
            # The exact comparators of sine, cosine and tangent reduce their argument by exact
            # enclosures of pi, which takes about a minute beyond 2^500. The random operands
            # stay below 2^400, and LARGE has three operands beyond it for each function.
            limit = 400 if name in ("sin", "cos", "tan") else None
            for index in range(count):
                fmt.mode = "EAZUD"[rng.randrange(5)]
                bits = random_operand(rng, fmt, index % 2 == 0, limit)
                emit(name, fmt, bits, "-", unary(fmt, name, fmt.decode(bits)))
            if limit is not None and format_name == "binary64" and count >= 100:
                for position, bits in enumerate(LARGE):
                    fmt.mode = "EZU"[position]
                    emit(name, fmt, bits, "-", unary(fmt, name, fmt.decode(bits)))
        for index in range(count):
            fmt.mode = "EAZUD"[rng.randrange(5)]
            a = random_operand(rng, fmt, index % 2 == 0)
            b = random_operand(rng, fmt, index % 4 < 2)
            binary_cases(fmt, a, b)
            n = rng.randint(-60, 60)
            emit("compound", fmt, a, n, compound(fmt, fmt.decode(a), n))
            degree = rng.randint(-9, 9)
            emit("rootn", fmt, a, degree, rootn(fmt, fmt.decode(a), degree))
            exponent = rng.randint(-40, 40)
            emit("pown", fmt, a, exponent, pown(fmt, fmt.decode(a), exponent))


if __name__ == "__main__":
    main()
