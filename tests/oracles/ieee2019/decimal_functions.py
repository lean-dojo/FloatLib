#!/usr/bin/env python3
"""Reference results for the decimal functions of IEEE 754-2019 clause 9.2.

usage: decimal_functions.py PACKAGES COUNT SEED

PACKAGES is a directory that holds the Python package `mpmath`. The script writes one case per
line for `oracle ieee2019 check`, of two kinds:

    dfun NAME PRECISION X EXPECTED
    dtot NAME PRECISION MODE X Y EXPECTED FLAGS

The `dtot` lines are for the total functions of `Transcendentals.CorrectlyRounded`, which
return a datum with flags in each rounding direction. MODE is `E`, `A`, `Z`, `U` or `D` as for
the binary functions, Y is `-` for a function of one operand, a datum for `powr`, `pow`,
`atan2` and `atan2Pi` (in the order of the call) and the integer `n` for `compound`. EXPECTED
is a datum, `i,SIGN` for an infinity, and FLAGS the sum of invalid 1, divideByZero 2,
overflow 4, underflow 8 and inexact 16. For each function and format there are COUNT
pseudo-random operands, each in the five directions: the 26 functions of one argument, `exp`,
`expm1`, `log`, `logp1`, and `powr`, `pow` (a negative base with an integral exponent
included), `atan2`, `atan2Pi` and `compound`. `exp`, `exp2`, `exp10`, `expm1` and `sinh` also
get COUNT operands at each end of the exponent range, where the result is subnormal or zero
with `underflow`, or beyond the largest finite value with `overflow`. EXPECTED is the value
that `mpmath` computes with four times the precision of the format and 60 digits more, rounded
here in the direction of the case onto the grid of the format with exact rational arithmetic:
the quantum exponent is the least possible one, a result below the least normal magnitude is
rounded at the least quantum exponent with `underflow`, and a rounded magnitude beyond the
largest finite one gives the overflow result of the direction. An integral power is computed
exactly with rationals, and every other result is taken to be inexact.

The `dfun` lines are for the certified functions:

NAME is the name of the function in the standard, PRECISION the number of digits of the format
(7, 16 or 34), and X and EXPECTED are data in the form `f,SIGN,COEFFICIENT,EXPONENT`. For each of
the 26 functions of one argument, for `exp` and for `log`, and for each format, there are COUNT
pseudo-random operands with a full coefficient and a magnitude between 1/1000 and 100, inside
the domain of the function
(below 1 for the inverse sine, cosine and hyperbolic tangent, at least 1 for the inverse
hyperbolic cosine, positive for the logarithms). EXPECTED is the value that `mpmath` computes
with four times the precision of the format and 60 digits more, rounded here to the precision
of the format, to nearest with ties to even, with exact rational arithmetic. A case whose
result is not a normal number of the format is left out.

FloatLib returns a result only when an enclosure settles the rounding, so the oracle counts a
case without a result separately and compares the value of every result that is returned.
"""
import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import functions  # noqa: E402  (reads PACKAGES from sys.argv[1] and imports mpmath)

mpmath = functions.mpmath
# The decimal128 results near the ends of the exponent range have more than 6,000 digits.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
FORMATS = {7: (-95, 96), 16: (-383, 384), 34: (-6143, 6144)}
UNIT = {"asin", "acos", "asinPi", "acosPi", "atanh"}
POSITIVE = {"log2", "log10", "log2p1", "log10p1", "log"}
REAL = functions.REAL
# The 26 functions of one argument of the decimal table; `exp`, `expm1`, `log` and `logp1` are
# definitions of their own, and the binary list `functions.UNARY` also has `rSqrt` and `cbrt`.
UNARY = [name for name in REAL if name not in ("exp", "expm1", "log", "logp1")]


def round_decimal(value: Fraction, precision: int):
    """Sign, coefficient of `precision` digits and exponent of `value` rounded to nearest-even."""
    sign, magnitude = value < 0, abs(value)
    exponent = len(str(magnitude.numerator)) - len(str(magnitude.denominator))
    while Fraction(10) ** exponent > magnitude:
        exponent -= 1
    while Fraction(10) ** (exponent + 1) <= magnitude:
        exponent += 1
    scaled = magnitude / Fraction(10) ** (exponent - precision + 1)
    coefficient, rest = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * rest
    if twice > scaled.denominator or (twice == scaled.denominator and coefficient % 2 == 1):
        coefficient += 1
    if coefficient == 10 ** precision:
        coefficient //= 10
        exponent += 1
    return sign, coefficient, exponent - precision + 1, exponent


def datum(sign, coefficient, exponent):
    return f"f,{int(sign)},{coefficient},{exponent}"


def round_directed(value: Fraction, precision: int, emin: int, emax: int, mode: str, exact: bool):
    """Datum and flags of `value` rounded in the direction `mode` onto the grid of a format
    with `precision` digits and decimal exponents from `emin` to `emax`. `exact` says that
    `value` is the exact result; otherwise the result is inexact whatever `value` is."""
    sign, magnitude = value < 0, abs(value)
    least, largest = emin - precision + 1, emax - precision + 1
    exponent = len(str(magnitude.numerator)) - len(str(magnitude.denominator))
    while Fraction(10) ** exponent > magnitude:
        exponent -= 1
    while Fraction(10) ** (exponent + 1) <= magnitude:
        exponent += 1
    quantum = max(exponent - precision + 1, least)
    scaled = magnitude / Fraction(10) ** quantum
    coefficient, rest = divmod(scaled.numerator, scaled.denominator)
    inexact = rest != 0 or not exact
    twice = 2 * rest
    if mode == "E":
        up = twice > scaled.denominator or (twice == scaled.denominator and coefficient % 2 == 1)
    elif mode == "A":
        up = twice >= scaled.denominator
    else:
        up = rest != 0 and ((mode == "U" and not sign) or (mode == "D" and sign))
    if up:
        coefficient += 1
    if coefficient == 10 ** precision:
        coefficient //= 10
        quantum += 1
    if quantum > largest:
        to_infinity = mode in ("E", "A") or (mode == "U" and not sign) or (mode == "D" and sign)
        result = f"i,{int(sign)}" if to_infinity else datum(sign, 10 ** precision - 1, largest)
        return result, 4 + 16
    tiny = magnitude < Fraction(10) ** emin
    return datum(sign, coefficient, quantum), (16 if inexact else 0) + (8 if tiny and inexact else 0)


def operand(rng, precision, low, high, negative=False):
    """A pseudo-random operand with a full coefficient and a decade from `low` to `high`."""
    coefficient = rng.randrange(10 ** (precision - 1), 10 ** precision)
    exponent = rng.randrange(low, high + 1) - precision
    value = Fraction(-coefficient if negative else coefficient) * Fraction(10) ** exponent
    return value, datum(negative, coefficient, exponent)


def high_precision(function, *arguments):
    return functions.to_fraction(function(*[mpmath.mpf(q.numerator) / mpmath.mpf(q.denominator)
                                             for q in arguments]))


# The base whose power a function of the exponential family is, for operands near the ends of
# the exponent range.
EXTREME = {"exp": mpmath.e, "exp2": 2, "exp10": 10, "expm1": mpmath.e, "sinh": mpmath.e}


def saturated(name, precision, x, value):
    """No finite operand reaches the limits: `tanh x` is never 1 or -1, and `exp x - 1`,
    `2 ^ x - 1` and `10 ^ x - 1` are never -1. When the working precision no longer shows the
    difference, the value is moved strictly inside the limit, so that it rounds like the true
    value in every direction."""
    if abs(value) == 1 and (name == "tanh" or (name in ("expm1", "exp2m1", "exp10m1") and x < 0)):
        return value * (1 - Fraction(1, 10 ** (precision + 20)))
    return value


def emit_total(name, precision, x, y, value, emin, emax, exact=False):
    for mode in "EAZUD":
        result, flags = round_directed(value, precision, emin, emax, mode, exact)
        print("dtot", name, precision, mode, x, y, result, flags)


def total_cases(rng, count):
    for precision, (emin, emax) in FORMATS.items():
        mpmath.mp.dps = 4 * precision + 60
        for name in UNARY + ["exp", "expm1", "log", "logp1"]:
            for _ in range(count):
                if name in UNIT:
                    low, high = -2, 0
                elif name == "acosh":
                    low, high = 1, 2
                else:
                    low, high = -2, 2
                positive = name in POSITIVE or name in ("acosh", "logp1")
                x, text = operand(rng, precision, low, high, not positive and rng.random() < 0.5)
                value = saturated(name, precision, x, high_precision(REAL[name], x))
                if value != 0:
                    emit_total(name, precision, text, "-", value, emin, emax)
        for name, base in EXTREME.items():
            scale = mpmath.log(10) / mpmath.log(base)
            for decade, negative in ((emax, False), (emin - precision // 2, True)):
                for _ in range(count):
                    target = (abs(decade) + rng.uniform(-1.5, 1.5)) * scale
                    digits = Fraction(int(target * 10 ** 6), 10 ** 6)
                    exponent = len(str(digits.numerator)) - len(str(digits.denominator))
                    while Fraction(10) ** exponent > digits:
                        exponent -= 1
                    quantum = exponent - precision + 1
                    coefficient = int(digits / Fraction(10) ** quantum)
                    if name == "sinh" and negative:
                        continue
                    x = Fraction(-coefficient if negative else coefficient) * Fraction(10) ** quantum
                    value = saturated(name, precision, x, high_precision(REAL[name], x))
                    if value != 0:
                        emit_total(name, precision, datum(negative, coefficient, quantum), "-", value,
                                   emin, emax)
        for _ in range(count):
            base, base_text = operand(rng, precision, -2, 2)
            exponent, exponent_text = operand(rng, precision, -2, 1, rng.random() < 0.5)
            value = high_precision(mpmath.power, base, exponent)
            emit_total("powr", precision, base_text, exponent_text, value, emin, emax)
            emit_total("pow", precision, base_text, exponent_text, value, emin, emax)
            n = rng.randrange(-12, 13)
            negative_base = Fraction(-rng.randrange(1, 10 ** min(precision, 4)), 10 ** rng.randrange(0, 3))
            emit_total("pow", precision,
                       datum(True, -negative_base.numerator * (10 ** 2 // negative_base.denominator), -2),
                       datum(n < 0, abs(n), 0), negative_base ** n, emin, emax, exact=True)
            y, y_text = operand(rng, precision, -2, 2, rng.random() < 0.5)
            x, x_text = operand(rng, precision, -2, 2, rng.random() < 0.5)
            angle = high_precision(mpmath.atan2, y, x)
            emit_total("atan2", precision, y_text, x_text, angle, emin, emax)
            emit_total("atan2Pi", precision, y_text, x_text,
                       high_precision(lambda b, a: mpmath.atan2(b, a) / mpmath.pi, y, x), emin, emax)
            rate, rate_text = operand(rng, precision, -3, 0, rng.random() < 0.5)
            n = rng.randrange(-40, 41)
            emit_total("compound", precision, rate_text, n, (1 + rate) ** n, emin, emax, exact=True)


def main():
    count, seed = int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    total_cases(random.Random(seed + 1), count)
    for precision, (emin, emax) in FORMATS.items():
        mpmath.mp.dps = 4 * precision + 60
        for name in UNARY + ["exp", "log"]:
            written = 0
            while written < count:
                coefficient = rng.randrange(10 ** (precision - 1), 10 ** precision)
                if name in UNIT:
                    decade = rng.randrange(-2, 1)
                elif name == "acosh":
                    decade = rng.randrange(1, 3)
                else:
                    decade = rng.randrange(-2, 3)
                exponent = decade - precision
                negative = name not in POSITIVE and name != "acosh" and rng.random() < 0.5
                x = Fraction(-coefficient if negative else coefficient) * Fraction(10) ** exponent
                argument = mpmath.mpf(x.numerator) / mpmath.mpf(x.denominator)
                result = REAL[name](argument)
                value = functions.to_fraction(result)
                if value == 0:
                    continue
                sign, digits, quantum, leading = round_decimal(value, precision)
                if not emin <= leading <= emax:
                    continue
                print("dfun", name, precision, datum(negative, coefficient, exponent), datum(sign, digits, quantum))
                written += 1


if __name__ == "__main__":
    main()
