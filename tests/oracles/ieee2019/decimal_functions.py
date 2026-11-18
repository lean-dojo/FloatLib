#!/usr/bin/env python3
"""Reference results for the certified decimal functions of IEEE 754-2019 clause 9.2.

usage: decimal_functions.py PACKAGES COUNT SEED

PACKAGES is a directory that holds the Python package `mpmath`. The script writes one case per
line for `oracle ieee2019 check`:

    dfun NAME PRECISION X EXPECTED

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
FORMATS = {7: (-95, 96), 16: (-383, 384), 34: (-6143, 6144)}
UNIT = {"asin", "acos", "asinPi", "acosPi", "atanh"}
POSITIVE = {"log2", "log10", "log2p1", "log10p1", "log"}
REAL = dict(functions.REAL, exp=mpmath.exp, log=mpmath.log)


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


def main():
    count, seed = int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    for precision, (emin, emax) in FORMATS.items():
        mpmath.mp.dps = 4 * precision + 60
        for name in list(functions.UNARY) + ["exp", "log"]:
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
