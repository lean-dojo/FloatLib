#!/usr/bin/env python3
"""Reference results for the operations of IEEE 754-2019 that FloatLib added in 2026-11.

The script writes one case per line for `oracle ieee2019`, which compares FloatLib with them.
Every reference is independent of FloatLib:

* decimal addition, subtraction and multiplication with their flags, and `max`, `min`,
  `max_mag`, `min_mag`: Python's `decimal` module (libmpdec), in an IEEE interchange context
  (`clamp=1`) of decimal32, decimal64 or decimal128 and the five rounding directions;
* the augmented operations, `sumAbs`, `sumSquare` and `scaledProd` on binary64: exact rational
  arithmetic with `fractions.Fraction`, rounded by CPython's correctly rounded conversion of a
  fraction to a float, with the tie rule of roundTiesTowardZero applied on top for the
  augmented operations. `sumAbs` is also compared with `math.fsum` here.

* the decimal reductions `sum`, `sumAbs`, `sumSquare` and `dot`: the terms are added without
  rounding in a `decimal` context of 26,000 digits, and the exact sum is rounded once, with its
  flags, by the interchange context.

* the decimal scaled products `scaledProd`, `scaledProdSum` and `scaledProdDiff`: the factors
  and their product are formed without rounding in such a context, the scale factor is the
  adjusted exponent of the exact product, and the scaled product is rounded once by the
  interchange context. The special cases (NaN, infinite and invalid factors) follow ISO/IEC TS
  18661-4 F.10.10a.5 to F.10.10a.7 directly;
* the decimal reductions from left to right in an accumulator format: a chain of additions of
  `decimal` in the accumulator's interchange context, whose flags accumulate, and a conversion
  to the destination's context.

usage: reference.py KIND COUNT SEED
       (KIND: decimal | extrema | augmented | reductions | decimal-reductions | decimal-scaled
        | decimal-ordered)

Line formats (fields separated by one space):

  dec OP PRECISION MODE X Y R FLAGS       OP add|sub|mul, MODE E|A|Z|U|D
  ext OP PRECISION X Y R                  OP max|min|maxmag|minmag
  aug OP X Y HEAD TAIL FLAGS              OP add|sub|mul, binary64 words in hexadecimal
  red OP N X1 ... XN R                    OP sumabs|sumsq
  red scaledprod N X1 ... XN PR SF
  dred OP PRECISION MODE N X1 ... XN R FLAGS          OP sum|sumabs|sumsq
  dred dot PRECISION MODE N X1 ... XN Y1 ... YN R FLAGS
  dsp scaledprod PRECISION MODE N X1 ... XN PR SF FLAGS
  dsp OP PRECISION MODE N X1 ... XN Y1 ... YN PR SF FLAGS     OP scaledprodsum|scaledproddiff
  dord OP ACCUMULATOR PRECISION MODE N X1 ... XN R FLAGS      OP sum|sumabs|sumsq
  dord dot ACCUMULATOR PRECISION MODE N X1 ... XN Y1 ... YN R FLAGS

A decimal datum is `f,SIGN,COEFFICIENT,EXPONENT`, `i,SIGN` or `n,SIGN,SIGNALING,PAYLOAD`.
FLAGS is the sum of invalid 1, divideByZero 2, overflow 4, underflow 8 and inexact 16.
"""
import decimal
import math
import random
import struct
import sys
from fractions import Fraction

FORMATS = {7: (96, -95), 16: (384, -383), 34: (6144, -6143)}
MODES = {"E": decimal.ROUND_HALF_EVEN, "A": decimal.ROUND_HALF_UP, "Z": decimal.ROUND_DOWN,
         "U": decimal.ROUND_CEILING, "D": decimal.ROUND_FLOOR}


def context(precision, mode="E"):
    emax, emin = FORMATS[precision]
    return decimal.Context(prec=precision, rounding=MODES[mode], Emin=emin, Emax=emax, clamp=1,
                           traps=[])


def datum(value):
    sign, digits, exponent = value.as_tuple()
    if exponent == "F":
        return f"i,{sign}"
    if exponent in ("n", "N"):
        payload = int("".join(map(str, digits)) or "0")
        return f"n,{sign},{1 if exponent == 'N' else 0},{payload}"
    return f"f,{sign},{int(''.join(map(str, digits)))},{exponent}"


def flags(ctx):
    table = [(decimal.InvalidOperation, 1), (decimal.DivisionByZero, 2), (decimal.Overflow, 4),
             (decimal.Underflow, 8), (decimal.Inexact, 16)]
    return sum(bit for signal, bit in table if ctx.flags[signal])


def random_finite(rng, precision):
    emax, _ = FORMATS[precision]
    lowest, highest = -(emax + precision - 2), emax - precision + 1
    kind = rng.randrange(10)
    if kind == 0:
        coefficient = 0
    elif kind < 4:
        coefficient = rng.randrange(10 ** rng.randrange(1, precision + 1))
    elif kind < 7:
        coefficient = rng.randrange(10 ** (precision - 1), 10 ** precision)
    else:
        coefficient = rng.choice([1, 5, 10 ** (precision - 1), 10 ** precision - 1,
                                  5 * 10 ** (precision - 1)])
    where = rng.randrange(10)
    if where < 5:
        exponent = rng.randrange(-2 * precision, 2 * precision)
    elif where < 7:
        exponent = rng.randrange(lowest, lowest + 3 * precision)
    elif where < 9:
        exponent = rng.randrange(highest - 3 * precision, highest + 1)
    else:
        exponent = rng.randrange(lowest, highest + 1)
    digits = tuple(map(int, str(coefficient)))
    return decimal.Decimal((rng.randrange(2), digits, exponent))


def random_special(rng, precision, signaling=True):
    kind = rng.randrange(3 if signaling else 2)
    sign = rng.randrange(2)
    if kind == 0:
        return decimal.Decimal((sign, (), "F"))
    payload = tuple(map(int, str(rng.randrange(10 ** (precision - 1)))))
    return decimal.Decimal((sign, payload, "N" if kind == 2 else "n"))


def decimal_cases(count, rng):
    operations = {"add": "add", "sub": "subtract", "mul": "multiply"}
    for index in range(count):
        precision = rng.choice([7, 16, 34])
        mode = rng.choice("EAZUD")
        x = random_finite(rng, precision)
        y = random_finite(rng, precision)
        if index % 4 == 1:
            # Exponents close together, so that alignment keeps most digits.
            shift = rng.randrange(-precision - 2, precision + 3)
            _, emin = FORMATS[precision]
            exponent = min(max(x.as_tuple().exponent + shift, emin - precision + 1),
                           FORMATS[precision][0] - precision + 1)
            y = decimal.Decimal((y.as_tuple().sign, y.as_tuple().digits, exponent))
        if index % 29 == 0:
            x = random_special(rng, precision)
        elif index % 31 == 0:
            y = random_special(rng, precision)
        if x.is_nan() and y.is_nan():
            continue
        name = rng.choice(list(operations))
        ctx = context(precision, mode)
        result = getattr(ctx, operations[name])(x, y)
        print("dec", name, precision, mode, datum(x), datum(y), datum(result), flags(ctx))


def extrema_cases(count, rng):
    operations = {"max": "max", "min": "min", "maxmag": "max_mag", "minmag": "min_mag"}
    for index in range(count):
        precision = rng.choice([7, 16, 34])
        x = random_finite(rng, precision)
        y = random_finite(rng, precision)
        if index % 3 == 0:
            # A member of the cohort of x, or its negation.
            sign, digits, exponent = x.as_tuple()
            coefficient = int("".join(map(str, digits)))
            while coefficient % 10 == 0 and coefficient != 0 and rng.randrange(2):
                coefficient //= 10
                exponent += 1
            emax, _ = FORMATS[precision]
            if exponent <= emax - precision + 1:
                y = decimal.Decimal((rng.choice([sign, sign, 1 - sign]),
                                     tuple(map(int, str(coefficient))), exponent))
        if index % 17 == 0:
            x = random_special(rng, precision, signaling=False)
        elif index % 19 == 0:
            y = random_special(rng, precision, signaling=False)
        if x.is_nan() and y.is_nan():
            continue
        name = rng.choice(list(operations))
        ctx = context(precision)
        result = getattr(ctx, operations[name])(x, y)
        print("ext", name, precision, datum(x), datum(y), datum(result))


def bits(value):
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def from_bits(word):
    return struct.unpack("<d", struct.pack("<Q", word))[0]


MAX = from_bits(0x7FEFFFFFFFFFFFFF)
OVERFLOW_MIDPOINT = Fraction(MAX) + Fraction(2) ** 970


def nearest_even(exact):
    """Correctly rounded binary64 value of a fraction, or None when it overflows."""
    if abs(exact) >= OVERFLOW_MIDPOINT:
        return None
    return exact.numerator / exact.denominator


def ties_toward_zero(exact):
    """roundTiesTowardZero of a nonzero fraction to binary64: (value, overflowed)."""
    if abs(exact) > OVERFLOW_MIDPOINT:
        return (math.inf if exact > 0 else -math.inf), True
    if abs(exact) == OVERFLOW_MIDPOINT:
        return (MAX if exact > 0 else -MAX), False
    rounded = nearest_even(exact)
    if Fraction(rounded) == exact:
        return rounded, False
    other = math.nextafter(rounded, -math.inf if Fraction(rounded) > exact else math.inf)
    # Beyond the largest finite value the neighbour is an infinity, and the tie was handled above.
    if (math.isfinite(other) and abs(Fraction(rounded) - exact) == abs(Fraction(other) - exact)
            and abs(other) < abs(rounded)):
        rounded = other
    if rounded == 0:
        rounded = zero(exact < 0)
    return rounded, False


def zero(negative):
    return -0.0 if negative else 0.0


def augmented(name, x, y):
    """Head, tail and flags of an augmented operation on finite binary64 operands."""
    sign_x, sign_y = math.copysign(1, x) < 0, math.copysign(1, y) < 0
    if name == "sub":
        sign_y = not sign_y
        y = -y
    exact = Fraction(x) * Fraction(y) if name == "mul" else Fraction(x) + Fraction(y)
    if exact == 0:
        result = zero((sign_x != sign_y) if name == "mul" else (sign_x and sign_y))
        return result, result, 0
    head, overflowed = ties_toward_zero(exact)
    if overflowed:
        return head, head, 4 + 16
    error = exact - Fraction(head)
    if error == 0:
        return head, zero(exact < 0), 0
    tail, _ = ties_toward_zero(error)
    inexact = Fraction(tail) != error
    return head, tail, (8 + 16) if inexact else 0


def random_double(rng):
    kind = rng.randrange(12)
    if kind == 0:
        return rng.choice([0.0, -0.0, 1.0, -1.0, MAX, -MAX, 5e-324, -5e-324, 2.2250738585072014e-308])
    if kind < 4:
        word = rng.getrandbits(64)
        if (word >> 52) & 0x7FF == 0x7FF:
            word &= ~(1 << 62)
        return from_bits(word)
    if kind < 7:
        return math.ldexp(rng.getrandbits(53) | (1 << 52), rng.randrange(-70, 20)) * rng.choice([1, -1])
    if kind < 9:
        return float(rng.randrange(-1000, 1000)) * 2.0 ** rng.randrange(-6, 6)
    if kind == 9:
        return from_bits(rng.getrandbits(52) | (rng.randrange(0, 3) << 52)) * rng.choice([1, -1])
    if kind == 10:
        return math.ldexp(rng.getrandbits(53) | (1 << 52), rng.randrange(900, 972)) * rng.choice([1, -1])
    return math.ldexp(rng.getrandbits(53) | (1 << 52), rng.randrange(-600, -480)) * rng.choice([1, -1])


def augmented_cases(count, rng):
    for index in range(count):
        name = rng.choice(["add", "sub", "mul"])
        x = random_double(rng)
        y = random_double(rng)
        if index % 5 == 0 and name != "mul":
            # A tie: y is half a unit in the last place of x.
            y = math.ulp(x) / 2 * rng.choice([1, -1])
            if y == 0:
                continue
        if index % 7 == 0 and name == "mul":
            x = math.ldexp(rng.getrandbits(53) | (1 << 52), -52)
            y = math.ldexp(rng.getrandbits(26) | (1 << 25), rng.randrange(-30, 30))
        head, tail, status = augmented(name, x, y)
        print("aug", name, f"{bits(x):016x}", f"{bits(y):016x}", f"{bits(head):016x}",
              f"{bits(tail):016x}", status)


def reduction_cases(count, rng):
    for index in range(count):
        size = rng.randrange(0, 9)
        values = [random_double(rng) for _ in range(size)]
        if index % 3 == 0:
            values = [float(rng.randrange(-50, 50)) * 2.0 ** rng.randrange(-60, 60) for _ in range(size)]
        words = " ".join(f"{bits(value):016x}" for value in values)
        kind = index % 3
        if kind == 0:
            exact = sum(abs(Fraction(value)) for value in values)
            rounded = nearest_even(exact)
            if rounded is None:
                rounded = math.inf
            elif all(abs(value) < 1e300 for value in values):
                assert math.fsum(abs(value) for value in values) == rounded
            print("red sumabs", size, words, f"{bits(rounded):016x}")
        elif kind == 1:
            exact = sum(Fraction(value) ** 2 for value in values)
            rounded = nearest_even(exact)
            if rounded is None:
                rounded = math.inf
            print("red sumsq", size, words, f"{bits(rounded):016x}")
        else:
            product = Fraction(1)
            negative = False
            for value in values:
                product *= Fraction(value)
                negative ^= math.copysign(1, value) < 0
            if product == 0:
                print("red scaledprod", size, words, f"{bits(zero(negative)):016x}", 0)
                continue
            scale = abs(product).numerator.bit_length() - abs(product).denominator.bit_length()
            if abs(product) < Fraction(2) ** scale:
                scale -= 1
            scaled = nearest_even(product / Fraction(2) ** scale)
            print("red scaledprod", size, words, f"{bits(scaled):016x}", scale)


def decimal_reduction_cases(count, rng):
    for index in range(count):
        precision = rng.choice([7, 16, 34])
        mode = rng.choice("EAZUD")
        name = rng.choice(["sum", "sumabs", "sumsq", "dot"])
        size = rng.randrange(0, 6)
        xs = [random_finite(rng, precision) for _ in range(size)]
        ys = [random_finite(rng, precision) for _ in range(size)]
        if index % 3 == 0 and size > 1:
            # Exponents close to the first operand, and one exact cancellation in three.
            for position in range(1, size):
                sign, digits, exponent = xs[position].as_tuple()
                shifted = xs[0].as_tuple().exponent + rng.randrange(-precision, precision + 1)
                low, high = -(FORMATS[precision][0] + precision - 2), FORMATS[precision][0] - precision + 1
                xs[position] = decimal.Decimal((sign, digits, min(max(shifted, low), high)))
            if index % 9 == 0:
                xs[-1] = xs[0].copy_negate()
        # Exact arithmetic: enough digits for the whole exponent range of decimal128, twice.
        exact = decimal.Context(prec=26000, rounding=MODES[mode], Emin=-999999, Emax=999999, traps=[])
        if name == "sum":
            terms = xs
        elif name == "sumabs":
            terms = [x.copy_abs() for x in xs]
        elif name == "sumsq":
            terms = [exact.multiply(x, x) for x in xs]
        else:
            terms = [exact.multiply(x, y) for x, y in zip(xs, ys)]
        total = decimal.Decimal(0)
        for position, term in enumerate(terms):
            total = term if position == 0 else exact.add(total, term)
        if exact.flags[decimal.Inexact] or exact.flags[decimal.Rounded]:
            raise SystemExit("the exact context rounded a sum")
        ctx = context(precision, mode)
        result = ctx.plus(total)
        if total.is_zero():
            # `plus` is `0 + total`, which makes a zero positive. The sign of an exact zero sum
            # is that of the chain of additions, which the exact context has computed.
            result = result.copy_sign(total)
        operands = [datum(x) for x in xs] + ([datum(y) for y in ys] if name == "dot" else [])
        print("dred", name, precision, mode, size, *operands, datum(result), flags(ctx))


def exact_context(mode):
    """A context that adds and multiplies decimal128 data without rounding."""
    return decimal.Context(prec=80000, rounding=MODES[mode], Emin=-999999999, Emax=999999999,
                           traps=[])


def scaled_factor(exact, name, x, y):
    """One factor of a scaled product: ("nan", datum, signaling), ("invalid",), ("inf", sign)
    or ("finite", value)."""
    operands = [x] if name == "scaledprod" else [x, y]
    nans = [operand for operand in operands if operand.is_nan()]
    if nans:
        return ("nan", nans[0], any(operand.is_snan() for operand in nans))
    if name == "scaledproddiff":
        operands[1] = operands[1].copy_negate()
    infinite = [operand for operand in operands if operand.is_infinite()]
    if len(infinite) == 2 and infinite[0].is_signed() != infinite[1].is_signed():
        return ("invalid",)
    if infinite:
        return ("inf", infinite[0].is_signed())
    return ("finite", operands[0] if len(operands) == 1 else exact.add(*operands))


def decimal_scaled_cases(count, rng):
    for index in range(count):
        precision = rng.choice([7, 16, 34])
        mode = rng.choice("EAZUD")
        name = rng.choice(["scaledprod", "scaledprodsum", "scaledproddiff"])
        size = rng.randrange(0, 6)
        xs = [random_finite(rng, precision) for _ in range(size)]
        ys = [random_finite(rng, precision) for _ in range(size)]
        low, high = -(FORMATS[precision][0] + precision - 2), FORMATS[precision][0] - precision + 1
        if index % 3 == 0:
            # Exponents of a pair close together, so that a sum keeps digits of both operands.
            for position in range(size):
                sign, digits, _ = ys[position].as_tuple()
                shifted = xs[position].as_tuple().exponent + rng.randrange(-precision, precision + 1)
                ys[position] = decimal.Decimal((sign, digits, min(max(shifted, low), high)))
        if index % 12 == 0 and size:
            # One factor that is an exact zero by cancellation.
            ys[0] = xs[0] if name == "scaledproddiff" else xs[0].copy_negate()
        if index % 7 == 0 and size:
            xs[rng.randrange(size)] = random_special(rng, precision)
        if index % 11 == 0 and size:
            ys[rng.randrange(size)] = random_special(rng, precision)
        exact = exact_context(mode)
        factors = [scaled_factor(exact, name, x, y) for x, y in zip(xs, ys)]
        finite = [factor[1] for factor in factors if factor[0] == "finite"]
        product = decimal.Decimal(1)
        for value in finite:
            product = exact.multiply(product, value)
        if exact.flags[decimal.Inexact] or exact.flags[decimal.Rounded]:
            raise SystemExit("the exact context rounded a product")
        negative = product.is_signed()
        for factor in factors:
            if factor[0] == "inf":
                negative ^= factor[1]
        infinite = any(factor[0] == "inf" for factor in factors)
        invalid = any(factor[0] == "invalid" for factor in factors) or (infinite and product.is_zero())
        nans = [factor for factor in factors if factor[0] == "nan"]
        ctx = context(precision, mode)
        scale = 0
        if nans:
            sign, digits, _ = nans[0][1].as_tuple()
            payload = int("".join(map(str, digits)) or "0")
            result = f"n,{sign},0,{payload}"
            status = 1 if invalid or any(factor[2] for factor in nans) else 0
        elif invalid:
            result, status = "n,0,0,0", 1
        elif infinite:
            result, status = f"i,{int(negative)}", 0
        elif product.is_zero():
            result, status = datum(ctx.plus(product).copy_sign(product)), flags(ctx)
        else:
            scale = product.adjusted()
            result = datum(ctx.plus(exact.scaleb(product, -scale)))
            status = flags(ctx)
        operands = [datum(x) for x in xs] + ([] if name == "scaledprod" else [datum(y) for y in ys])
        print("dsp", name, precision, mode, size, *operands, result, scale, status)


def convert(ctx, value):
    """Conversion of a datum into the format of a context, with its flags."""
    result = ctx.plus(value)
    # `plus` is `0 + value`, which makes a zero positive.
    return result.copy_sign(value) if value.is_zero() else result


def decimal_ordered_cases(count, rng):
    for index in range(count):
        accumulator = rng.choice([7, 16, 34])
        precision = rng.choice([7, 16, 34])
        mode = rng.choice("EAZUD")
        name = rng.choice(["sum", "sumabs", "sumsq", "dot"])
        size = rng.randrange(0, 7)
        source = rng.choice([7, 16, 34])
        xs = [random_finite(rng, source) for _ in range(size)]
        ys = [random_finite(rng, source) for _ in range(size)]
        low, high = -(FORMATS[source][0] + source - 2), FORMATS[source][0] - source + 1
        if index % 2 == 0 and size > 1:
            # Exponents close to the first operand, so that the additions round.
            for values in (xs, ys):
                for position in range(1, size):
                    sign, digits, _ = values[position].as_tuple()
                    shifted = xs[0].as_tuple().exponent + rng.randrange(-source, source + 1)
                    values[position] = decimal.Decimal((sign, digits, min(max(shifted, low), high)))
            if index % 8 == 0:
                xs[-1] = xs[0].copy_negate()
        if index % 13 == 0 and size:
            xs[rng.randrange(size)] = decimal.Decimal((rng.randrange(2), (), "F"))
        acc = context(accumulator, mode)
        out = context(precision, mode)
        if name == "sum":
            terms = [convert(acc, x) for x in xs]
        elif name == "sumabs":
            terms = [convert(acc, x.copy_abs()) for x in xs]
        elif name == "sumsq":
            terms = [acc.multiply(convert(acc, x), convert(acc, x)) for x in xs]
        else:
            terms = [acc.multiply(convert(acc, x), convert(acc, y)) for x, y in zip(xs, ys)]
        if terms:
            total = terms[0]
            for term in terms[1:]:
                total = acc.add(total, term)
            result = convert(out, total)
        else:
            result = decimal.Decimal(0)
        operands = [datum(x) for x in xs] + ([datum(y) for y in ys] if name == "dot" else [])
        print("dord", name, accumulator, precision, mode, size, *operands, datum(result),
              flags(acc) | flags(out))


def main():
    kind, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    {"decimal": decimal_cases, "extrema": extrema_cases, "augmented": augmented_cases,
     "reductions": reduction_cases, "decimal-reductions": decimal_reduction_cases,
     "decimal-scaled": decimal_scaled_cases, "decimal-ordered": decimal_ordered_cases}[kind](count, rng)


if __name__ == "__main__":
    main()
