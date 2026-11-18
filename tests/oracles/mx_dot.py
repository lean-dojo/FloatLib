"""OCP MX §§6.1–6.2 exact dot observations against gfloat decoding and MPFR.

All products and sums are exact fractions. MPFR rounds the final rational
once in its IEEE binary32 context, including subnormal and overflow behavior.
This checks FloatLib's chosen exact-intermediate implementation; the standard
also permits other intermediate precisions.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
import json
import math
from pathlib import Path
import random
import struct

import gfloat
from gfloat import formats
import gmpy2

from block_formats import run_oracle


PROFILES = {
    name: getattr(formats, "format_info_" + descriptor).etype
    for name, descriptor in [
        ("e5m2", "mxfp8_e5m2"), ("e4m3", "mxfp8_e4m3"),
        ("e3m2", "mxfp6_e3m2"), ("e2m3", "mxfp6_e2m3"),
        ("e2m1", "mxfp4_e2m1"), ("int8", "mxint8"),
    ]
}


@lru_cache(maxsize=None)
def decode(profile, scale, code):
    if scale == 255:
        return math.nan
    value = float(gfloat.decode_float(PROFILES[profile], code).fval)
    if not math.isfinite(value):
        return value
    exponent = scale - 127
    factor = Fraction(2 ** exponent) if exponent >= 0 else Fraction(1, 2 ** -exponent)
    return Fraction(value) * factor


def exact_dot(left, right, row):
    total = Fraction(0)
    for offset in range(0, len(row), 66):
        sl, sr = row[offset:offset + 2]
        for lane in range(32):
            a = decode(left, sl, row[offset + 2 + 2 * lane])
            b = decode(right, sr, row[offset + 3 + 2 * lane])
            if isinstance(a, float) or isinstance(b, float):
                product = float(a) * float(b)
            else:
                product = a * b
            # A nonfinite product is handled in the extended reals. Finite
            # rational partial sums are never rounded or converted to float.
            if isinstance(total, float) or isinstance(product, float):
                total = float(total) + float(product)
            else:
                total += product
    if isinstance(total, float):
        rounded = total
    else:
        with gmpy2.context(gmpy2.ieee(32)):
            rounded = float(gmpy2.mpfr(gmpy2.mpq(total.numerator, total.denominator)))
    if math.isnan(rounded):
        return None
    return struct.unpack("<I", struct.pack("<f", rounded))[0]


def constant_block(a, b, sl=127, sr=127):
    return [sl, sr] + [a, b] * 32


def rows_for(left, right, rng, count):
    kl, kr = PROFILES[left].k, PROFILES[right].k
    if left == right:
        if kl <= 6:
            for a in range(2 ** kl):
                for b in range(2 ** kr):
                    yield constant_block(a, b)
        else:
            for a in range(2 ** kl):
                for b in [0, 1, 2 ** (kr - 2), 2 ** (kr - 1), 2 ** kr - 1]:
                    yield constant_block(a, b)
    # Every ordered profile pair, several block counts, and extreme scales.
    scales = [0, 1, 64, 120, 126, 127, 128, 134, 190, 253, 254, 255]
    for index in range(count):
        row = []
        for _ in range(1 + index % 3):
            sl, sr = rng.choice(scales), rng.choice(scales)
            row += [sl, sr]
            for _ in range(32):
                row += [rng.randrange(2 ** kl), rng.randrange(2 ** kr)]
        yield row
    # Opposite enormous block sums cancel before a small middle block is rounded.
    for scale in [0, 64, 127, 190, 254]:
        one_l = int(gfloat.encode_float(PROFILES[left], 1.0))
        minus_one_l = int(gfloat.encode_float(PROFILES[left], -1.0))
        one_r = int(gfloat.encode_float(PROFILES[right], 1.0))
        yield (constant_block(one_l, one_r, scale, scale)
               + constant_block(one_l, one_r)
               + constant_block(minus_one_l, one_r, scale, scale))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--count", type=int, default=64)
    parser.add_argument("--seed", type=int, default=20261116)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    cases, differences = [], []
    for left in PROFILES:
        for right in PROFILES:
            rows = list(rows_for(left, right, rng, args.count))
            actual = run_oracle(args.oracle, ["dot", left, right], rows)
            for index, (row, result) in enumerate(zip(rows, actual, strict=True)):
                if result is None or result[0] or len(result[1]) != 2 or result[2]:
                    raise RuntimeError("Malformed or rejected Lean dot observation")
                expected = exact_dot(left, right, row)
                for operation, found in zip(("Dot", "DotGeneral"), result[1], strict=True):
                    good = (found & 0x7F800000 == 0x7F800000 and
                            found & 0x7FFFFF != 0) if expected is None else found == expected
                    if not good:
                        differences.append({
                            "left": left, "right": right, "row": index,
                            "operation": operation, "input": row,
                            "expected": expected, "actual": found,
                        })
            cases.append({"left": left, "right": right, "rows": len(rows),
                          "comparisons": 2 * len(rows)})
    report = {
        "document": "OCP MX v1.0, §§6.1–6.2",
        "gfloat": "0.5.2", "gmpy2": gmpy2.version(), "mpfr": gmpy2.mpfr_version(),
        "seed": args.seed, "cases": cases,
        "comparisons": sum(case["comparisons"] for case in cases),
        "differences": differences, "unexplained_mismatches": len(differences),
        "status": "pass" if not differences else "fail",
        "scope": [
            "All FP4 and both FP6 code pairs in constant 32-element blocks.",
            "All FP8 and INT8 codes paired with five representative partners.",
            "All 36 ordered profile pairs, with one to three blocks.",
            "NaN scales, signed infinities, zero products, overflow and cancellation.",
            "Exact intermediates and one final binary32 rounding only.",
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                      ("status", "comparisons", "unexplained_mismatches")}))
    raise SystemExit(bool(differences))


if __name__ == "__main__":
    main()
