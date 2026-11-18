"""OCP MX §§6.1–6.2 finite intermediates against exact decoding and MPFR.

Product precision, accumulator precision and output precision are independent.
Each exact product is rounded into its product format, cast to the accumulator,
and added to the accumulator in stored order. DotGeneral must retain that state
across block boundaries. Exceptional outputs are compared by class and sign;
NaN payloads are outside this rational stored-dot contract.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import math
from pathlib import Path
import platform
import random
import struct
import subprocess

import gmpy2

from block_formats import run_oracle
from mx_dot import PROFILES, decode, rows_for


def file_hash(path):
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def rounded(value, width):
    """Round an exact finite fraction with MPFR's IEEE subnormal context."""
    if isinstance(value, float):
        return value
    with gmpy2.context(gmpy2.ieee(width)):
        result = gmpy2.mpfr(gmpy2.mpq(value.numerator, value.denominator))
    if not gmpy2.is_finite(result):
        return float(result)
    numerator, denominator = result.as_integer_ratio()
    return Fraction(int(numerator), int(denominator))


def extended_binary(operation, left, right):
    if isinstance(left, float) or isinstance(right, float):
        return operation(float(left), float(right))
    return operation(left, right)


def output_word(value, width):
    """Encode the final rounding, preserving negative zero from underflow."""
    if isinstance(value, float):
        delivered = value
    else:
        with gmpy2.context(gmpy2.ieee(width)):
            delivered = gmpy2.mpfr(gmpy2.mpq(value.numerator, value.denominator))
    if math.isnan(float(delivered)):
        return None
    code, integer = {16: ("e", "H"), 32: ("f", "I"), 64: ("d", "Q")}[width]
    return struct.unpack("<" + integer, struct.pack("<" + code, float(delivered)))[0]


def finite_dot(left, right, row, product_width, accumulator_width, output_width):
    total = Fraction(0)
    for offset in range(0, len(row), 66):
        sl, sr = row[offset:offset + 2]
        for lane in range(32):
            a = decode(left, sl, row[offset + 2 + 2 * lane])
            b = decode(right, sr, row[offset + 3 + 2 * lane])
            product = extended_binary(lambda x, y: x * y, a, b)
            projected = rounded(rounded(product, product_width), accumulator_width)
            total = rounded(
                extended_binary(lambda x, y: x + y, total, projected), accumulator_width)
    return output_word(total, output_width)


def is_nan(bits, width):
    exponent, fraction = {16: (5, 10), 32: (8, 23), 64: (11, 52)}[width]
    return ((bits >> fraction) & ((1 << exponent) - 1)) == (1 << exponent) - 1 \
        and bits & ((1 << fraction) - 1) != 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--product", type=int, choices=[16, 32, 64], required=True)
    parser.add_argument("--accumulator", type=int, choices=[16, 32, 64], required=True)
    parser.add_argument("--output", type=int, choices=[16, 32, 64], required=True)
    parser.add_argument("--count", type=int, default=64)
    parser.add_argument("--seed", type=int, default=20261116)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    cases, differences = [], []
    inputs_hash, observations_hash = hashlib.sha256(), hashlib.sha256()
    for left in PROFILES:
        for right in PROFILES:
            rows = list(rows_for(left, right, rng, args.count))
            actual = run_oracle(args.oracle, [
                "finite-dot", left, right, str(args.product), str(args.accumulator),
                str(args.output)], rows)
            for index, (row, result) in enumerate(zip(rows, actual, strict=True)):
                if result is None or result[0] or len(result[1]) != 2 or result[2]:
                    raise RuntimeError("Malformed or rejected Lean finite-dot observation")
                inputs_hash.update(json.dumps([left, right, row]).encode() + b"\n")
                observations_hash.update(json.dumps(result[1]).encode() + b"\n")
                expected = finite_dot(
                    left, right, row, args.product, args.accumulator, args.output)
                for operation, found in zip(("Dot", "DotGeneral"), result[1], strict=True):
                    good = is_nan(found, args.output) if expected is None else found == expected
                    if not good:
                        differences.append(dict(
                            left=left, right=right, row=index, operation=operation,
                            input=row, expected=expected, actual=found))
            cases.append(dict(left=left, right=right, rows=len(rows), comparisons=2 * len(rows)))
    report = dict(
        document="OCP MX v1.0, §§6.1–6.2",
        source_commit=subprocess.check_output([
            "git", "-C", str(Path(__file__).resolve().parents[2]), "rev-parse", "HEAD"
        ], text=True).strip(),
        gfloat=importlib.metadata.version("gfloat"),
        gmpy2=gmpy2.version(), mpfr=gmpy2.mpfr_version(), python=platform.python_version(),
        producer_sha256=file_hash(Path(args.oracle)),
        checker_sha256={name: file_hash(Path(__file__).with_name(name)) for name in
                        ["mx_finite_dot.py", "mx_dot.py", "block_formats.py"]},
        product_width=args.product, accumulator_width=args.accumulator, output_width=args.output,
        seed=args.seed, random_rows_per_pair=args.count, cases=cases,
        comparisons=sum(case["comparisons"] for case in cases),
        input_sha256=inputs_hash.hexdigest(), observations_sha256=observations_hash.hexdigest(),
        differences=differences, unexplained_mismatches=len(differences),
        status="pass" if not differences else "fail",
        scope=[
            "All FP4 and both FP6 code pairs in constant 32-element blocks.",
            "All FP8 and INT8 codes paired with five representative partners.",
            "All 36 ordered profile pairs, with one to three blocks.",
            "NaN scales, signed infinities, zero products, overflow and cancellation.",
            "Nearest-even product rounding, accumulator cast and each ordered addition.",
            "DotGeneral retains the same accumulator across block boundaries.",
            "One final rounding of the decoded accumulator to the independent output format.",
            "This finite corpus does not prove the universal finite-range hypotheses.",
        ])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in (
        "status", "comparisons", "unexplained_mismatches",
        "product_width", "accumulator_width", "output_width")}))
    raise SystemExit(bool(differences))


if __name__ == "__main__":
    main()
