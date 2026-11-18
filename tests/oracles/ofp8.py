"""OFP8 r1: strict corpus validation against independent gfloat encodings.

All source values and midpoint neighbours are exact in binary64. NaN payload
and sign are deliberately compared by class, as OFP8 5.2.1 leaves them free.
Signed zeros and every non-NaN destination code are compared exactly.
"""

import argparse
import csv
from fractions import Fraction
import importlib.metadata
import itertools
import json
import math
from pathlib import Path
import struct

from gfloat import decode_float, encode_float, round_float
from gfloat.formats import format_info_ocp_e4m3, format_info_ocp_e5m2

FORMATS = {"e4m3": format_info_ocp_e4m3, "e5m2": format_info_ocp_e5m2}


def binary32(word):
    return struct.unpack(">f", struct.pack(">I", word))[0]


def word32(value):
    return struct.unpack(">I", struct.pack(">f", value))[0]


def boundary_words():
    words = set()
    for fmt in FORMATS.values():
        positive = [decode_float(fmt, code).fval for code in range(128)]
        positive = sorted({x for x in positive if math.isfinite(x)})
        # Add the next precision-grid point beyond the last finite encoding.
        positive.append(positive[-1] + positive[-1] - positive[-2])
        points = positive + [(a + b) / 2 for a, b in zip(positive, positive[1:])]
        for value in points:
            for sign in (1, -1):
                code = word32(sign * value)
                words.update(c for c in (code - 1, code, code + 1) if 0 <= c < 2**32)
    for sign, exponent, fraction in itertools.product(
        (0, 1), range(256), (0, 1, 2**22 - 1, 2**22, 2**23 - 2, 2**23 - 1)
    ):
        words.add((sign << 31) | (exponent << 23) | fraction)
    return sorted(words)


def source_value(source, word):
    if source == "binary16":
        return struct.unpack(">e", struct.pack(">H", word))[0]
    return binary32(word if source == "binary32" else word << 16)


def expected_rows(words):
    for name in FORMATS:
        for code in range(256):
            yield ["decode", name, str(code)]
    for source in ("binary16", "bfloat16"):
        for word in range(65536):
            yield [source, str(word)]
    for word in words:
        yield ["binary32", str(word)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prepare", type=Path)
    parser.add_argument("--observations", type=Path)
    parser.add_argument("--words", type=Path)
    parser.add_argument("--result", type=Path)
    args = parser.parse_args()
    if args.prepare:
        words = boundary_words()
        args.prepare.write_text(json.dumps(words) + "\n")
        print(f"Prepared {len(words)} exact binary32 boundary words")
        return
    words = json.loads(args.words.read_text())
    if words != boundary_words():
        raise ValueError("binary32 corpus differs from the declared construction")
    counts = {"decode": 0, "binary16": 0, "bfloat16": 0, "binary32": 0}
    differences = []
    mismatch_count = 0
    with args.observations.open(newline="") as stream:
        for expected, row in itertools.zip_longest(expected_rows(words), csv.reader(stream)):
            if expected is None or row is None or row[:len(expected)] != expected:
                raise ValueError(f"missing, extra or reordered corpus row: {expected}, {row}")
            if row[0] == "decode":
                if len(row) != 5:
                    raise ValueError(row)
                _, name, code, sign, actual = row
                ref = decode_float(FORMATS[name], int(code))
                if math.isnan(ref.fval):
                    good = actual == "nan"
                elif math.isinf(ref.fval):
                    good = actual == "inf" and (sign == "true") == ref.signbit
                else:
                    good = Fraction(actual) == Fraction(float(ref.fval)) and (sign == "true") == ref.signbit
                comparisons = [("decode", good, actual, repr(ref.fval))]
            else:
                if len(row) != 6:
                    raise ValueError(row)
                source, word, *outputs = row
                value = source_value(source, int(word))
                comparisons = []
                for (name, fmt), pair in zip(FORMATS.items(), (outputs[:2], outputs[2:])):
                    for saturation, actual in zip((True, False), pair):
                        reference = round_float(fmt, value, sat=saturation)
                        code = int(actual)
                        if not 0 <= code < 256:
                            raise ValueError(row)
                        good = (math.isnan(decode_float(fmt, code).fval) if math.isnan(reference)
                                else code == encode_float(fmt, reference))
                        comparisons.append((f"{name}:{'SAT' if saturation else 'NONSAT'}",
                                            good, code, repr(reference)))
            for operation, good, actual, expected in comparisons:
                counts[row[0]] += 1
                if not good:
                    mismatch_count += 1
                    if len(differences) < 20:
                        differences.append({"input": row[:3] if row[0] == "decode" else row[:2],
                                            "operation": operation, "actual": actual, "expected": expected})
    report = {
        "document": "OCP OFP8 revision 1.0 (2023-12-01)", "clauses": ["5.1", "5.2.1"],
        "reference": f"gfloat {importlib.metadata.version('gfloat')}",
        "coverage": "All binary16 and bfloat16 words, both destinations, both saturation modes",
        "binary32_words": len(words), "comparisons": counts,
        "mismatches": mismatch_count, "first_mismatches": differences,
        "status": "pass" if mismatch_count == 0 else "fail",
        "limitations": ["Binary32 is a boundary and exponent-stratified corpus, not exhaustive.",
                        "NaN sign and payload are compared by class, as the standard permits.",
                        "FloatLib status fields are not required by OFP8 and are not compared here."]}
    args.result.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if mismatch_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
