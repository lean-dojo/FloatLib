"""Exhaustive small-word block/scaled comparison with gfloat 0.5.2.

The independent closed arithmetic follows P3109 v4.1 §§4.10 and 5.7–5.8,
including NaN for every zero denominator. gfloat supplies source decoding,
destination rounding and destination encoding. Python binary64 is exact for
all finite additions and products in this small corpus. Finite quotients are
rounded to binary64 first; they are far more accurate than the 1–4-bit targets.
"""

import argparse
import csv
from functools import lru_cache
import importlib.metadata
import json
import math
from pathlib import Path

from gfloat import decode_float, encode_float, round_float
from gfloat.formats import format_info_p3109
from gfloat.types import Domain, Signedness


@lru_cache(None)
def descriptor(width, precision, extended):
    return format_info_p3109(width, precision, Signedness.Signed,
                             Domain.Extended if extended else Domain.Finite)


def closed(op, x, y):
    if op == "Add":
        return x + y
    if op == "Multiply":
        return x * y
    if op == "Divide":
        return math.nan if y == 0 else x / y
    if op == "FMA":
        return x * y + 0.5
    raise ValueError(op)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("observations", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    right_format = descriptor(3, 2, True)
    counts, formats, mismatches = {}, set(), []
    with args.observations.open(newline="") as stream:
        for row in csv.reader(stream):
            w, p, domain, a, b, scale, op, block, scaled = row
            fmt = descriptor(int(w), int(p), domain.endswith(".extended"))
            formats.add((w, p, domain))
            x = decode_float(fmt, int(a)).fval * int(scale)
            y = decode_float(right_format, int(b)).fval * 2
            exact = closed(op, x, y)
            for family, actual, normalized in (
                ("Block", int(block), exact / 2),
                ("Scaled", int(scaled), exact),
            ):
                name = family + op
                counts[name] = counts.get(name, 0) + 1
                expected = encode_float(fmt, round_float(fmt, normalized))
                if actual != expected:
                    mismatches.append({"input": row, "family": family, "expected": expected})
    result = {
        "reference": f"gfloat {importlib.metadata.version('gfloat')}",
        "document": "P3109 interim report v4.1, 14 September 2026, unapproved draft",
        "clauses": ["4.10.3", "4.10.4", "4.10.5", "4.10.6", "5.7", "5.8"],
        "descriptors": len(formats),
        "left_widths": [3, 4, 5],
        "right_descriptor": "binary3p2se",
        "left_scales": [0, 1, -2],
        "right_scale": 2,
        "block_result_scale": 2,
        "cases": counts,
        "mismatches": len(mismatches),
        "first_mismatches": mismatches[:10],
        "status": "pass" if not mismatches else "fail",
        "limitations": [
            "Finite division uses a binary64 oracle intermediate.",
            "Nearest-even and no saturation only; other policies have separate Lean tests.",
            "This corpus tests four operations, not the entire block operation inventory.",
        ],
    }
    args.result.parent.mkdir(parents=True, exist_ok=True)
    args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
