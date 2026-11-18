"""Compare compiled P3109 queries with gfloat 0.5.2.

The inputs are observations from P3109Queries.lean, not trusted certificates.
Every descriptor and code at widths 3..8 is checked; total order is exhaustive
at widths 3..5. At these widths gfloat's binary64 observations are exact.
"""

import argparse
import csv
from fractions import Fraction
import importlib.metadata
import json
import math
from pathlib import Path

from gfloat import decode_float
from gfloat.formats import format_info_p3109
from gfloat.types import Domain, FloatClass, Signedness


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("observations", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    formats = {}
    values = {}
    counts = {"value": 0, "order": 0}
    mismatches = []
    with args.observations.open(newline="") as stream:
        for row in csv.reader(stream):
            kind, width, precision, signedness, domain, *data = row
            key = (int(width), int(precision), signedness, domain)
            if key not in formats:
                formats[key] = format_info_p3109(
                    key[0], key[1],
                    Signedness.Signed if signedness.endswith(".signed") else Signedness.Unsigned,
                    Domain.Finite if domain.endswith(".finite") else Domain.Extended,
                )
                values[key] = [decode_float(formats[key], code) for code in range(2 ** key[0])]
            counts[kind] += 1
            if kind == "value":
                code, actual_class, actual_value = data
                reference = values[key][int(code)]
                if reference.fclass == FloatClass.NAN:
                    expected_class, expected_value = "ClsNaN", "nan"
                elif reference.fclass == FloatClass.ZERO:
                    expected_class, expected_value = "ClsZero", Fraction(0)
                else:
                    sign = "Negative" if reference.signbit else "Positive"
                    category = {
                        FloatClass.NORMAL: "Normal",
                        FloatClass.SUBNORMAL: "Subnormal",
                        FloatClass.INFINITE: "Infinity",
                    }[reference.fclass]
                    expected_class = f"Cls{sign}{category}"
                    expected_value = (
                        ("-inf" if reference.signbit else "inf")
                        if reference.fclass == FloatClass.INFINITE
                        else Fraction.from_float(reference.fval)
                    )
                observed = actual_value if actual_value in {"nan", "inf", "-inf"} else Fraction(actual_value)
                good = actual_class.endswith("." + expected_class) and observed == expected_value
            elif kind == "order":
                left, right, actual = data
                x, y = values[key][int(left)].fval, values[key][int(right)].fval
                expected = math.isnan(x) or (not math.isnan(y) and x <= y)
                good = actual == str(expected).lower()
            else:
                raise ValueError(f"Unknown observation kind: {kind}")
            if not good:
                mismatches.append(row)
    result = {
        "reference": f"gfloat {importlib.metadata.version('gfloat')}",
        "document": "P3109 interim report v4.1, 14 September 2026, unapproved draft",
        "clauses": ["4.12.1", "4.13.1"],
        "formats": len(formats),
        "cases": counts,
        "mismatches": len(mismatches),
        "first_mismatches": mismatches[:10],
        "status": "pass" if not mismatches else "fail",
    }
    args.result.parent.mkdir(parents=True, exist_ok=True)
    args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
