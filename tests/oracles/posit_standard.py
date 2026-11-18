"""Check public posit observations against SoftPosit pX2 and signed-word order.

SoftPosit's fixed posit8 and posit16 types predate the 2022 es=2 requirement.
Only the generic pX2 family is used here. Every observed result must have the
canonical zero padding of its left-aligned 32-bit carrier.
"""

import argparse
from collections import Counter
import csv
from functools import lru_cache
import importlib.metadata
import json
from pathlib import Path

import softposit


@lru_cache(None)
def operand(width, word):
    result = softposit.posit_2_t()
    result.v = word << (32 - width)
    return result


def compact(width, result):
    padding = 32 - width
    if result.v & ((1 << padding) - 1):
        raise ValueError("SoftPosit returned a noncanonical left-aligned word")
    return result.v >> padding


def signed(width, word):
    return word if word < (1 << (width - 1)) else word - (1 << width)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("observations", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    counts, mismatches = Counter(), []
    next_unary = {width: 0 for width in range(2, 9)}
    next_binary = {width: 0 for width in range(2, 9)}
    with args.observations.open(newline="") as stream:
        for row in csv.reader(stream):
            kind, width_text, a_text, *tail = row
            width, a = int(width_text), int(a_text)
            x = operand(width, a)
            if kind == "U":
                if a != next_unary[width]:
                    raise ValueError(f"Missing, reordered or duplicate unary row: {row}")
                next_unary[width] += 1
                actual = list(map(int, tail))
                names = ["negate", "nearestInt", "sqrt"]
                expected = [
                    (-a) % (1 << width),
                    compact(width, softposit.pX2_roundToInt(x, width)),
                    compact(width, softposit.pX2_sqrt(x, width)),
                ]
            elif kind == "B":
                b = int(tail[0])
                if a * (1 << width) + b != next_binary[width]:
                    raise ValueError(f"Missing, reordered or duplicate binary row: {row}")
                next_binary[width] += 1
                actual = list(map(int, tail[1:]))
                y, one_ulp = operand(width, b), operand(width, 1)
                names = [
                    "addition", "subtraction", "multiplication", "division", "fma",
                    "compareEqual", "compareNotEqual", "compareGreater",
                    "compareGreaterEqual", "compareLess", "compareLessEqual",
                ]
                expected = [
                    compact(width, f(x, y, width)) for f in (
                        softposit.pX2_add, softposit.pX2_sub,
                        softposit.pX2_mul, softposit.pX2_div,
                    )
                ]
                expected.append(compact(width, softposit.pX2_mulAdd(x, y, one_ulp, width)))
                sa, sb = signed(width, a), signed(width, b)
                expected.extend([sa == sb, sa != sb, sa > sb, sa >= sb, sa < sb, sa <= sb])
                # These three operations also have independent SoftPosit entry points.
                for name, actual_value, expected_value in [
                    ("softposit_compareEqual", actual[5], softposit.pX2_eq(x, y)),
                    ("softposit_compareLess", actual[9], softposit.pX2_lt(x, y)),
                    ("softposit_compareLessEqual", actual[10], softposit.pX2_le(x, y)),
                ]:
                    counts[name] += 1
                    if actual_value != expected_value:
                        mismatches.append({"input": row[:4], "operation": name,
                                           "actual": actual_value, "expected": expected_value})
            else:
                raise ValueError(f"Unknown row type: {kind}")
            if len(actual) != len(expected):
                raise ValueError(f"Wrong result count: {row}")
            for name, actual_value, expected_value in zip(names, actual, expected):
                counts[name] += 1
                if actual_value != expected_value:
                    inputs = row[:3] if kind == "U" else row[:4]
                    mismatches.append({"input": inputs, "operation": name,
                                       "actual": actual_value, "expected": int(expected_value)})
    for width in range(2, 9):
        if next_unary[width] != 1 << width or next_binary[width] != 1 << (2 * width):
            raise ValueError(f"Incomplete width {width}")
    # One difference from the reference is known, and a permanent Lean proof fixes
    # FloatLib's word for it. Preserve the raw difference; accepting it never masks a
    # different word or result.
    known_difference = {
        "input": ["U", "8", "129"], "operation": "nearestInt", "actual": 129, "expected": 127,
    }
    unexplained = [row for row in mismatches if row != known_difference]
    known_differences = []
    if known_difference in mismatches:
        known_differences.append({
            "difference": known_difference,
            "correct_word": 129,
            "reason": "The word denotes the integer -2^24, which nearestInt must fix.",
            "lean_proof": "tests/FloatLibTests/Conformance/Posit/Standard.lean",
        })
    result = {
        "reference": f"softposit {importlib.metadata.version('softposit')}",
        "reference_family": "pX2, es=2, left-aligned 32-bit carrier",
        "document": "Posit Standard (2022)",
        "clauses": ["4.1", "5.2", "5.3", "5.4", "5.5"],
        "widths": list(range(2, 9)),
        "cases": counts,
        "mismatches": len(mismatches),
        "unexplained_mismatches": len(unexplained),
        "first_mismatches": mismatches[:20],
        "known_differences": known_differences,
        "status": ("fail" if unexplained else
                   "pass-with-known-difference" if mismatches else "pass"),
        "limitations": [
            "FMA enumerates both multiplicands with the third word fixed at minpos.",
            "This corpus covers thirteen standard operations and FloatLib's FMA extension.",
            "No comparison with legacy es=0 posit8 or es=1 posit16 is made.",
        ],
    }
    args.result.parent.mkdir(parents=True, exist_ok=True)
    args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if unexplained:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
