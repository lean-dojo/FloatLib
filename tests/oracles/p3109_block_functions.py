"""P3109 §§5.3–5.4 and §§5.7–5.8, with exact independent scale normalization.

Directed MPFR encloses the unrounded function. Exact Fraction division applies
the result scale before the independent report-formula projection. No rounded
scalar output is used as an intermediate. Exceptional normalization implements
the chapter 5 case table directly.
"""

import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess

from p3109_functions import binary, descriptor, MODE_COUNT, NAMES, precision_counts, unary


def sign(value):
    if isinstance(value, str):
        assert value in ("-inf", "+inf")
        return -1 if value == "-inf" else 1
    return (value > 0) - (value < 0)


def multiply(left, right):
    if left == "nan" or right == "nan":
        return "nan"
    if isinstance(left, str) or isinstance(right, str):
        if left == 0 or right == 0:
            return "nan"
        return "-inf" if sign(left) * sign(right) < 0 else "+inf"
    return left * right


class NormalizedTarget:
    def __init__(self, target, scale):
        self.target, self.scale = target, scale

    def project(self, value):
        scale = self.scale
        if scale == "nan" or value == "nan":
            normalized = "nan"
        elif scale == 0:
            normalized = F(0)
        elif isinstance(scale, str):
            normalized = F(sign(scale) * sign(value))
        elif isinstance(value, str):
            normalized = "-inf" if sign(scale) * sign(value) < 0 else "+inf"
        else:
            normalized = value / scale
        return self.target.project(normalized)

    def enclose(self, lower, upper, strict):
        scale = self.scale
        if scale == "nan":
            return self.target.project("nan")
        if scale == 0:
            return self.target.project(F(0))
        if isinstance(scale, str):
            if lower > 0 or strict and lower == 0 and upper > 0:
                value_sign = 1
            elif upper < 0 or strict and upper == 0 and lower < 0:
                value_sign = -1
            elif lower == upper == 0:
                value_sign = 0
            else:
                return None
            return self.target.project(F(sign(scale) * value_sign))
        bounds = sorted(F(*(int(x) for x in bound.as_integer_ratio())) / scale
                        for bound in (lower, upper))
        return self.target.enclose(*bounds, strict)


@lru_cache(None)
def normalized_target(target, scale):
    return NormalizedTarget(target, scale)


@lru_cache(None)
def expected_unary(target, scale, name, argument):
    return unary(normalized_target(target, scale), name, argument)


@lru_cache(None)
def expected_binary(target, scale, pi_scaled, y, x):
    return binary(normalized_target(target, scale), pi_scaled, y, x)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("producer", type=Path)
    parser.add_argument("report", type=Path)
    parser.add_argument("--profile", type=int, default=0)
    args = parser.parse_args()
    process = subprocess.Popen([str(args.producer.resolve()), str(args.profile)],
                               stdout=subprocess.PIPE)
    digest, counts, mismatches = hashlib.sha256(), Counter(), []
    scale_format = descriptor(8, 3, True, True)
    pairs = set()
    try:
        for raw in process.stdout:
            digest.update(raw)
            row = raw.decode().strip().split(",")
            if row[0] == "F":
                def read(start):
                    return descriptor(int(row[start]), int(row[start + 1]),
                                      row[start + 2] == "true", row[start + 3] == "true")
                source, target = read(1), read(5)
                pairs.add(tuple(row[1:]))
                continue
            kind, name = row[:2]
            input_scale = scale_format.decode(int(row[2]))
            result_scale = scale_format.decode(int(row[3])) if kind in ("U", "B") else F(1)
            argument = multiply(input_scale, source.decode(int(row[4])))
            if kind in ("U", "S"):
                expected = expected_unary(target, result_scale, name, argument)
                data_start = 5
            else:
                assert kind in ("B", "T")
                right = multiply(F(-2), scale_format.decode(int(row[5])))
                expected = expected_binary(target, result_scale, name == "ArcTan2Pi",
                                           argument, right)
                data_start = 6
            actual = list(map(int, row[data_start:]))
            assert len(actual) == MODE_COUNT * 3
            counts[kind + ":" + name] += 1
            if expected != actual and len(mismatches) < 20:
                mismatches.append({
                    "formats": [source.width, source.precision, source.signed, source.extended,
                                target.width, target.precision, target.signed, target.extended],
                    "input": row[:data_start],
                    "differences": [[i, a, b] for i, (a, b) in enumerate(zip(actual, expected))
                                    if a != b]})
    except BaseException:
        process.terminate()
        process.wait()
        raise
    code = process.wait()
    expected_counts = {
        **{"U:" + name: 2016 for name in NAMES},
        **{"S:" + name: 288 for name in NAMES},
        **{"B:" + name: 14112 for name in ("ArcTan2", "ArcTan2Pi")},
        **{"T:" + name: 2016 for name in ("ArcTan2", "ArcTan2Pi")},
    }
    coverage_complete = counts == expected_counts and len(pairs) == 2
    report = {
        "document": "P3109 v4.1, 14 September 2026, unapproved",
        "clauses": ["5.3", "5.4.1", "5.4.2", "5.7", "5.8"],
        "reference": "directed MPFR, Fraction scale normalization and report-formula projection",
        "profile": args.profile, "descriptor_pairs": len(pairs), "block_length": 3,
        "input_scale_values": ["0", "1", "-2", "+inf", "-inf", "nan"],
        "result_scale_values": ["0", "1", "-2", "1/2", "+inf", "-inf", "nan"],
        "function_inputs": dict(counts), "projections": sum(counts.values()) * MODE_COUNT * 3,
        "mode_count": MODE_COUNT, "saturation_count": 3,
        "mpfr_precisions": dict(precision_counts), "producer_exit": code,
        "coverage_complete": coverage_complete,
        "first_mismatches": mismatches, "sha256": digest.hexdigest(),
        "status": "pass" if code == 0 and not mismatches and coverage_complete else "fail"}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if report["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
