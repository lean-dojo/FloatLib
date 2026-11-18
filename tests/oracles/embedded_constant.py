#!/usr/bin/env python3
"""Check N1169 constants using full regex matches and exact Fraction arithmetic."""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import random
import re
import subprocess

DECIMAL = r"(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?"
HEX = r"0[xX](?:[0-9a-fA-F]+(?:\.[0-9a-fA-F]*)?|\.[0-9a-fA-F]+)[pP][+-]?[0-9]+"
PATTERN = re.compile(rf"(?P<body>{HEX}|{DECIMAL})(?P<suffix>u?[hl]?[rk])", re.IGNORECASE)


def parse(text):
    match = PATTERN.fullmatch(text)
    if not match:
        return None
    body, suffix = match["body"], match["suffix"].lower()
    signed = not suffix.startswith("u")
    kind = int(suffix.endswith("k"))
    length = 0 if "h" in suffix else 2 if "l" in suffix else 1
    hexadecimal = body.lower().startswith("0x")
    if hexadecimal:
        significand, exponent = re.split("[pP]", body[2:])
        fractional = len(significand.split(".")[1]) if "." in significand else 0
        value = int(significand.replace(".", ""), 16) * Fraction(2) ** (
            int(exponent) - 4 * fractional)
    else:
        value = Fraction(body)
    return int(signed), kind, length, value, int(hexadecimal)


def corpus():
    suffixes = []
    for suffix in ["r", "hr", "lr", "ur", "uhr", "ulr",
                   "k", "hk", "lk", "uk", "uhk", "ulk"]:
        suffixes.extend("".join(chars) for chars in
                        itertools.product(*[(char, char.upper()) for char in suffix]))
    bodies = ["", ".", "+1", "-1", " 1", "1 ", "1e+", "0x1", "0x.p0",
              "nan", "inf", "1_0", "0x1p", "0x1p-", "1e2tail"]
    for numerator in range(65):
        for places in range(4):
            bodies.append(f"{numerator}e-{places}")
            bodies.append(f"0x{numerator:x}p-{places}")
    inputs = {body + suffix for body in bodies for suffix in suffixes}
    inputs.update(["1", "1.0", "0x1p0", "1ru", "1klu", "1rr", "1llr", "1uuk", "1hhr"])
    rng = random.Random(640442)
    for _ in range(1500):
        suffix = rng.choice(suffixes)
        numerator = rng.randrange(1 << 20)
        exponent = rng.randrange(-25, 26)
        inputs.add(f"{numerator}e{exponent:+d}{suffix}")
        inputs.add(f"0X{numerator:X}P{exponent:+d}{suffix}")
    return sorted(inputs)


def coefficient(value, fractional, mode, hexadecimal):
    scaled = value * (1 << fractional)
    lower, remainder = divmod(scaled.numerator, scaled.denominator)
    if hexadecimal and mode == 1:
        return lower
    if hexadecimal and mode == 2:
        return lower + bool(remainder)
    twice = 2 * remainder
    nearest = lower + (twice > scaled.denominator or
                       (twice == scaled.denominator and lower % 2 == 1))
    return nearest + (0 if hexadecimal or mode == 0 else -1 if mode == 1 else 1)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("executable", type=Path)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    inputs = corpus()
    args.corpus.write_text(json.dumps(inputs, ensure_ascii=True, separators=(",", ":")) + "\n")
    literals = [parse(text) for text in inputs]
    process = subprocess.Popen(
        [str(args.executable.resolve()), str(args.corpus.resolve())],
        stdout=subprocess.PIPE, text=True)
    digest = hashlib.sha256()
    counts = {"parse": 0, "translation": 0}
    failures, failure_count = [], 0
    for line in process.stdout:
        digest.update(line.encode())
        fields = line.strip().split(",")
        index = int(fields[1])
        literal = literals[index]
        actual = [None if value == "NA" else int(value) for value in fields[2:]]
        if fields[0] == "A":
            if literal is None:
                expected = [None]
            else:
                signed, kind, length, value, hexadecimal = literal
                expected = [signed, kind, length, value.numerator, value.denominator, hexadecimal]
            counts["parse"] += 1
        else:
            if literal is None:
                raise AssertionError(f"Lean translated a rejected input: {inputs[index]}")
            fractional, integral, mode, result = actual
            signed, kind, _, value, hexadecimal = literal
            high = (1 << (fractional + (integral if kind else 0))) - 1
            low = -(high + 1) if signed else 0
            scaled = value * (1 << fractional)
            if kind == 0 and value == 1:
                expected_result = high
            elif not low <= scaled <= high:
                expected_result = None
            else:
                expected_result = max(low, min(high, coefficient(
                    value, fractional, mode, hexadecimal)))
            expected = [fractional, integral, mode, expected_result]
            counts["translation"] += 1
        if actual != expected:
            failure_count += 1
            if len(failures) < 30:
                failures.append({"input": inputs[index], "actual": actual, "expected": expected})
    if process.wait():
        raise SystemExit("Lean producer failed")
    report = {
        "source": "N1169 C 6.4.4.2a; N1256 C99 6.4.4.2 paragraph 3",
        "oracle": "Independent full-match regex grammar and fractions.Fraction",
        "inputs": len(inputs), "comparisons": counts, "total_comparisons": sum(counts.values()),
        "failure_count": failure_count, "failures": failures,
        "corpus_sha256": hashlib.sha256(args.corpus.read_bytes()).hexdigest(),
        "lean_output_sha256": digest.hexdigest(),
        "scope": [
            "Every case variation of all twelve suffixes, selected full-grammar rejection cases.",
            "Bounded decimal and hexadecimal coefficient/exponent grids plus 3000 seeded literals.",
            "18 layout choices and nearest, decimal-lower/hex-floor, decimal-upper/hex-ceil policies.",
            "Exact source-range constraints, fract-one maximum and hexadecimal mandatory exponents.",
            "Not every source literal, every layout, C preprocessing or evaluation formats."
        ]
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if failure_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
