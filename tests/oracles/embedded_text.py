#!/usr/bin/env python3
"""Compare N1169 text parsing with independent regular expressions and Fraction."""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import random
import re
import subprocess

DECIMAL = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")
HEX = re.compile(
    r"[+-]?0[xX](?:[0-9a-fA-F]+(?:\.[0-9a-fA-F]*)?|\.[0-9a-fA-F]+)"
    r"(?:[pP][+-]?[0-9]+)?")
WHITESPACE = " \t\n\r\v\f"


def parse(text):
    start = len(text) - len(text.lstrip(WHITESPACE))
    tail = text[start:]
    matches = [match for pattern in [DECIMAL, HEX] if (match := pattern.match(tail))]
    if not matches:
        return None, 0
    match = max(matches, key=lambda item: item.end())
    token = match.group()
    if "x" not in token.lower():
        return Fraction(token), start + match.end()
    sign = -1 if token.startswith("-") else 1
    magnitude = token.lstrip("+-")[2:].lower()
    parts = magnitude.split("p")
    significand = parts[0]
    exponent = int(parts[1]) if len(parts) == 2 else 0
    fractional = len(significand.split(".")[1]) if "." in significand else 0
    coefficient = int(significand.replace(".", ""), 16)
    return sign * coefficient * Fraction(2) ** (exponent - 4 * fractional), start + match.end()


def corpus():
    inputs = {""}
    # Every short string over characters exercising both exponent grammars and signs.
    alphabet = "01xep+-. \t"
    for length in range(1, 5):
        inputs.update("".join(chars) for chars in itertools.product(alphabet, repeat=length))
    for prefix in ["", " ", "\t\n", "\v\f\r", "+", "-", " +", " -"]:
        for token in ["0", ".5", "1.", "127", "0.875", "0.9", "1e+", "1E-3",
                      "0x1.f", "0X.8P+1", "0x.p+", "0x1p-", "0x1e2", "nan", "INF"]:
            for suffix in ["", "tail", "\x00rest", "é", "e+", "p-"]:
                inputs.add(prefix + token + suffix)
    rng = random.Random(18037)
    for _ in range(1200):
        coefficient = rng.randrange(-100000, 100001)
        exponent = rng.randrange(-20, 21)
        inputs.add(f"{coefficient}e{exponent:+d}trailing")
        sign = "-" if coefficient < 0 else ""
        inputs.add(f"{sign}0x{abs(coefficient):x}p{exponent:+d}!")
    return sorted(inputs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("executable", type=Path)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--width", type=int, default=6)
    args = parser.parse_args()
    inputs = corpus()
    args.corpus.write_text(json.dumps(inputs, ensure_ascii=True, separators=(",", ":")) + "\n")
    subjects = [parse(text) for text in inputs]
    process = subprocess.Popen(
        [str(args.executable.resolve()), str(args.corpus.resolve()), str(args.width)],
        stdout=subprocess.PIPE, text=True)
    digest = hashlib.sha256()
    counts = {"subject": 0, "conversion": 0}
    failures = []
    failure_count = 0
    for line in process.stdout:
        digest.update(line.encode())
        fields = line.strip().split(",")
        index = int(fields[1])
        value, endptr = subjects[index]
        if fields[0] == "A":
            expected = [value.numerator, value.denominator, endptr] if value is not None else [
                None, None, 0]
            actual = [None if item == "NA" else int(item) for item in fields[2:]]
            counts["subject"] += 3
        else:
            signed, integral, fractional, mode = map(int, fields[2:6])
            precision = integral + fractional
            low = -(1 << precision) if signed else 0
            high = (1 << precision) - 1
            if value is None:
                expected = [0, 0, 0]
            else:
                scaled = value * (1 << fractional)
                lower, remainder = divmod(scaled.numerator, scaled.denominator)
                if mode == 0:
                    rounded = lower
                elif mode == 1:
                    rounded = lower + bool(remainder)
                else:
                    twice = 2 * remainder
                    rounded = lower + (twice > scaled.denominator or
                                       (twice == scaled.denominator and lower % 2 == 1))
                expected = [max(low, min(high, rounded)), endptr, int(not low <= scaled <= high)]
            actual = list(map(int, fields[6:]))
            counts["conversion"] += 3
        if actual != expected:
            failure_count += 1
            if len(failures) < 30:
                failures.append({"input": inputs[index], "record": fields[:6],
                                 "actual": actual, "expected": expected})
    if process.wait():
        raise SystemExit("Lean producer failed")
    report = {
        "source": "WG14 N1169, ISO/IEC TR 18037:2006(E), C 7.18a.6.8",
        "oracle": "Python re maximal numeric-prefix matches, fractions.Fraction",
        "inputs": len(inputs), "maximum_width": args.width, "comparisons": counts,
        "total_comparisons": sum(counts.values()), "failure_count": failure_count,
        "failures": failures, "corpus_sha256": hashlib.sha256(args.corpus.read_bytes()).hexdigest(),
        "lean_output_sha256": digest.hexdigest(),
        "scope": [
            "All strings of lengths zero through four over the ten-character alphabet 01xep+-. TAB.",
            "Selected cases cover all C whitespace, decimal/hexadecimal exponents, incomplete "
            "exponents, NUL termination, rejected NaN/infinity, signs and non-ASCII tails.",
            "2400 seeded bounded decimal and hexadecimal exponent examples.",
            "Every signed/unsigned layout through maximum_width and all three rounders.",
            "End offsets and exact-source range errors are checked as well as stored coefficients.",
            "Only the C-locale grammar is claimed; this is not every possible input string."
        ]
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if failure_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
