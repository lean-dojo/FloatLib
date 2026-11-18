#!/usr/bin/env python3
"""N1169 formatted conversion oracle: independent automaton and exact Fraction."""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import random
import re
import subprocess

SPACE = " \t\n\r\v\f"
DIGITS = "0123456789"
HEX = DIGITS + "abcdefABCDEF"
ACCEPTING = {"zero", "integer", "fraction", "hexinteger", "hexfraction", "exponent"}


def transition(state, char):
    """Read one character of the numeric-prefix DFA; None is the rejecting sink."""
    if state == "start" and char in "+-":
        return "sign"
    if state in {"start", "sign"}:
        if char == "0":
            return "zero"
        if char in DIGITS:
            return "integer"
        if char == ".":
            return "point"
    if state == "zero" and char in "xX":
        return "hexprefix"
    if state in {"zero", "integer"}:
        if char in DIGITS:
            return "integer"
        if char == ".":
            return "fraction"
        if char in "eE":
            return "exponentmarker"
    if state in {"point", "fraction"}:
        if char in DIGITS:
            return "fraction"
        if state == "fraction" and char in "eE":
            return "exponentmarker"
    if state in {"hexprefix", "hexinteger"}:
        if char in HEX:
            return "hexinteger"
        if char == ".":
            return "hexpoint" if state == "hexprefix" else "hexfraction"
        if state == "hexinteger" and char in "pP":
            return "exponentmarker"
    if state in {"hexpoint", "hexfraction"}:
        if char in HEX:
            return "hexfraction"
        if state == "hexfraction" and char in "pP":
            return "exponentmarker"
    if state == "exponentmarker" and char in "+-":
        return "exponentsign"
    if state in {"exponentmarker", "exponentsign", "exponent"} and char in DIGITS:
        return "exponent"
    return None


def prefix(text):
    state = "start"
    consumed = 0
    for char in text:
        next_state = transition(state, char)
        if next_state is None:
            break
        state = next_state
        consumed += 1
    return consumed, state in ACCEPTING


def exact(text):
    if "x" not in text.lower():
        return Fraction(text)
    sign = -1 if text.startswith("-") else 1
    significand, *exponent = re.split("[pP]", text.lstrip("+-")[2:])
    places = len(significand.split(".")[1]) if "." in significand else 0
    return sign * int(significand.replace(".", ""), 16) * Fraction(2) ** (
        (int(exponent[0]) if exponent else 0) - 4 * places)


def scanned(text, limit):
    rest = text.lstrip(SPACE)
    skipped = len(text) - len(rest)
    bounded = rest[:limit] if limit else rest
    consumed, complete = prefix(bounded)
    if consumed == 0:
        return skipped, 2 if not rest else 1, None
    if not complete:
        return skipped + consumed, 1, None
    return skipped + consumed, 0, exact(bounded[:consumed])


def rounded(value, mode):
    lower, remainder = divmod(value.numerator, value.denominator)
    if mode == 0:
        return lower
    if mode == 1:
        return lower + bool(remainder)
    twice = 2 * remainder
    return lower + (twice > value.denominator or
                    (twice == value.denominator and lower % 2 == 1))


def printed(coefficient, fractional, signed, mode, precision, width, mask):
    places = 6 if precision is None or precision < 0 else precision
    decimal = rounded(Fraction(coefficient * 10 ** places, 1 << fractional), mode)
    negative = decimal < 0 or (decimal == 0 and coefficient < 0)
    sign = "-" if negative else "+" if signed and mask & 2 else (
        " " if signed and mask & 4 else "")
    digits = str(abs(decimal)).rjust(places + 1, "0")
    if places:
        digits = digits[:-places] + "." + digits[-places:]
    elif mask & 8:
        digits += "."
    padding = max(0, abs(width) - len(sign) - len(digits))
    if mask & 1 or width < 0:
        return sign + digits + " " * padding
    if mask & 16:
        return sign + "0" * padding + digits
    return " " * padding + sign + digits


def corpus():
    alphabet = "01xep+-. \t"
    items = {""}
    texts = {""}
    for length in range(1, 6):
        words = {"".join(chars) for chars in itertools.product(alphabet, repeat=length)}
        items.update(words)
        if length <= 4:
            texts.update(words)
    for start in ["", " ", "\t\n", "\v\f\r", "+", "-", " +", " -"]:
        for token in ["0", ".5", "1.", "127", "0.875", "0.9", "1e+", "1E-3",
                      "0x1.f", "0X.8P+1", "0x.p+", "0x1p-", "0x1e2", "nan", "INF"]:
            for tail in ["", "tail", "\x00rest", "é", "e+", "p-"]:
                texts.add(start + token + tail)
    rng = random.Random(7196)
    for _ in range(300):
        coefficient = rng.randrange(-100000, 100001)
        exponent = rng.randrange(-20, 21)
        texts.add(f"{coefficient}e{exponent:+d}trailing")
        texts.add(f"{'-' if coefficient < 0 else ''}0x{abs(coefficient):x}p{exponent:+d}!")
    return {"items": sorted(items), "texts": sorted(texts),
            "precisions": [None, -1, 0, 1, 2, 6], "fieldWidths": [0, 1, 8, -8],
            "scanWidths": [0, 1, 2, 3, 4, 8], "flagMasks": list(range(32)), "maximumWidth": 6}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("executable", type=Path)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = corpus()
    args.corpus.write_text(json.dumps(data, ensure_ascii=True, separators=(",", ":")) + "\n")
    subjects = {(index, width): scanned(text, width) for index, text in enumerate(data["texts"])
                for width in data["scanWidths"]}
    process = subprocess.Popen([str(args.executable.resolve()), str(args.corpus.resolve())],
                               stdout=subprocess.PIPE, text=True)
    digest = hashlib.sha256()
    counts = {"item": 0, "output": 0, "input": 0}
    failures, failure_count = [], 0
    for line in process.stdout:
        digest.update(line.encode())
        fields = line.removesuffix("\n").split(",")
        if fields[0] == "A":
            index = int(fields[1])
            actual = int(fields[2])
            expected = int(prefix(data["items"][index])[0] == len(data["items"][index]))
            counts["item"] += 1
        elif fields[0] == "P":
            width, signed, fractional, word, mode, p, w, mask = map(int, fields[1:9])
            coefficient = word - (1 << width) if signed and word >= 1 << (width - 1) else word
            actual = fields[9]
            expected = printed(coefficient, fractional, signed, mode, data["precisions"][p],
                               data["fieldWidths"][w], mask)
            counts["output"] += 1
        elif fields[0] == "S":
            index, limit, width, signed, fractional, mode = map(int, fields[1:7])
            consumed, status, value = subjects[index, limit]
            coefficient = None
            if value is not None:
                coefficient = rounded(value * (1 << fractional), mode)
                precision = width - signed
                low, high = -(1 << precision) if signed else 0, (1 << precision) - 1
                if not low <= coefficient <= high:
                    status, coefficient = 3, None
            actual = [int(fields[7]), int(fields[8]),
                      None if fields[9] == "NA" else int(fields[9])]
            expected = [consumed, status, coefficient]
            counts["input"] += 3
        else:
            raise SystemExit(f"unexpected Lean record: {fields[0]}")
        if actual != expected:
            failure_count += 1
            if len(failures) < 30:
                failures.append({"record": fields, "expected": expected})
    if process.wait():
        raise SystemExit("Lean producer failed")
    formats = sum(2 * width + 1 for width in range(1, data["maximumWidth"] + 1))
    values = sum((2 * width + 1) * (1 << width)
                 for width in range(1, data["maximumWidth"] + 1))
    expected_counts = {
        "item": len(data["items"]),
        "output": values * 3 * len(data["precisions"]) * len(data["fieldWidths"]) *
                  len(data["flagMasks"]),
        "input": len(data["texts"]) * len(data["scanWidths"]) * formats * 3 * 3,
    }
    if counts != expected_counts:
        raise SystemExit(f"incomplete Lean corpus: {counts} != {expected_counts}")
    report = {
        "source": "N1169 C 7.19.6.1–2 and inherited N1256 C99 clauses",
        "oracle": "Independent single-pass prefix DFA and exact fractions.Fraction",
        "items": len(data["items"]), "texts": len(data["texts"]), "comparisons": counts,
        "total_comparisons": sum(counts.values()), "failure_count": failure_count,
        "failures": failures, "corpus_sha256": hashlib.sha256(args.corpus.read_bytes()).hexdigest(),
        "lean_output_sha256": digest.hexdigest(),
        "scope": [
            "All item strings through length five over a ten-character grammar alphabet.",
            "All numeric input strings through length four over that alphabet, structured "
            "grammar boundaries and 600 seeded subjects; six field-width settings.",
            "Every signed/unsigned fixed grid through width six and all three rounders.",
            "Every output code at those widths, 32 flag combinations, six precision settings "
            "and four signed field widths.",
            "Single resolved C-locale conversions; no streams, pointer writes, assignment "
            "suppression, full format parsing or non-C locale."
        ]
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if failure_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
