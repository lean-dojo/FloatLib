"""Posit Standard §§6.1, 6.3–6.4 against the independent exact rational oracle."""

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from posit_functions import decode, rounded


def expected_rows():
    for source in range(2, 11):
        for target in range(2, 11):
            for word in range(1 << source):
                yield ["C", source, target, word], [rounded(target, decode(source, word))]
    for bits in range(2, 9):
        for width in range(1, 13):
            sentinel = 1 << (width - 1)
            modulus = 2 * sentinel
            for word in range(modulus):
                signed = word if word < sentinel else word - modulus
                yield ["F", bits, width, word], [
                    rounded(bits, None if word == sentinel else Fraction(integer))
                    for integer in (signed, word)]
            for word in range(1 << bits):
                exact = decode(bits, word)
                integer = None if exact is None else round(exact)
                yield ["T", bits, width, word], [
                    sentinel if integer is None or not lower <= integer <= upper
                    else integer % modulus
                    for lower, upper in [(-sentinel, sentinel - 1), (0, modulus - 1)]]
        for word in range(1 << bits):
            yield ["D", bits, word], [decode(bits, word), word]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("observations", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    counts, failures, digest = Counter(), [], hashlib.sha256()
    with args.observations.open("rb") as stream:
        for fields, expected in expected_rows():
            raw = stream.readline()
            digest.update(raw)
            row = raw.decode().strip().split(",")
            if row[:len(fields)] != list(map(str, fields)):
                raise ValueError(f"Missing, reordered or duplicate input: {fields}, got {row}")
            output = row[len(fields):]
            if len(output) != len(expected):
                raise ValueError(f"Wrong number of outputs at {fields}")
            if fields[0] == "D":
                actual = [None if output[0] == "NaR" else Fraction(output[0]), int(output[1])]
            else:
                actual = list(map(int, output))
            counts[fields[0]] += len(expected)
            if actual != expected:
                counts["mismatches"] += 1
                if len(failures) < 30:
                    failures.append({"input": fields, "actual": list(map(str, actual)),
                                     "expected": list(map(str, expected))})
        if stream.read(1):
            raise ValueError("Unexpected extra observation")
    result = dict(
        status="fail" if failures else "pass",
        document="Posit Standard (2022), §§4.1, 6.1, 6.3–6.4",
        reference="Independent regime/exponent/fraction decoding and Fraction arithmetic.",
        cases=dict(counts), observations_sha256=digest.hexdigest(), first_mismatches=failures,
        limitations=[
            "Precision conversion exhausts every source word for every pair of widths 2–10.",
            "Integer conversion exhausts posit widths 2–8 and integer widths 1–12, both signs.",
            "Decimal checks exhaust display values and their parse round trips at widths 2–8.",
            "This is testing evidence, not a proof of the universal claims or of every input string.",
        ])
    args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
