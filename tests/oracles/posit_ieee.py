"""Posit Standard §6.5 against independent exact binary/posit field decoding."""

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from pathlib import Path

from posit_functions import decode, rounded


SMALL = [(exponent, fraction) for exponent in range(2, 5) for fraction in range(1, 5)]
MODES = ["nearest", "nearestAway", "towardZero", "up", "down", "away"]


@lru_cache(None)
def binary_decode(exponent, fraction, word):
    """Return None for every infinity/NaN, collapsing both zero signs as §6.5 requires."""
    sign = word >> (exponent + fraction)
    field = (word >> fraction) & ((1 << exponent) - 1)
    tail = word & ((1 << fraction) - 1)
    if field == (1 << exponent) - 1:
        return None
    bias = (1 << (exponent - 1)) - 1
    coefficient = tail if field == 0 else (1 << fraction) + tail
    power = max(field, 1) - bias - fraction
    return (-1 if sign else 1) * coefficient * Fraction(2) ** power


def binary_round(exponent, fraction, exact, mode):
    """Quantize a rational with an integer grid, then encode or apply directed overflow."""
    all_exponents = (1 << exponent) - 1
    if exact is None:
        return (all_exponents << fraction) | (1 << (fraction - 1))
    if exact == 0:
        return 0
    negative, magnitude = exact < 0, abs(exact)
    sign = int(negative) << (exponent + fraction)
    bias = (1 << (exponent - 1)) - 1
    leading = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if magnitude < Fraction(2) ** leading:
        leading -= 1
    quantum = max(leading, 1 - bias) - fraction
    scaled = magnitude / (Fraction(2) ** quantum)
    coefficient, remainder = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * remainder
    increment = {
        "nearest": twice > scaled.denominator or
                   (twice == scaled.denominator and coefficient % 2 == 1),
        "nearestAway": twice >= scaled.denominator,
        "towardZero": False,
        "up": not negative and remainder != 0,
        "down": negative and remainder != 0,
        "away": remainder != 0,
    }[mode]
    coefficient += increment
    if coefficient >= 1 << (fraction + 1):
        coefficient >>= 1
        quantum += 1
    encoded_exponent = quantum + fraction + bias
    if encoded_exponent >= all_exponents:
        infinity = mode in {"nearest", "nearestAway", "away"} or \
            (mode == "up" and not negative) or (mode == "down" and negative)
        magnitude_word = all_exponents << fraction
        return sign | (magnitude_word if infinity else magnitude_word - 1)
    if coefficient < 1 << fraction:
        return sign | coefficient
    return sign | (encoded_exponent << fraction) | (coefficient - (1 << fraction))


def expected_rows():
    for exponent, fraction in SMALL + [(5, 10), (8, 7)]:
        for bits in range(2, 9):
            for word in range(1 << (1 + exponent + fraction)):
                yield ["F", exponent, fraction, bits, word], rounded(
                    bits, binary_decode(exponent, fraction, word))
    for exponent, fraction in SMALL + [(5, 10), (8, 7), (8, 23), (11, 52),
                                       (15, 112), (19, 236)]:
        for bits in range(2, 9):
            for word in range(1 << bits):
                for mode in MODES:
                    yield ["T", exponent, fraction, bits, word, mode], binary_round(
                        exponent, fraction, decode(bits, word), mode)


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
            if len(row) != len(fields) + 1 or row[:-1] != list(map(str, fields)):
                raise ValueError(f"Missing, extra or reordered output: {fields}, got {row}")
            actual = int(row[-1])
            counts[fields[0]] += 1
            if actual != expected:
                counts["mismatches"] += 1
                if len(failures) < 30:
                    failures.append(dict(input=fields, actual=actual, expected=expected))
        if stream.read(1):
            raise ValueError("Unexpected extra observation")
    result = dict(
        status="fail" if failures else "pass",
        document="Posit Standard (2022), §6.5",
        reference="Independent Fraction field decoding, posit cuts and integer-grid IEEE rounding.",
        cases=dict(counts), observations_sha256=digest.hexdigest(), first_mismatches=failures,
        limitations=[
            "Incoming binary16 and bfloat16 words are exhaustive at posit widths 2–8.",
            "Twelve smaller IEEE descriptors are exhaustive in both directions.",
            "Outgoing posit words at widths 2–8 cover binary16, bfloat16 and binary32/64/128/256.",
            "All five IEEE rounding directions are tested; away-from-zero is an extension.",
            "The report checks output encodings, not conversion status flags or all widths.",
        ])
    args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
