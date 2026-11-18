#!/usr/bin/env python3
"""Check N1169 exact-value observations using independent Python Fractions."""
import argparse
import collections
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess


def rounded(value, mode):
    lower, remainder = divmod(value.numerator, value.denominator)
    if mode == 0:
        return lower
    if mode == 1:
        return lower + bool(remainder)
    twice = 2 * remainder
    return lower + (twice > value.denominator or
                    (twice == value.denominator and lower % 2 == 1))


def truncated(value, unsigned):
    integer = abs(value.numerator) // value.denominator
    if value < 0:
        integer = -integer
    return integer if (0 if unsigned else -128) <= integer <= (255 if unsigned else 127) else None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("executable", type=Path)
    parser.add_argument("--width", type=int, default=6)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--clang-corpus", type=Path)
    parser.add_argument("--clang", type=Path, default=Path("/usr/bin/clang"))
    parser.add_argument("--policy", action="store_true")
    parser.add_argument("--interface", action="store_true")
    args = parser.parse_args()
    if sum(bool(x) for x in [args.policy, args.interface, args.clang_corpus]) > 1:
        parser.error("--policy, --interface and --clang-corpus are separate corpora")
    clang = {}
    if args.clang_corpus:
        for line in args.clang_corpus.read_text().splitlines():
            row = line.split(",")
            sign, a, b = map(int, row[:3])
            outputs = [None if item == "NA" else int(item) for item in row[3:]]
            for k in range(4):
                if sign and outputs[k] is not None and outputs[k] >= 128:
                    outputs[k] -= 256
            clang[sign, a, b] = outputs
    selection = "fract8" if args.clang_corpus else str(args.width)
    selections = ["policy", str(args.width)] if args.policy else [selection]
    if args.interface:
        selections = ["interface", str(args.width)]
    process = subprocess.Popen([str(args.executable.resolve()), *selections],
                               stdout=subprocess.PIPE, text=True)
    digest = hashlib.sha256()
    counts = collections.Counter()
    cases = collections.Counter()
    failures = []
    failure_count = 0
    formats = 0
    for line in process.stdout:
        digest.update(line.encode())
        fields = line.strip().split(",")
        kind = fields[0]
        if kind == "F":
            signed, integral, fractional = map(int, fields[1:])
            precision = integral + fractional
            width = precision + signed
            size = 1 << width
            low, high = (-1 << precision) if signed else 0, (1 << precision) - 1
            scale = 1 << fractional
            formats += 1
            continue

        def coefficient(word):
            return word - size if signed and word >= size // 2 else word

        def value(word):
            return Fraction(coefficient(word), scale)

        def convert(q, mode, saturation):
            scaled = q * scale
            coefficient = rounded(scaled, mode)
            if not saturation and not low <= coefficient <= high:
                return None
            return max(low, min(high, coefficient))

        def all_conversions(q):
            return [convert(q, mode, saturation) for mode in range(3) for saturation in range(2)]

        def selected(q, operation, policy, mode, saturation):
            if q is None:
                return None
            if policy in [4, 5] and operation == 2 and abs(q) == 1:
                inward = scale - 1 if q == 1 else 1 - scale
                return min(high, max(low, inward))
            ordinary = convert(q, mode, saturation)
            if ordinary is None:
                return None
            if operation in [2, 3] and policy in [2, 3, 5]:
                neighbor = ordinary + (1 if policy == 3 else -1)
                return min(high, max(low, neighbor))
            return ordinary

        if kind == "L":
            expected = [low, high, precision, width]
            expected += [bound for extra in [0, 1, 7] for bound in
                         [-(1 << (precision + extra)) if signed else 0,
                          (1 << (precision + extra)) - 1]]
            expected.append(1 if precision else None)
            start = 1
        elif kind == "V":
            a, integer = map(int, fields[1:3])
            q = value(a)
            expected = list(map(int, [
                integer == q, integer != q, integer < q, integer <= q,
                integer > q, integer >= q, q == integer, q != integer,
                q < integer, q <= integer, q > integer, q >= integer]))
            left = [integer + q, integer - q, integer * q,
                    integer / q if q else None]
            right = [q + integer, q - integer, q * integer,
                     q / integer if integer else None]
            for mode in range(3):
                for sat in range(2):
                    for policy in range(6):
                        left_fixed = [selected(result, op, policy, mode, sat)
                                      for op, result in enumerate(left)]
                        expected += left_fixed
                        expected += [selected(result, op, policy, mode, sat)
                                     for op, result in enumerate(right)]
                        expected += [truncated(Fraction(result, scale), unsigned)
                                     if result is not None else None
                                     for unsigned in [False, True] for result in left_fixed]
            start = 3
        elif kind == "U":
            a = int(fields[1])
            q, c = value(a), coefficient(a)
            count = precision if c == 0 else max(
                k for k in range(precision + 1) if low <= c * (1 << k) <= high)
            expected = [c, q.numerator, q.denominator, a,
                        min(high, max(low, abs(c))), count, int(c == 0)]
            expected += [convert(result, mode, sat)
                         for mode in range(3) for sat in range(2)
                         for result in [-q, q + 1, q - 1]]
            start = 2
        elif kind == "S":
            a, count = map(int, fields[1:3])
            q, c = value(a), coefficient(a)
            expected = [convert(q * (1 << count) if left else q / (1 << count), mode, sat)
                        if 0 <= count < width else None
                        for mode in range(3) for sat in range(2) for left in [True, False]]
            if 0 <= count < fractional:
                step = 1 << (fractional - count)
                coarse = rounded(Fraction(c, step), 2) * step
                expected.append(max(low, min(high, coarse)))
            else:
                expected.append(None)
            start = 3
        elif kind == "I":
            a, integer = map(int, fields[1:3])
            q = value(a)
            expected = [truncated(result, unsigned) if result is not None else None
                        for unsigned in [False, True]
                        for result in [integer * q, Fraction(integer) / q if q else None]]
            expected += [convert(result, mode, sat) if result is not None else None
                         for mode in range(3) for sat in range(2)
                         for result in [integer * q, q / integer if integer else None]]
            start = 3
        elif kind == "B":
            a, b = map(int, fields[1:3])
            x, y = value(a), value(b)
            exact = [x + y, x - y, x * y, x / y if y else None]
            expected = [convert(q, mode, sat) if q is not None else None
                        for mode in range(3) for sat in range(2) for q in exact]
            expected += list(map(int, [x == y, x != y, x < y, x <= y, x > y, x >= y]))
            expected += [truncated(x / y, unsigned) if y else None for unsigned in [False, True]]
            start = 3
        elif kind == "P":
            a, b = map(int, fields[1:3])
            x, y = value(a), value(b)
            exact = [x + y, x - y, x * y, x / y if y else None]

            expected = [
                selected(q, operation, policy, mode, sat)
                for mode in range(3) for sat in range(2) for policy in range(6)
                for operation, q in enumerate(exact)
            ]
            start = 3
        elif kind == "C":
            q = Fraction(int(fields[1]), int(fields[2]))
            expected = all_conversions(q) + [convert(q, 2, True)]
            start = 3
        elif kind == "Q":
            numerator, denominator = map(int, fields[1:3])
            expected = [convert(Fraction(numerator, denominator), mode, True)
                        if denominator else None for mode in range(3)]
            start = 3
        else:
            raise ValueError(f"Unknown record {kind}")
        actual = [None if item == "NA" else int(item) for item in fields[start:]]
        counts[kind] += len(expected)
        cases[kind] += 1
        if actual != expected:
            failure_count += 1
            if len(failures) < 30:
                failures.append({"format": [signed, integral, fractional], "record": fields[:start],
                                 "actual": actual, "expected": expected})
        if kind == "B" and args.clang_corpus:
            c_values = clang.pop((signed, a, b))
            permitted = [[actual[4 + k], actual[12 + k]] for k in range(4)]
            permitted += [[item] for item in actual[24:30]]
            counts["clang"] += len(c_values)
            cases["clang"] += 1
            if any(item not in allowed for item, allowed in zip(c_values, permitted)):
                failure_count += 1
                if len(failures) < 30:
                    failures.append({"format": [signed, integral, fractional],
                                     "record": fields[:start], "clang": c_values,
                                     "permitted_lean": permitted})
    status = process.wait()
    if status:
        raise SystemExit(f"Lean producer failed: {status}")
    if clang:
        raise SystemExit(f"{len(clang)} Clang rows were not compared")
    report = {
        "source": "WG14 N1169, ISO/IEC TR 18037:2006(E), clauses 4.1.3–4.1.7 and C 7.18a.6",
        "oracle": "Python fractions.Fraction, direct integer floor/ceiling/tie parity/truncation",
        "maximum_width": 8 if args.clang_corpus else args.width, "formats": formats,
        "cases": dict(cases), "comparisons": dict(counts), "total_comparisons": sum(counts.values()),
        "corpus_sha256": digest.hexdigest(), "failure_count": failure_count, "failures": failures,
        "scope": [
            ("Signed short _Fract s.7 and unsigned short _Fract .8, matching the tested Clang layout."
             if args.clang_corpus else
             "All signed and unsigned layouts at every width from one through maximum_width."),
            ("All words and all pairs in both C short-fract types."
             if args.clang_corpus else
             "All words and all pairs; these small layouts are extensions below C precision minima."),
            "All floor, ceiling and nearest-even policies, DEFAULT/SAT and _Sat type precedence.",
            "All valid shift and rounding counts plus the adjacent invalid counts.",
            "Integer-result support uses signed and unsigned eight-bit ranges.",
            "C ABI, padding, text, locale, mutation, mixed-layout arithmetic and relaxed precision are separate."
        ]
    }
    if args.clang_corpus:
        report["clang_version"] = subprocess.check_output(
            [str(args.clang), "--version"], text=True).splitlines()[0]
        report["clang_command"] = "-std=c11 -O2 -ffixed-point"
        report["clang_probe_sha256"] = hashlib.sha256(
            Path(__file__).with_suffix(".c").read_bytes()).hexdigest()
        report["clang_corpus_sha256"] = hashlib.sha256(args.clang_corpus.read_bytes()).hexdigest()
        report["scope"].append(
            "Clang SAT arithmetic is checked against the union of Lean floor and ceiling outcomes; "
            "comparisons must agree exactly. No C division by zero is evaluated.")
    if args.policy:
        report["source"] = (
            "WG14 N1169, ISO/IEC TR 18037:2006(E), 4.1.6.2.1, C 6.3.1.3a and C 7.18a.4")
        report["scope"] = [
            "All signed and unsigned layouts from width one through maximum_width.",
            "All operand pairs, four arithmetic operations, three rounders and DEFAULT/SAT.",
            "Six policy instances: ordinary ON/OFF, both OFF neighbors, inward units with "
            "ordinary ON, and inward units with lower-neighbor OFF.",
            "Undefined division and ordinary rounded overflow are checked explicitly.",
            "The Lean theorem covers arbitrary admissible policies; the corpus tests these six."
        ]
    if args.interface:
        report["source"] = (
            "WG14 N1169, ISO/IEC TR 18037:2006(E), 4.1.6.2.3, 4.1.6.3, C 7.18a.2–3")
        report["scope"] = [
            "All signed and unsigned layouts from width one through maximum_width.",
            "Endpoints, bit counts and associated integer ranges with 0, 1 and 7 extra bits.",
            "Epsilon at positive precision; no epsilon is constructed for zero value bits.",
            "Every fixed code with nine integers spanning both sides of signed eight-bit range.",
            "Twelve directed integer comparisons and sixteen arithmetic/assignment results "
            "under three rounders, two overflow modes and all six arithmetic policies.",
            "Integer assignment first rounds into the fixed type, then truncates into signed "
            "or unsigned eight-bit integer range.",
            "Mathematical integer operands do not model host C integer argument overflow."
        ]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if failure_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
