"""Independent Fraction implementation of P3109 v4.1 §§4.7.4–4.7.6.

Stream exact rational observations from the compiled Lean producer. The reference
uses the report's logarithmic quantum and scaled-fraction formulas, not bisection
or the new threshold comparisons. No generated data becomes a Lean axiom.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess


def pow2(exponent):
    return F(2 ** exponent) if exponent >= 0 else F(1, 2 ** (-exponent))


def log2floor(value):
    exponent = value.numerator.bit_length() - value.denominator.bit_length()
    return exponent - (value < pow2(exponent))


def nearest_even(value):
    lower, remainder = divmod(value.numerator, value.denominator)
    return lower + (2 * remainder > value.denominator or
                    (2 * remainder == value.denominator and lower % 2))


MODES = [(name, 0, 0) for name in ('zero', 'up', 'down', 'away', 'even', 'odd')]
for n in range(4):
    for r in range(2 ** n):
        MODES.extend((kind, n, r) for kind in ('A', 'B', 'C'))


class Format:
    def __init__(self, width, precision, signed, extended):
        self.width, self.precision, self.signed, self.extended = width, precision, signed, extended
        self.bias = 2 ** (width - precision - signed)
        self.minimum = 2 - precision - self.bias
        self.nan = 2 ** (width - 1) if signed else 2 ** width - 1
        self.infinity = 2 ** (width - 1) - 1 if signed else 2 ** width - 2
        self.maximum_code = self.infinity - extended
        trailing = 2 ** (precision - 1)
        self.values = {}
        for code in range(self.maximum_code + 1):
            row, fraction = divmod(code, trailing)
            value = fraction * pow2(self.minimum) if row == 0 else (
                trailing + fraction) * pow2(row - self.bias + 1 - precision)
            self.values[value] = code
        self.maximum = max(self.values)

    def expected(self, target):
        if not target:
            return [0] * (len(MODES) * 3)
        magnitude = abs(target)
        quantum = max(log2floor(magnitude), 1 - self.bias) - self.precision + 1
        unit = pow2(quantum)
        scaled = magnitude / unit
        lower = scaled.numerator // scaled.denominator
        fraction = scaled - lower
        even = lower % 2 == 0 if self.precision > 1 else (lower == 0 or (quantum + self.bias) % 2 == 0)
        negative = target < 0
        result = []
        for mode, n, r in MODES:
            if mode == 'zero':
                up = False
            elif mode == 'up':
                up = bool(fraction) and not negative
            elif mode == 'down':
                up = bool(fraction) and negative
            elif mode == 'away':
                up = fraction >= F(1, 2)
            elif mode == 'even':
                up = fraction > F(1, 2) or (fraction == F(1, 2) and not even)
            elif mode == 'odd':
                up = bool(fraction) and even
            elif mode == 'A':
                z = fraction * 2 ** n
                up = z.numerator // z.denominator + r >= 2 ** n
            elif mode == 'B':
                z = fraction * 2 ** (n + 1)
                up = z.numerator // z.denominator + 2 * r + 1 >= 2 ** (n + 1)
            else:
                up = nearest_even(fraction * 2 ** n) + r >= 2 ** n
            rounded = (lower + up) * unit
            below = negative and rounded and (not self.signed or rounded > self.maximum)
            above = not negative and rounded > self.maximum
            for saturation in ('finite', 'propagate', 'none'):
                if below:
                    if saturation != 'none' or mode in ('zero', 'up'):
                        code = self.maximum_code + 2 ** (self.width - 1) if self.signed else 0
                    else:
                        code = 2 ** self.width - 1 if self.signed and self.extended else self.nan
                elif above:
                    code = self.maximum_code if saturation != 'none' or mode in ('zero', 'down') else (
                        self.infinity if self.extended else self.nan)
                else:
                    code = self.values[rounded]
                    if code and negative:
                        code += 2 ** (self.width - 1)
                result.append(code)
        return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('producer', type=Path)
    parser.add_argument('report', type=Path)
    args = parser.parse_args()
    process = subprocess.Popen([str(args.producer.resolve())], stdout=subprocess.PIPE)
    digest = hashlib.sha256()
    descriptors = observations = projections = 0
    mismatches = []
    current = None
    for raw in process.stdout:
        digest.update(raw)
        row = raw.decode().strip().split(',')
        if row[0] == 'F':
            current = Format(int(row[1]), int(row[2]), row[3] == 'true', row[4] == 'true')
            descriptors += 1
        else:
            assert row[0] == 'R' and current is not None
            target = F(int(row[1]), int(row[2]))
            actual = list(map(int, row[3:]))
            expected = current.expected(target)
            assert len(actual) == len(expected)
            observations += 1
            projections += len(actual)
            if actual != expected and len(mismatches) < 20:
                mismatches.append({'format': vars(current) | {'values': None, 'maximum': str(current.maximum)},
                                   'target': str(target), 'differences': [
                                       [i, a, b] for i, (a, b) in enumerate(zip(actual, expected)) if a != b]})
    code = process.wait()
    report = {'document': 'P3109 v4.1, 14 September 2026, unapproved draft',
              'clauses': ['4.7.4', '4.7.5', '4.7.6'],
              'reference': 'independent Python Fraction; report logarithmic quantum and fraction formulas',
              'descriptors': descriptors, 'rational_inputs': observations, 'projections': projections,
              'modes_per_input': len(MODES), 'random_widths': [0, 1, 2, 3],
              'producer_exit': code, 'first_mismatches': mismatches,
              'sha256': digest.hexdigest(), 'status': 'pass' if code == 0 and not mismatches else 'fail'}
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if report['status'] != 'pass':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
