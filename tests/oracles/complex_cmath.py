#!/usr/bin/env python3
"""Compare the special values of FloatLib's complex functions with CPython's cmath, in binary64.

cmath has its own tables of special values, written independently of FloatLib, so this is a
check of FloatLib's tables (C23 Annex G, working draft N3220) against a second implementation.
The Lean executable `oracle complex` evaluates each function, rounding to nearest, at every pair
of the parts `±0, ±0.5, ±1, ±2, ±∞, NaN`. cmath raises `ValueError` or `OverflowError` at some
arguments, where C signals "invalid", a pole or an overflow, so the comparison covers the
arguments at which it returns a value. A part is compared by its class, a NaN, an infinity or a
zero with its sign, or a finite value, which has to agree to twelve digits since cmath is not
correctly rounded.

Two kinds of difference are expected, and counted apart:

* a sign that Annex G leaves unspecified (`UNSPECIFIED` lists those rows of G.6.2.1, G.6.3.1 to
  G.6.3.6, G.6.4.1 and G.6.5.2, and the rows that G.6.1, paragraph 8, derives from them for the
  circular functions);
* a row at which N3220 specifies a value and cmath returns `NaN + i NaN`:
  `ctanh (0 + i NaN) = 0 + i NaN` (G.6.3.6), with `ctan (NaN + i 0) = NaN + i 0` derived from it,
  and `cacosh (0 + i NaN) = NaN ± i π / 2` (G.6.3.1). FloatLib has to return the row of N3220.

Any other difference is a failure. Usage:

    python3 tests/oracles/complex_cmath.py --oracle PATH
"""

import argparse
import cmath
import math
import struct
import subprocess
import sys

FUNCTIONS = ["sqrt", "exp", "log", "sin", "cos", "tan", "sinh", "cosh", "tanh", "asin", "acos",
             "atan", "asinh", "acosh", "atanh"]
VALUES = [0.0, -0.0, 0.5, -0.5, 1.0, -1.0, 2.0, -2.0, math.inf, -math.inf, math.nan]

# Rows of Annex G with an unspecified sign: the classes of the two parts of the argument, without
# their signs, and the part of the result whose sign is open.
UNSPECIFIED = {
    "acos": [("inf", "nan", "im")],
    "acosh": [("zero", "nan", "im")],
    "asinh": [("nan", "inf", "re")],
    "atanh": [("nan", "inf", "re")],
    "cosh": [("zero", "inf", "im"), ("zero", "nan", "im"), ("inf", "inf", "re"),
             ("nan", "zero", "im")],
    "sinh": [("zero", "inf", "re"), ("zero", "nan", "re"), ("inf", "inf", "re"),
             ("inf", "nan", "re")],
    "tanh": [("inf", "inf", "im"), ("inf", "nan", "im")],
    "exp": [("inf", "inf", "both"), ("inf", "nan", "both")],
    "sqrt": [("inf", "nan", "im")],
}
# G.6.1, paragraph 8: `f z = -i g (i z)` exchanges the parts of the argument and of the result,
# and `ccos z = ccosh (i z)` exchanges the parts of the argument.
SWAP = {"re": "im", "im": "re", "both": "both"}
for circular, hyperbolic in (("sin", "sinh"), ("tan", "tanh"), ("asin", "asinh"),
                             ("atan", "atanh")):
    UNSPECIFIED[circular] = [(im, re, SWAP[part]) for re, im, part in UNSPECIFIED[hyperbolic]]
UNSPECIFIED["cos"] = [(im, re, part) for re, im, part in UNSPECIFIED["cosh"]]


def word(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def value(w):
    return struct.unpack("<d", struct.pack("<Q", w))[0]


def kind(x):
    """The class of a part without its sign."""
    if math.isnan(x):
        return "nan"
    if math.isinf(x):
        return "inf"
    return "zero" if x == 0 else "finite"


def negative(x):
    return math.copysign(1.0, x) < 0


def same(ours, theirs):
    if kind(ours) != kind(theirs):
        return False
    if kind(ours) == "nan":
        return True
    if kind(ours) == "finite":
        return math.isclose(ours, theirs, rel_tol=1e-12)
    return negative(ours) == negative(theirs)


def unspecified(name, x, y, ours, reference):
    """Whether the results differ only in signs that Annex G leaves open at this argument."""
    for re_kind, im_kind, part in UNSPECIFIED.get(name, []):
        if (kind(x), kind(y)) != (re_kind, im_kind):
            continue
        open_parts = {"re": (True, False), "im": (False, True), "both": (True, True)}[part]
        if all(same(a, b) or (free and kind(a) == kind(b) and kind(a) in ("zero", "inf"))
               for a, b, free in zip(ours, reference, open_parts)):
            return True
    return False


def row_of_c23(name, x, y, ours):
    """Whether FloatLib returns the row of N3220 at an argument where cmath returns NaNs."""
    if name == "tanh" and kind(x) == "zero" and kind(y) == "nan":
        return kind(ours[0]) == "zero" and negative(ours[0]) == negative(x) and (
            kind(ours[1]) == "nan")
    if name == "tan" and kind(x) == "nan" and kind(y) == "zero":
        return kind(ours[0]) == "nan" and kind(ours[1]) == "zero" and (
            negative(ours[1]) == negative(y))
    if name == "acosh" and kind(x) == "zero" and kind(y) == "nan":
        return kind(ours[0]) == "nan" and math.isclose(abs(ours[1]), math.pi / 2, rel_tol=1e-15)
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--oracle", required=True, help="path of the built `oracle` executable")
    args = parser.parse_args()
    pairs = [(x, y) for x in VALUES for y in VALUES]
    print("| function | arguments | cmath returns a value | agree | sign unspecified by C | "
          "C23 row | failures |")
    print("|---|---|---|---|---|---|---|")
    notes = []
    failures = 0
    for name in FUNCTIONS:
        requests = "".join(f"{name} 11 52 nearest {word(x)} {word(y)}\n" for x, y in pairs)
        answers = subprocess.run([args.oracle, "complex"], input=requests, capture_output=True,
                                 text=True, check=True).stdout.splitlines()
        if len(answers) != len(pairs):
            raise RuntimeError(f"{name}: expected {len(pairs)} answers, got {len(answers)}")
        returned = agree = open_sign = c23 = failed = 0
        for (x, y), answer in zip(pairs, answers):
            try:
                result = getattr(cmath, name)(complex(x, y))
            except (ValueError, OverflowError):
                continue
            returned += 1
            reference = (result.real, result.imag)
            ours = tuple(value(int(field)) for field in answer.split())
            line = (f"`{name}({x!r} + {y!r}i)`: FloatLib `{ours[0]!r} + {ours[1]!r}i`, "
                    f"cmath `{reference[0]!r} + {reference[1]!r}i`")
            if same(ours[0], reference[0]) and same(ours[1], reference[1]):
                agree += 1
            elif row_of_c23(name, x, y, ours):
                c23 += 1
                notes.append("- C23 row: " + line)
            elif unspecified(name, x, y, ours, reference):
                open_sign += 1
                notes.append("- sign unspecified: " + line)
            else:
                failed += 1
                notes.append("- FAIL: " + line)
        failures += failed
        print(f"| {name} | {len(pairs)} | {returned} | {agree} | {open_sign} | {c23} | {failed} |")
    print()
    print("\n".join(notes))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
