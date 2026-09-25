#!/usr/bin/env python3
"""Draw content/assets/ch13-element-values.png: seven small formats and their value sets.

One row per format: E5M2, E4M3FN, E4M3FNUZ, E5M2FNUZ, E2M3, E3M2 and E2M1, in the order chapter 09
introduces them. The desktop rows give the sign, exponent and fraction widths as numbers.
Every positive finite value is a tick on a common logarithmic scale, tall for a normal value
and short for a subnormal one. The phone version stacks seven panels with readable limits,
counts and axis labels. Zero has no place on a logarithmic axis; infinities and NaNs are also
excluded. Each row therefore contains exactly the positive finite values of its format.

Sources. The descriptors are those of
FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean: `e5m2 = ieee 5 2`,
`e4m3fn = finiteMaxNaN 4 3`, `e4m3fnuz = finiteUnsignedZero 4 3`,
`e5m2fnuz = finiteUnsignedZero 5 2`, `e2m3 = finite 2 3`, `e3m2 = finite 3 2`, `e2m1 = finite 2 1`,
with the biases the constructors in Format/Definition.lean assign: `ieeeBias w = 2^(w-1) - 1`
for `ieee`, `finiteMaxNaN` and `finite`, and `ieeeBias w + 1` for `finiteUnsignedZero`. Which
words are numbers follows the classifiers of
FloatLib/Floats/Formats/BinaryInterchange/Model/Carrier.lean: under `ieee` an all-ones exponent
is an infinity (zero fraction) or a NaN; under `finiteMaxNaN` only the word with all exponent and
all fraction bits set is NaN, for either sign; under `finiteUnsignedZero` only the word equal to
the sign mask (negative zero) is NaN and only the all-zero word is zero; under `finite` every word
is a number. The value of a finite word follows `toDyadic?` in
FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean and `ieeeToDyadic?` in
Dyadic/Core.lean: a zero exponent field denotes fraction * 2^(1 - bias - fracWidth), any other
exponent field E denotes (2^fracWidth + fraction) * 2^(E - bias - fracWidth).

Before drawing, the script checks its own arithmetic against two `-- ` results printed in the
chapter: the sixteen E2M1 codes decode to 0, 1/2, 1, 3/2, 2, 3, 4, 6 and their negatives, and the
largest finite values of e2m1, e2m3, e3m2, e4m3fn, e4m3fnuz, e5m2, e5m2fnuz are
6, 15/2, 28, 448, 240, 57344, 57344.

Run from anywhere: python3 ch13_element_values.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402

IEEE, FINITE_MAX_NAN, FINITE_UNSIGNED_ZERO, FINITE = "ieee", "finiteMaxNaN", "finiteUnsignedZero", "finite"


def ieee_bias(exp_width: int) -> int:
    """`FloatFormat.ieeeBias`."""
    return 2 ** (exp_width - 1) - 1


def descriptor(name: str, encoding: str, exp_width: int, frac_width: int) -> dict:
    """The four data fields of a `FloatFormat` built by the named constructor."""
    bias = ieee_bias(exp_width) + (1 if encoding == FINITE_UNSIGNED_ZERO else 0)
    return {"name": name, "encoding": encoding, "expWidth": exp_width, "fracWidth": frac_width,
            "bias": bias}


# In the order the chapter introduces them.
FORMATS = (
    descriptor("E5M2", IEEE, 5, 2),
    descriptor("E4M3FN", FINITE_MAX_NAN, 4, 3),
    descriptor("E4M3FNUZ", FINITE_UNSIGNED_ZERO, 4, 3),
    descriptor("E5M2FNUZ", FINITE_UNSIGNED_ZERO, 5, 2),
    descriptor("E2M3", FINITE, 2, 3),
    descriptor("E3M2", FINITE, 3, 2),
    descriptor("E2M1", FINITE, 2, 1),
)


def fields(fmt: dict, word: int) -> tuple[int, int, int]:
    """Sign, exponent field, fraction field of a stored word."""
    frac = word & ((1 << fmt["fracWidth"]) - 1)
    exp = (word >> fmt["fracWidth"]) & ((1 << fmt["expWidth"]) - 1)
    sign = word >> (fmt["expWidth"] + fmt["fracWidth"])
    return sign, exp, frac


def is_nan(fmt: dict, word: int) -> bool:
    sign, exp, frac = fields(fmt, word)
    all_ones_exp = (1 << fmt["expWidth"]) - 1
    all_ones_frac = (1 << fmt["fracWidth"]) - 1
    if fmt["encoding"] == IEEE:
        return exp == all_ones_exp and frac != 0
    if fmt["encoding"] == FINITE_MAX_NAN:
        return exp == all_ones_exp and frac == all_ones_frac
    if fmt["encoding"] == FINITE_UNSIGNED_ZERO:
        return word == 1 << (fmt["expWidth"] + fmt["fracWidth"])  # the sign mask
    return False


def is_inf(fmt: dict, word: int) -> bool:
    _sign, exp, frac = fields(fmt, word)
    return fmt["encoding"] == IEEE and exp == (1 << fmt["expWidth"]) - 1 and frac == 0


def to_rational(fmt: dict, word: int) -> Fraction | None:
    """`Model.toDyadic?` as an exact rational; None for infinities and NaNs."""
    if is_nan(fmt, word) or is_inf(fmt, word):
        return None
    sign, exp, frac = fields(fmt, word)
    if fmt["encoding"] == FINITE_UNSIGNED_ZERO and word == 0:
        return Fraction(0)
    if exp == 0:
        value = Fraction(frac) * Fraction(2) ** (1 - fmt["bias"] - fmt["fracWidth"])
    else:
        value = Fraction((1 << fmt["fracWidth"]) + frac) * Fraction(2) ** (exp - fmt["bias"] - fmt["fracWidth"])
    return -value if sign else value


def positive_values(fmt: dict) -> tuple[list[Fraction], list[Fraction]]:
    """Positive finite nonzero values, split into (normals, subnormals)."""
    normals, subnormals = [], []
    for exp in range(1 << fmt["expWidth"]):
        for frac in range(1 << fmt["fracWidth"]):
            word = (exp << fmt["fracWidth"]) | frac
            value = to_rational(fmt, word)
            if value is None or value == 0:
                continue
            (subnormals if exp == 0 else normals).append(value)
    return normals, subnormals


def check_against_chapter() -> None:
    by_name = {f["name"]: f for f in FORMATS}
    e2m1 = by_name["E2M1"]
    codes = [to_rational(e2m1, code) for code in range(16)]
    expected = [Fraction(v) for v in (0, "1/2", 1, "3/2", 2, 3, 4, 6, 0, "-1/2", -1, "-3/2", -2, -3, -4, -6)]
    assert codes == expected, codes
    maxima = [max(positive_values(by_name[n])[0]) for n in
              ("E2M1", "E2M3", "E3M2", "E4M3FN", "E4M3FNUZ", "E5M2", "E5M2FNUZ")]
    assert maxima == [Fraction(v) for v in (6, "15/2", 28, 448, 240, 57344, 57344)], maxima


def rational_label(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def power_of_two_label(value: Fraction) -> str:
    """`2^k` for a value of the form 1/2^k (every least subnormal here is one), else the fraction."""
    if value.numerator == 1 and value.denominator & (value.denominator - 1) == 0:
        return f"$2^{{{-(value.denominator.bit_length() - 1)}}}$"
    return rational_label(value)


NORMAL_COLOUR = fs.BLUE
SUBNORMAL_COLOUR = fs.VERMILION

def draw(mobile: bool):
    fig = plt.figure(figsize=(3.8, 10.3) if mobile else (9, 6.3))
    fig.text(0.035, 0.98, "Which positive values fit?", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.93 if mobile else 0.90,
             "Tall blue ticks: normal\nShort orange ticks: subnormal" if mobile else
             "Tall blue ticks: normal     Short orange ticks: subnormal",
             fontsize=11.5, linespacing=1.4)
    for i, fmt in enumerate(FORMATS):
        normals, subnormals = positive_values(fmt)
        smallest, largest = min(subnormals), max(normals)
        bits = 1 + fmt["expWidth"] + fmt["fracWidth"]
        if mobile:
            y = 0.82 - i * 0.113
            fig.text(0.035, y + 0.043, f"{fmt['name']}  ({bits} bits)", fontsize=12, weight="bold")
            fig.text(0.035, y + 0.016,
                     f"{power_of_two_label(smallest)} to {rational_label(largest)}; "
                     f"{len(normals) + len(subnormals)} values", fontsize=11.5)
            ax = fig.add_axes([0.09, y - 0.029, 0.84, 0.035])
        else:
            y = 0.78 - i * 0.102
            fig.text(0.035, y, fmt["name"], fontsize=12, weight="bold")
            fig.text(0.035, y - 0.032,
                     f"{bits} bits: 1 + {fmt['expWidth']} + {fmt['fracWidth']}", fontsize=11,
                     color=fs.MUTED)
            fig.text(0.25, y, f"{power_of_two_label(smallest)} to {rational_label(largest)}",
                     fontsize=11.5)
            fig.text(0.25, y - 0.032, f"{len(normals) + len(subnormals)} positive values",
                     fontsize=11, color=fs.MUTED)
            ax = fig.add_axes([0.46, y - 0.033, 0.50, 0.062])
        ax.set_xscale("log", base=2)
        ax.set_xlim(2.0 ** -18, 2.0 ** 17)
        ax.set_ylim(-0.42, 0.42)
        ax.vlines([float(v) for v in normals], -0.3, 0.3, color=NORMAL_COLOUR, lw=0.9)
        ax.vlines([float(v) for v in subnormals], -0.16, 0.16, color=SUBNORMAL_COLOUR, lw=1)
        ks = [-16, -8, 0, 8, 16]
        ax.set_xticks([2.0 ** k for k in ks],
                      labels=[f"$2^{{{k}}}$" if k else "$1$" for k in ks])
        ax.tick_params(axis="x", labelsize=11, length=2, pad=2)
        ax.set_yticks([])
        ax.minorticks_off()
        ax.spines['left'].set_visible(False)
        ax.spines['bottom'].set_visible(False)
        if not mobile and i != len(FORMATS) - 1:
            ax.set_xticklabels([])
    fig.text(0.035, 0.03 if mobile else 0.01,
             "Same logarithmic value axis in every row.\nZero, infinities and NaNs are not plotted."
             if mobile else
             "Fields: sign + exponent + fraction.  Same logarithmic value axis; zero, infinities and NaNs omitted.",
             fontsize=11.5, color=fs.MUTED, linespacing=1.5)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    check_against_chapter()
    fs.setup()
    out = args.out or fs.ASSETS / "ch13-element-values.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
