#!/usr/bin/env python3
"""Draw content/assets/ch06-three-readings.png: one binary32 word read three ways.

Chapter 06 reads a stored word as bits, as an exact dyadic and as a real number, and names the
function for each step. The figure follows the chapter's own example word `tiny32`, the
binary32 word nearest to 1e-8, down that chain: a word with three field widths and values,
its exact dyadic components, and its real value. Short arrow labels name the two operations;
the chapter retains their full Lean names. The phone version stacks the three readings.

Sources:

* the word, `Model.ofNatBits 0x322bcc77`, and its decoded record
  `{ negative := false, significand := 11258999, exponent := -50 }` are the chapter's Lean
  block and its printed result (site/content/chapters/06-the-numerical-models.md); the script
  recomputes the record from the bits and asserts agreement, and does the same for the
  chapter's `one32` (0x3f800000, significand 8388608, exponent -23) and for the least
  subnormal (significand 1, exponent -149);
* the format parameters are `FloatFormat.binary32` in
  FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean (expWidth 8, fracWidth 23,
  exponentBias 127), and the decoding rule is that of `toDyadic?` in
  FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean, with the subnormal exponent
  `minSubnormalExponent = 1 - exponentBias - fracWidth` from Format/Properties.lean;
* field extraction, dyadic decoding and real interpretation follow `Model.signBit`,
  `Model.expField`, `Model.fracField`, `Model.toDyadic?` and `Dyadic.toReal`;
* the decimal expansion of 11258999 / 2^50 is computed exactly with Python's `decimal` module
  and cut after twelve significant digits.

Run from anywhere: python3 ch06_three_readings.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

# FloatFormat.binary32 (Format/Catalog.lean).
EXP_WIDTH = 8
FRAC_WIDTH = 23
BIAS = 127
assert BIAS == 2 ** (EXP_WIDTH - 1) - 1      # FloatFormat.ieeeBias 8
TOTAL = 1 + EXP_WIDTH + FRAC_WIDTH
MIN_SUBNORMAL_EXP = 1 - BIAS - FRAC_WIDTH    # FloatFormat.minSubnormalExponent
ALL_ONES = 2 ** EXP_WIDTH - 1

SIGN_COLOUR = fs.PURPLE
EXP_COLOUR = fs.ORANGE
FRAC_COLOUR = fs.SKY
FIELDS = [(1, SIGN_COLOUR), (EXP_WIDTH, EXP_COLOUR), (FRAC_WIDTH, FRAC_COLOUR)]
MONO = "DejaVu Sans Mono"

TINY32 = 0x322BCC77
ONE32 = 0x3F800000


def fields_of(word: int) -> tuple[int, int, int]:
    """Model.signBit, Model.expField and Model.fracField, by masking."""
    sign = word >> (TOTAL - 1)
    exp_field = (word >> FRAC_WIDTH) & ALL_ONES
    frac_field = word & (2 ** FRAC_WIDTH - 1)
    return sign, exp_field, frac_field


def to_dyadic(word: int) -> tuple[bool, int, int] | None:
    """Model.toDyadic? for an IEEE descriptor: None for NaN and infinity."""
    sign, exp_field, frac_field = fields_of(word)
    if exp_field == ALL_ONES:
        return None
    if exp_field == 0:
        return (bool(sign), frac_field, MIN_SUBNORMAL_EXP if frac_field else 0)
    return (bool(sign), 2 ** FRAC_WIDTH + frac_field, exp_field - BIAS - FRAC_WIDTH)


def dyadic_value(d: tuple[bool, int, int]) -> Fraction:
    negative, significand, exponent = d
    value = significand * Fraction(2) ** exponent
    return -value if negative else value


def significant_digits(value: Fraction, digits: int) -> str:
    """Scientific notation, exact arithmetic, cut (not rounded) after `digits` significant digits."""
    getcontext().prec = 80
    exact = Decimal(value.numerator) / Decimal(value.denominator)
    exponent = exact.adjusted()
    mantissa = exact.scaleb(-exponent)
    text = str(mantissa)
    integer, _, fraction = text.partition(".")
    return f"{integer}.{fraction[:digits - 1]}... x 10^{exponent}"


def draw(mobile: bool):
    """One finite word; the two arrows interpret it without rounding."""
    fig = plt.figure(figsize=(3.8, 6.5) if mobile else (9, 3.65))
    fig.text(0.035, 0.97, "One word, three readings", va="top", fontsize=14, weight="bold")
    fig.text(0.035, 0.89 if mobile else 0.85,
             r"binary32 nearest to $10^{-8}$", fontsize=12, color=fs.MUTED)
    positions = ([(0.035, y, 0.93, 0.205) for y in (0.655, 0.37, 0.085)] if mobile else
                 [(x, 0.20, 0.285, 0.55) for x in (0.025, 0.3575, 0.69)])
    for i, rect in enumerate(positions):
        ax = fig.add_axes(rect)
        ax.set(xlim=(0, 1), ylim=(0, 1))
        ax.axis("off")
        ax.add_patch(Rectangle((0, 0), 1, 1, facecolor=fs.PAPER_2,
                               edgecolor=fs.LINE, linewidth=0.8))
        ax.text(0.06, 0.87, ("1  Stored bits", "2  Exact dyadic", "3  Real value")[i],
                fontsize=12, weight="bold", va="center")
        if i == 0:
            ax.text(0.06, 0.63, "0x322bcc77", family=MONO, fontsize=14)
            x = 0.06
            for width, colour in FIELDS:
                ax.add_patch(Rectangle((x, 0.41), 0.88 * width / TOTAL, 0.09,
                                       facecolor=colour, edgecolor="white", linewidth=0.7))
                x += 0.88 * width / TOTAL
            ax.text(0.06, 0.24, "sign 0    exponent 100", fontsize=11.5)
            ax.text(0.06, 0.07, "fraction 2870391", fontsize=11.5)
        elif i == 1:
            ax.text(0.06, 0.60, "positive", fontsize=12)
            ax.text(0.06, 0.36, "significand 11258999", fontsize=11.5)
            ax.text(0.06, 0.12, "exponent −50", fontsize=11.5)
        else:
            ax.text(0.06, 0.60, r"$11258999 \times 2^{-50}$", fontsize=14)
            ax.text(0.06, 0.34, r"$= 9.99999993922\ldots$", fontsize=12)
            ax.text(0.06, 0.12, r"$\phantom{=}\times 10^{-9}$", fontsize=12)
    arrow_ax = fig.add_axes([0, 0, 1, 1], zorder=0)
    arrow_ax.axis("off")
    for i, label in enumerate(("decode", "interpret")):
        if mobile:
            upper = positions[i][1]
            lower = positions[i + 1][1] + positions[i + 1][3]
            arrow_ax.annotate("", (0.5, lower + 0.005), (0.5, upper - 0.005),
                              arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.2))
            arrow_ax.text(0.54, (upper + lower) / 2, label, fontsize=11.5, va="center")
        else:
            start = positions[i][0] + positions[i][2]
            end = positions[i + 1][0]
            arrow_ax.annotate("", (end - 0.003, 0.46), (start + 0.003, 0.46),
                              arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.2))
            arrow_ax.text((start + end) / 2, 0.11, label, fontsize=11.5, ha="center")
    fig.text(0.035, 0.015,
             "Same finite value; neither step rounds.", fontsize=11.5, color=fs.MUTED)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    assert to_dyadic(TINY32) == (False, 11258999, -50)
    assert to_dyadic(ONE32) == (False, 8388608, -23)
    assert to_dyadic(1) == (False, 1, -149)
    assert fields_of(TINY32) == (0, 100, 2870391)
    value = dyadic_value(to_dyadic(TINY32))
    assert value == Fraction(11258999, 2 ** 50)
    assert significant_digits(value, 12) == "9.99999993922... x 10^-9"
    fs.setup()
    out = args.out or fs.ASSETS / "ch06-three-readings.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
