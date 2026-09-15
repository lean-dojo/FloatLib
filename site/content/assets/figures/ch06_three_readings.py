#!/usr/bin/env python3
"""Draw content/assets/ch06-three-readings.png: one binary32 word read three ways.

Chapter 06 reads a stored word as bits, as an exact dyadic and as a real number, and names the
function for each step. The figure follows the chapter's own example word `tiny32`, the
binary32 word nearest to 1e-8, down that chain: the 32 bits with their three fields, the
`Dyadic` record `toDyadic?` returns, and the real number `Dyadic.toReal` gives it.

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
* the function names on the arrows (`Model.signBit`, `Model.expField`, `Model.fracField`,
  `Model.toDyadic?`, `Dyadic.toReal`, `Model.toReal`) are copied from the chapter's node links;
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
from matplotlib.colors import to_rgba  # noqa: E402
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


def bit_cells(ax, word: int, *, x0: float, y: float, height: float = 0.8) -> None:
    x = x0
    bit = TOTAL - 1
    for width, colour in FIELDS:
        for _ in range(width):
            ax.add_patch(Rectangle((x, y), 1, height, facecolor=to_rgba(colour, 0.38),
                                   edgecolor=fs.INK, linewidth=0.6))
            ax.text(x + 0.5, y + height / 2, str((word >> bit) & 1), ha="center", va="center",
                    fontsize=9, family=MONO, color=fs.INK)
            x += 1
            bit -= 1


def heading(ax, y: float, number: str, text: str, names: str) -> None:
    ax.text(0, y, f"{number} {text}", ha="left", va="bottom", fontsize=10, color=fs.INK)
    ax.text(TOTAL, y, names, ha="right", va="bottom", fontsize=9, family=MONO, color=fs.MUTED)


def step_arrow(ax, y_from: float, y_to: float, name: str, note: str) -> None:
    x = TOTAL / 2
    fs.arrow(ax, (x, y_from), (x, y_to), color=fs.INK, linewidth=1.2, shrink=0.0)
    ax.text(x + 0.6, (y_from + y_to) / 2 + 0.05, name, ha="left", va="bottom", fontsize=9.5,
            family=MONO, color=fs.INK)
    ax.text(x + 0.6, (y_from + y_to) / 2 - 0.05, note, ha="left", va="top", fontsize=9,
            color=fs.MUTED)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    # The chapter's printed results.
    assert to_dyadic(TINY32) == (False, 11258999, -50)
    assert to_dyadic(ONE32) == (False, 8388608, -23)
    assert to_dyadic(1) == (False, 1, -149)
    sign, exp_field, frac_field = fields_of(TINY32)
    assert (sign, exp_field, frac_field) == (0, 100, 2870391)
    dyadic = to_dyadic(TINY32)
    assert dyadic is not None
    value = dyadic_value(dyadic)
    assert value == Fraction(11258999, 2 ** 50)
    decimal_text = significant_digits(value, 12)

    xlim = (-0.6, TOTAL + 0.6)
    ylim = (6.7, 22.4)
    height = fs.WIDTH * (ylim[1] - ylim[0]) / (xlim[1] - xlim[0])
    fig = plt.figure(figsize=(fs.WIDTH, height))
    ax = fs.diagram_axes(fig, xlim, ylim)

    ax.text(0, 22.3, "One binary32 word, three readings: tiny32 = Model.ofNatBits 0x322bcc77, "
            "the word nearest to $10^{-8}$", ha="left", va="top", fontsize=10.5, color=fs.INK)

    # First reading: the bits and their fields.
    heading(ax, 20.35, "1.", "the bits, a BitVec 32 in the single field Model.bits",
            "Model.signBit   Model.expField   Model.fracField")
    bit_cells(ax, TINY32, x0=0, y=19.15)
    for (lo, hi), text in zip(((0, 1), (1, 1 + EXP_WIDTH), (1 + EXP_WIDTH, TOTAL)),
                              (f"s = {sign}", f"E = {exp_field:08b} = {exp_field}",
                               f"F = {frac_field} = 0x{frac_field:06x}")):
        ax.text((lo + hi) / 2, 18.95, text, ha="center", va="top", fontsize=9.5, color=fs.INK)

    step_arrow(ax, 18.2, 16.55, "Model.toDyadic?",
               "some for every finite word, none for a NaN or an infinity")

    # Second reading: the exact dyadic.
    heading(ax, 15.8, "2.", "the exact value, a FloatLib.Numerics.Dyadic record", "")
    fs.box(ax, 0, 13.45, TOTAL, 2.1, "", facecolor=fs.PAPER_2, rounding=0.2)
    ax.text(TOTAL / 2, 14.95, "{ negative := false, significand := 11258999, exponent := -50 }",
            ha="center", va="center", fontsize=9.5, family=MONO, color=fs.INK)
    ax.text(TOTAL / 2, 14.0, r"significand $= 2^{23} + F = 8388608 + 2870391$, "
            r"exponent $= E - 127 - 23 = 100 - 150$, the hidden bit made explicit",
            ha="center", va="center", fontsize=9, color=fs.MUTED)

    step_arrow(ax, 13.15, 11.5, "Dyadic.toReal",
               "Model.toReal is this composed with toDyadic?, with 0 for none")

    # Third reading: the real number.
    heading(ax, 10.75, "3.", "the real number, the value the error bounds are stated about",
            "Model.toReal")
    fs.box(ax, 0, 8.6, TOTAL, 1.9, "", facecolor=fs.PAPER_2, rounding=0.2)
    ax.text(TOTAL / 2, 9.55, r"$11258999 \cdot 2^{-50} = 11258999 \,/\, 1125899906842624 = "
            + decimal_text.replace("x 10^", r"\times 10^{").replace("...", r"\ldots") + "}$",
            ha="center", va="center", fontsize=10, color=fs.INK)

    ax.text(0, 8.05, "The word never carries a second copy of its value: every reading is "
            "recomputed from the bits, and a real-valued theorem\nabout a word is only informative "
            "when the word is finite, which is why the finiteness hypotheses appear in every one.",
            ha="left", va="top", fontsize=9, color=fs.MUTED, linespacing=1.3)

    out = fs.save(fig, "ch06-three-readings.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
