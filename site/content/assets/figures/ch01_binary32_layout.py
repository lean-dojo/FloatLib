#!/usr/bin/env python3
"""Draw content/assets/ch01-binary32-layout.png: the three fields of a binary32 word.

Chapter 02 builds a format from a sign bit, an exponent field and a fraction field, and then
reads two concrete words. The figure shows the field layout of binary32, the stored words for
0.1 and -2.5 with each bit coloured by its field, the three field values read off each word,
and the decoding rules for a normal and for a subnormal word.

Sources:

* the format parameters are `FloatFormat.binary32` in
  FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean (expWidth 8, fracWidth 23,
  exponentBias 127, which is `ieeeBias 8 = 2^7 - 1` in Format/Definition.lean; the storage
  width is `bitWidth = 1 + 8 + 23`);
* the word for 0.1 is derived here from the value the chapter prints for the literal,
  `13421773 * 2^-27` (site/content/chapters/02-from-reals-to-machine-numbers.md, the `toString`
  result), by normalising the significand to 24 bits and biasing the exponent;
* the word for -2.5 is derived the same way from the value -2.5 and checked against the
  chapter's `toBits32 (-2.5 : Binary32)` result, 3223322624 (0xc0200000); the chapter's results
  for 1 and 2, 1065353216 and 1073741824, are checked the same way;
* the decoding rules are the chapter's formulas, (-1)^s (1 + F / 2^23) 2^(E - 127) for a normal
  word and (-1)^s F 2^(1 - 127 - 23) for a subnormal one, which are the two branches of
  `toDyadic?` in FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean.

Run from anywhere: python3 ch01_binary32_layout.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
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
BIAS = 2 ** (EXP_WIDTH - 1) - 1          # FloatFormat.ieeeBias 8
assert BIAS == 127
TOTAL = 1 + EXP_WIDTH + FRAC_WIDTH       # FloatFormat.bitWidth
PRECISION = FRAC_WIDTH + 1

SIGN_COLOUR = fs.PURPLE
EXP_COLOUR = fs.ORANGE
FRAC_COLOUR = fs.SKY
FIELDS = [("s", 1, SIGN_COLOUR), ("exponent E (8 bits)", EXP_WIDTH, EXP_COLOUR),
          ("fraction F (23 bits)", FRAC_WIDTH, FRAC_COLOUR)]
MONO = "DejaVu Sans Mono"


def encode_normal(value: Fraction) -> int:
    """The binary32 word of a value that lies in the normal range, from the chapter's rule.

    Write |value| = m * 2^e with 2^23 <= m < 2^24 (normalisation), then F = m - 2^23 (the hidden
    bit is dropped) and E = e + 23 + 127 (the bias). Raises if the value is not representable.
    """
    negative = value < 0
    magnitude = abs(value)
    exponent = 0
    while magnitude >= 2 ** PRECISION:
        magnitude /= 2
        exponent += 1
    while magnitude < 2 ** (PRECISION - 1):
        magnitude *= 2
        exponent -= 1
    if magnitude.denominator != 1:
        raise ValueError(f"{value} is not a binary32 value")
    significand = magnitude.numerator
    biased = exponent + FRAC_WIDTH + BIAS
    assert 0 < biased < 2 ** EXP_WIDTH - 1
    return (int(negative) << (TOTAL - 1)) | (biased << FRAC_WIDTH) | (significand - 2 ** FRAC_WIDTH)


def fields_of(word: int) -> tuple[int, int, int]:
    sign = word >> (TOTAL - 1)
    exp_field = (word >> FRAC_WIDTH) & (2 ** EXP_WIDTH - 1)
    frac_field = word & (2 ** FRAC_WIDTH - 1)
    return sign, exp_field, frac_field


def bit_cells(ax, word: int, *, y: float, height: float = 0.8) -> None:
    """One cell per bit, most significant first, tinted by the field the bit belongs to."""
    x = 0.0
    bit = TOTAL - 1
    for _name, width, colour in FIELDS:
        for _ in range(width):
            ax.add_patch(Rectangle((x, y), 1, height, facecolor=to_rgba(colour, 0.38),
                                   edgecolor=fs.INK, linewidth=0.6))
            ax.text(x + 0.5, y + height / 2, str((word >> bit) & 1), ha="center", va="center",
                    fontsize=9, family=MONO, color=fs.INK)
            x += 1
            bit -= 1


def field_readings(ax, word: int, *, y: float) -> None:
    sign, exp_field, frac_field = fields_of(word)
    spans = [(0, 1), (1, 1 + EXP_WIDTH), (1 + EXP_WIDTH, TOTAL)]
    texts = [f"s = {sign}", f"E = {exp_field:08b} = {exp_field}",
             f"F = {frac_field} = 0x{frac_field:06x}"]
    for (lo, hi), text in zip(spans, texts):
        ax.text((lo + hi) / 2, y, text, ha="center", va="top", fontsize=9.5, color=fs.INK)


def example_row(ax, word: int, title: str, value_line: str, *, y: float) -> None:
    ax.text(0, y + 0.95, title, ha="left", va="bottom", fontsize=9.5, color=fs.INK)
    ax.text(TOTAL, y + 0.95, f"0x{word:08x} = {word}", ha="right", va="bottom", fontsize=9.5,
            family=MONO, color=fs.MUTED)
    bit_cells(ax, word, y=y)
    field_readings(ax, word, y=y - 0.2)
    ax.text(TOTAL / 2, y - 1.05, value_line, ha="center", va="top", fontsize=10, color=fs.INK)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()

    # The chapter's values, and the words the chapter prints for them.
    tenth = Fraction(13421773, 2 ** 27)
    word_tenth = encode_normal(tenth)
    assert word_tenth == 0x3DCCCCCD
    word_neg = encode_normal(Fraction(-5, 2))
    assert word_neg == 3223322624 == 0xC0200000
    assert encode_normal(Fraction(1)) == 1065353216
    assert encode_normal(Fraction(2)) == 1073741824
    s, e, f = fields_of(word_tenth)
    assert (s, e, f) == (0, 123, 5033165)
    assert (2 ** FRAC_WIDTH + f) * Fraction(2) ** (e - BIAS - FRAC_WIDTH) == tenth
    s2, e2, f2 = fields_of(word_neg)
    assert (s2, e2, f2) == (1, 128, 2 ** 21)

    xlim = (-0.6, TOTAL + 0.6)
    ylim = (-0.3, 19.2)
    height = fs.WIDTH * (ylim[1] - ylim[0]) / (xlim[1] - xlim[0])
    fig = plt.figure(figsize=(fs.WIDTH, height))
    ax = fs.diagram_axes(fig, xlim, ylim)

    # Generic layout.
    ax.text(0, 18.7, "binary32: one sign bit, 8 exponent bits, 23 fraction bits "
            "(FloatFormat.binary32, bias 127)", ha="left", va="top", fontsize=10.5, color=fs.INK)
    # The sign field is too narrow for a name inside its cell, so it is named below the row.
    generic = [("", 1, SIGN_COLOUR)] + FIELDS[1:]
    fs.bit_layout(ax, generic, y=16.6, height=0.8, name_size=9.5, index_size=9)
    ax.text(0.5, 16.6 - 0.2, "sign s", ha="center", va="top", fontsize=9, color=fs.INK)

    # The two example words.
    example_row(ax, word_tenth,
                f"the literal 0.1, rounded to {PRECISION} significant bits",
                r"value $= (1 + 5033165 / 2^{23}) \cdot 2^{123 - 127} "
                r"= 13421773 \cdot 2^{-27} = 0.100000001490116119384765625$",
                y=12.9)
    example_row(ax, word_neg, "the value -2.5, which exercises all three fields",
                r"value $= -(1 + 2^{21} / 2^{23}) \cdot 2^{128 - 127} = -(1 + 1/4) \cdot 2 = -2.5$",
                y=8.1)

    # Decoding rules.
    ax.plot([0, TOTAL], [4.2, 4.2], color=fs.LINE, linewidth=0.8)
    rules = [
        (r"normal word, $0 < E < 255$:  value $= (-1)^s \, (1 + F / 2^{23}) \cdot 2^{E - 127}$, "
         r"the hidden bit supplies the 1"),
        (r"zero or subnormal word, $E = 0$:  value $= (-1)^s \, F \cdot 2^{1 - 127 - 23} "
         r"= (-1)^s \, F \cdot 2^{-149}$, no hidden bit"),
        (r"$E = 255$:  $F = 0$ is $\pm\infty$, $F \neq 0$ is NaN"),
    ]
    for i, rule in enumerate(rules):
        ax.text(0, 3.5 - 1.25 * i, rule, ha="left", va="top", fontsize=10, color=fs.INK)

    out = fs.save(fig, "ch01-binary32-layout.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
