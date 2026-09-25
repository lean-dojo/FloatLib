#!/usr/bin/env python3
"""Draw binary32 fields and two worked encodings, with separately stacked mobile fields.

FloatFormat.binary32 in Format/Catalog.lean has 8 exponent and 23 fraction bits, bias 127
and precision 24. Both encoded examples are derived exactly from the values in chapter 02:
13421773 * 2^-27 (the rounded literal 0.1) and -5/2 (exactly -2.5). The chapter's words for
1, 2 and -2.5 provide independent assertions. Every drawn bit is read from the derived word.

The normal/subnormal/reserved-exponent rules and the long decimal expansion remain in
chapter 02. This diagram focuses on reading stored fields, including the implicit leading
one of normal values. On mobile, fields are shown separately instead of shrinking 32 cells.

Run from anywhere: python3 ch01_binary32_layout.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

import figstyle as fs
from matplotlib.colors import to_rgba
from matplotlib.patches import Rectangle

OUT_NAME = "ch01-binary32-layout.png"
EXP_WIDTH, FRAC_WIDTH = 8, 23
BIAS = 2 ** (EXP_WIDTH - 1) - 1
TOTAL = 1 + EXP_WIDTH + FRAC_WIDTH
PRECISION = FRAC_WIDTH + 1
MONO = "DejaVu Sans Mono"
FIELDS = [("s", 1, fs.PURPLE), ("exponent E (8 bits)", EXP_WIDTH, fs.ORANGE),
          ("fraction F (23 bits)", FRAC_WIDTH, fs.SKY)]
assert (TOTAL, PRECISION, BIAS) == (32, 24, 127)


def encode_normal(value: Fraction) -> int:
    """Encode an exactly representable, nonzero normal value using the chapter's rule."""
    if value == 0:
        raise ValueError("zero is not normal")
    negative, magnitude, exponent = value < 0, abs(value), 0
    while magnitude >= 2 ** PRECISION:
        magnitude /= 2
        exponent += 1
    while magnitude < 2 ** (PRECISION - 1):
        magnitude *= 2
        exponent -= 1
    if magnitude.denominator != 1:
        raise ValueError(f"{value} is not exactly representable")
    significand = magnitude.numerator
    biased = exponent + FRAC_WIDTH + BIAS
    if not 0 < biased < 2 ** EXP_WIDTH - 1:
        raise ValueError(f"{value} is not in the normal range")
    return (int(negative) << (TOTAL - 1)) | (biased << FRAC_WIDTH) | (significand - 2 ** FRAC_WIDTH)


def fields_of(word: int) -> tuple[int, int, int]:
    return word >> 31, (word >> FRAC_WIDTH) & (2 ** EXP_WIDTH - 1), word & (2 ** FRAC_WIDTH - 1)


TENTH = Fraction(13421773, 2 ** 27)
EXAMPLES = [
    ("Rounded 0.1", encode_normal(TENTH), r"$13421773\times 2^{-27}$"),
    ("Exact −2.5", encode_normal(Fraction(-5, 2)), r"$-5/2$"),
]
assert [word for _, word, _ in EXAMPLES] == [0x3DCCCCCD, 0xC0200000]
assert fields_of(EXAMPLES[0][1]) == (0, 123, 5033165)
assert fields_of(EXAMPLES[1][1]) == (1, 128, 2097152)
assert encode_normal(Fraction(1)) == 1065353216
assert encode_normal(Fraction(2)) == 1073741824
assert EXAMPLES[1][1] == 3223322624


def layout(ax, width: float, y: float, mobile: bool):
    left, unit = 0.23 if mobile else 0.30, (width - (0.46 if mobile else 0.60)) / TOTAL
    labels = ["s", "E · 8", "F · 23"] if mobile else [field[0] for field in FIELDS]
    for (name, bits, colour), label in zip(FIELDS, labels):
        ax.add_patch(Rectangle((left, y), unit * bits, 0.42,
                               facecolor=to_rgba(colour, 0.38), edgecolor=fs.INK, lw=0.8))
        ax.text(left + unit * bits / 2, y + 0.21, label, ha="center", va="center", fontsize=11.5)
        left += unit * bits


def desktop_example(ax, title, word, value, y):
    ax.text(0.30, y, title, fontsize=13, weight="bold", va="center")
    ax.text(2.35, y, f"= {value}", fontsize=13, va="center")
    ax.text(8.70, y, f"0x{word:08x}", fontsize=12, family=MONO, ha="right", va="center")
    left, unit, bit = 0.30, 8.40 / TOTAL, TOTAL - 1
    for _, bits, colour in FIELDS:
        for _ in range(bits):
            ax.add_patch(Rectangle((left, y - 0.65), unit, 0.37,
                                   facecolor=to_rgba(colour, 0.22), edgecolor=fs.LINE, lw=0.6))
            ax.text(left + unit / 2, y - 0.465, str((word >> bit) & 1),
                    ha="center", va="center", fontsize=11.5, family=MONO)
            left += unit
            bit -= 1
    sign, exponent, fraction = fields_of(word)
    ax.text(0.30, y - 0.88, f"s = {sign}", fontsize=11.5, va="center")
    ax.text(0.30 + unit * 5, y - 0.88, f"E = {exponent}", fontsize=11.5, ha="center", va="center")
    ax.text(0.30 + unit * 20.5, y - 0.88, f"F = {fraction:,}", fontsize=11.5, ha="center", va="center")


def mobile_example(ax, title, word, value, y):
    sign, exponent, fraction = fields_of(word)
    ax.text(0.23, y, title, fontsize=13, weight="bold", va="center")
    ax.text(3.57, y, f"0x{word:08x}", fontsize=11.5, family=MONO, ha="right", va="center")
    ax.text(0.23, y - 0.37, f"= {value}", fontsize=14, va="center")
    ax.text(0.23, y - 0.80, f"s = {sign}", fontsize=11.5, family=MONO, va="center")
    ax.text(1.11, y - 0.80, f"E = {exponent:08b}", fontsize=11.5, family=MONO, va="center")
    ax.text(0.23, y - 1.19, "F · 23 fraction bits", fontsize=11.5, va="center")
    ax.add_patch(Rectangle((0.23, y - 1.77), 3.34, 0.39,
                           facecolor=to_rgba(fs.SKY, 0.22), edgecolor=fs.LINE, lw=0.6))
    ax.text(1.90, y - 1.575, f"{fraction:023b}", fontsize=11.5, family=MONO,
            ha="center", va="center")


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 7.3) if mobile else (9.0, 5.1)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18, "Reading a binary32 word", fontsize=14 if mobile else 16,
            weight="bold", va="top")
    if mobile:
        layout(ax, width, 6.23, True)
        ax.text(1.90, 5.98, "Sign · exponent · fraction", fontsize=11.5,
                ha="center", va="center", color=fs.MUTED)
        for example, y in zip(EXAMPLES, (5.47, 3.07)):
            mobile_example(ax, *example, y)
        ax.plot([0.23, 3.57], [3.40, 3.40], color=fs.LINE, lw=0.7)
        ax.text(1.90, 0.62, "Normal values: the leading 1\nis implicit.", fontsize=11.5,
                ha="center", va="center", linespacing=1.4)
    else:
        layout(ax, width, 3.99, False)
        for example, y in zip(EXAMPLES, (3.52, 2.03)):
            desktop_example(ax, *example, y)
        ax.text(4.50, 0.49, "Normal values have a leading 1 that is not stored.", fontsize=12,
                ha="center", va="center")
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    target = args.out or fs.ASSETS / OUT_NAME
    for mobile in (False, True):
        path = target.with_name(f"{target.stem}-mobile{target.suffix}") if mobile else target
        print(f"wrote {fs.save(build_figure(mobile), OUT_NAME, path)}")


if __name__ == "__main__":
    main()
