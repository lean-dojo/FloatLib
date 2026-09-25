#!/usr/bin/env python3
"""Draw content/assets/ch06-one-rounding.png: one exact sum, one rounding, on the grid at 1.

Chapter 06 states the central refinement theorem, toReal (add x y) = roundAt fmt (toReal x +
toReal y), and illustrates it with x = one32 (the binary32 word for 1) and y = tiny32 (the
word nearest to 1e-8): the exact sum 1 + y is a dyadic that binary32 cannot hold, and the
nearest grid point is 1 itself. The figure draws the binary32 grid around 1 in units of the
spacing there, places the exact real sum on it, and shows the single rounding back to 1.

Sources (site/content/chapters/06-the-numerical-models.md unless stated):

* one32 = 0x3f800000 decodes to significand 8388608 and exponent -23, that is 1; tiny32 =
  0x322bcc77 decodes to 11258999 * 2^-50; the chapter prints both records;
* the spacing of representable values just above 1 is 2^-23 (the chapter's statement; it is
  2^(0 - 23) from fracWidth 23 of FloatFormat.binary32 in
  FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean), and the chapter gives
  y as about 0.084 of that spacing; the script computes the exact ratio 11258999 * 2^-27;
* Model.add one32 tiny32 = 0x3f800000 with inexact := true is the chapter's printed result;
* the neighbouring words 0x3f7fffff (1 - 2^-24), 0x3f800001 (1 + 2^-23) and 0x3f800002
  (1 + 2 * 2^-23) are derived here with the decoding rule of toDyadic?
   (FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean) and checked by assertion.

The drawing keeps the worked number line. The full refinement statement, its finite/IEEE
hypotheses and its Lean identifiers remain in the chapter rather than inside the image.

Run from anywhere: python3 ch06_one_rounding.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402

# FloatFormat.binary32 (Format/Catalog.lean).
EXP_WIDTH = 8
FRAC_WIDTH = 23
BIAS = 127
TOTAL = 1 + EXP_WIDTH + FRAC_WIDTH
ALL_ONES = 2 ** EXP_WIDTH - 1
MIN_SUBNORMAL_EXP = 1 - BIAS - FRAC_WIDTH

ONE32 = 0x3F800000
TINY32 = 0x322BCC77
def to_value(word: int) -> Fraction:
    """The rule of Model.toDyadic? (Dyadic/Decode.lean), then Dyadic.toReal, for a finite word."""
    sign = word >> (TOTAL - 1)
    exp_field = (word >> FRAC_WIDTH) & ALL_ONES
    frac_field = word & (2 ** FRAC_WIDTH - 1)
    assert exp_field != ALL_ONES
    if exp_field == 0:
        value = frac_field * Fraction(2) ** MIN_SUBNORMAL_EXP
    else:
        value = (2 ** FRAC_WIDTH + frac_field) * Fraction(2) ** (exp_field - BIAS - FRAC_WIDTH)
    return -value if sign else value


def example_offset() -> Fraction:
    """Check the exact chapter example before converting a coordinate to float."""
    x = to_value(ONE32)
    y = to_value(TINY32)
    assert x == 1 and y == Fraction(11258999, 2 ** 50)
    ulp = Fraction(2) ** (0 - FRAC_WIDTH)                  # spacing just above 1
    assert to_value(ONE32 + 1) - x == ulp
    assert to_value(ONE32 - 1) == 1 - ulp / 2               # spacing below 1 is half as large
    assert to_value(ONE32 + 2) == 1 + 2 * ulp
    offset = y / ulp                                        # the exact sum, in units of the gap
    assert offset == 11258999 * Fraction(2) ** -27
    assert round(float(offset), 3) == 0.084
    result = ONE32                                          # Model.add one32 tiny32, chapter
    assert to_value(result) == 1

    return offset


def draw(mobile: bool, offset: Fraction):
    fig, ax = plt.subplots(figsize=(3.8, 4.65) if mobile else (9, 3.5))
    fig.subplots_adjust(left=0.04, right=0.96, top=0.70, bottom=0.20)
    ax.set_xlim(-0.7, 1.3)
    ax.set_ylim(-0.95, 1.1)
    ax.axis("off")
    ax.grid(False)
    fig.text(0.035, 0.95, "One exact sum, one rounding", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.82 if mobile else 0.80,
             "$1+y$, with binary32 $y$ nearest to $10^{-8}$" if not mobile else
             "$1+y$, with binary32 $y$\nnearest to $10^{-8}$",
             fontsize=12, color=fs.MUTED, linespacing=1.4)
    ax.plot([-0.62, 1.2], [0, 0], color=fs.INK, linewidth=1.0, zorder=1)
    for u, label in [(-0.5, r"$1 - 2^{-24}$"), (0.0, "1"), (1.0, r"$1 + 2^{-23}$")]:
        ax.plot([u, u], [-0.12, 0.12], color=fs.INK, linewidth=0.9, zorder=2)
        ax.plot([u], [0], marker="o", markersize=6.5, color=fs.BLUE, zorder=3)
        ax.text(u, -0.25, label, ha="center", va="top", fontsize=12)
    ax.plot([0.5, 0.5], [-0.10, 0.40], color=fs.MUTED, linewidth=0.9, linestyle=":")
    ax.text(0.5, 0.45, "midpoint", ha="center", fontsize=11.5, color=fs.MUTED)
    ax.annotate("", (1.0, -0.64), (0.0, -0.64),
                arrowprops=dict(arrowstyle="|-|", color=fs.MUTED, lw=0.8,
                                shrinkA=0, shrinkB=0, mutation_scale=3))
    ax.text(0.5, -0.77, r"one gap: $2^{-23}$", ha="center", va="top", fontsize=11.5)
    u_sum = float(offset)
    ax.plot([u_sum], [0], marker="D", markersize=7.5, markerfacecolor="white",
             markeredgecolor=fs.VERMILION, markeredgewidth=1.6, zorder=4)
    ax.annotate("exact sum", (u_sum, 0.13), (0.06, 0.90),
                fontsize=12, color=fs.VERMILION, ha="center",
                arrowprops=dict(arrowstyle="-", color=fs.VERMILION, lw=1))
    ax.annotate("", (0.0, 0.12), (u_sum, 0.12),
                arrowprops=dict(arrowstyle="->", connectionstyle="arc3,rad=-2",
                                color=fs.VERMILION, lw=1.4))
    fig.text(0.035, 0.10, "The sum is only 0.084 of a gap above 1.", fontsize=11.5)
    fig.text(0.035, 0.025, "Nearest result: 1     inexact: true", fontsize=12, color=fs.BLUE)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    offset = example_offset()
    fs.setup()
    out = args.out or fs.ASSETS / "ch06-one-rounding.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile, offset), target.name, target)}")


if __name__ == "__main__":
    main()
