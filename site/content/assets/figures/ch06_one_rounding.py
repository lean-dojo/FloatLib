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
  (FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean) and checked by assertion;
* the function and theorem names (toReal, roundAt, add, toReal_add_eq_roundAt, isIEEE,
  isFinite) are copied from the chapter's node links.

Run from anywhere: python3 ch06_one_rounding.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

# FloatFormat.binary32 (Format/Catalog.lean).
EXP_WIDTH = 8
FRAC_WIDTH = 23
BIAS = 127
TOTAL = 1 + EXP_WIDTH + FRAC_WIDTH
ALL_ONES = 2 ** EXP_WIDTH - 1
MIN_SUBNORMAL_EXP = 1 - BIAS - FRAC_WIDTH

ONE32 = 0x3F800000
TINY32 = 0x322BCC77
MONO = "DejaVu Sans Mono"


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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
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

    fig, ax = fs.figure(3.8)
    fig.subplots_adjust(left=0.01, right=0.99, top=0.99, bottom=0.01)
    left, right = -0.68, 1.3
    ax.set_xlim(left, right)
    ax.set_ylim(-1.75, 3.0)
    ax.axis("off")
    ax.grid(False)

    # The grid: filled circles are binary32 words, drawn in units of the spacing 2^-23 above 1.
    ax.plot([-0.62, 1.2], [0, 0], color=fs.INK, linewidth=1.0, zorder=1)
    grid = [(-0.5, ONE32 - 1, r"$1 - 2^{-24}$"), (0.0, ONE32, "1"),
            (1.0, ONE32 + 1, r"$1 + 2^{-23}$")]
    for u, word, label in grid:
        assert to_value(word) == 1 + u * ulp
        ax.plot([u, u], [-0.12, 0.12], color=fs.INK, linewidth=0.9, zorder=2)
        ax.plot([u], [0], marker="o", markersize=6.5, color=fs.BLUE, zorder=3)
        ax.text(u, -0.28, label, ha="center", va="top", fontsize=9.5, color=fs.INK)
        ax.text(u, -0.62, f"0x{word:08x}", ha="center", va="top", fontsize=9, family=MONO,
                color=fs.MUTED)
    # The half-way points, where nearest rounding changes its answer.
    for u in (-0.25, 0.5):
        ax.plot([u, u], [-0.1, 0.1], color=fs.MUTED, linewidth=0.8, linestyle=":", zorder=2)
        ax.text(u, -0.28, "midpoint", ha="center", va="top", fontsize=9, color=fs.MUTED)
    ax.annotate("", xy=(1.0, -1.08), xytext=(0.0, -1.08),
                arrowprops=dict(arrowstyle="|-|", color=fs.MUTED, lw=0.8, shrinkA=0, shrinkB=0,
                                mutation_scale=3))
    ax.text(0.5, -1.18, r"spacing $2^{-23}$, the unit in the last place at 1", ha="center",
            va="top", fontsize=9, color=fs.MUTED)

    # The exact real sum and its single rounding, drawn as a bracket from the sum back to 1.
    u_sum = float(offset)
    ax.plot([u_sum], [0], marker="D", markersize=7.5, markerfacecolor="white",
            markeredgecolor=fs.VERMILION, markeredgewidth=1.6, zorder=4)
    top_y = 0.78
    ax.plot([u_sum, u_sum, 0.0], [0.16, top_y, top_y], color=fs.VERMILION, linewidth=1.6,
            zorder=3)
    fs.arrow(ax, (0.0, top_y), (0.0, 0.16), color=fs.VERMILION, linewidth=1.6, shrink=0.0)
    ax.text(-0.04, top_y + 0.03, "roundAt binary32", ha="right", va="bottom", fontsize=9.5,
            family=MONO, color=fs.VERMILION)
    ax.text(-0.04, top_y - 0.05, "one rounding, to the nearest word", ha="right", va="top",
            fontsize=9, color=fs.MUTED)
    ax.text(u_sum + 0.04, 0.5, r"exact sum toReal x + toReal y $= 1 + 11258999 \cdot 2^{-50}$",
            ha="left", va="bottom", fontsize=9.5, color=fs.VERMILION)
    ax.text(u_sum + 0.04, 0.43, f"about {float(offset):.3f} of the gap, so the nearest word is 1",
            ha="left", va="top", fontsize=9, color=fs.MUTED)

    # The statement being pictured.
    ax.text(left, 2.95, "The refinement theorem toReal_add_eq_roundAt on the chapter's words "
            "x = one32 and y = tiny32", ha="left", va="top", fontsize=10.5, color=fs.INK)
    ax.text(left, 2.45, "toReal (add x y)  =  roundAt binary32 (toReal x + toReal y)",
            ha="left", va="top", fontsize=10, family=MONO, color=fs.INK)
    ax.text(left, 2.0, "hypotheses: isIEEE binary32, isFinite x, isFinite y, "
            "isFinite (add x y); here add x y = 0x3f800000, so both sides are 1,\n"
            "and the status flags of addWithStatus record inexact := true, the only trace the "
            "discarded $11258999 \\cdot 2^{-50}$ leaves",
            ha="left", va="top", fontsize=9, color=fs.MUTED, linespacing=1.3)

    out = fs.save(fig, "ch06-one-rounding.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
