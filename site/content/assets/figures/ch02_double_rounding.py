#!/usr/bin/env python3
"""Draw content/assets/ch02-double-rounding.png: rounding twice lands on the wrong neighbour.

The correctness chapter ("Rounding twice") takes x = 1 + 2^-24 + 2^-53, rounds it directly to binary32 (up,
to 1 + 2^-23) and then through binary64 (a tie, to even, then a second tie, to even, landing on
1). Those grids are 2^29 apart in spacing and cannot share a picture, so this figure draws the
same configuration on the smallest grids that show it: a three-digit target standing in for
binary32's 24 digits and a five-digit intermediate standing in for binary64's 53. The value is
x = 1 + 2^-3 + 2^-5, the chapter's x with (24, 53) replaced by (3, 5), and every grid point,
midpoint and rounding on the picture is computed here with exact rationals.

Sources:
* the grids are `flxExp prec` from FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean
  (fexp e = e - prec) in radix 2, and the rounding is `round` and `nearestEven` from
  FloatLib/Floats/Formats/Flocq/Theory/Rounding/Core.lean, with `magnitude` and `cexp` from
  FloatLib/Floats/Formats/Flocq/Theory/Core.lean, re-implemented below on Python fractions;
* the construction of x is the chapter's; binary32 and binary64 have 24 and 53 significand
  digits (fracWidth 23 and 52 in
  FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean, plus the hidden bit).

Before drawing, the script recomputes the chapter's own instance at 24 and 53 digits and checks
it against the three significands the chapter prints (8388609 * 2^-23, 4503599895805952 * 2^-52,
8388608 * 2^-23), so the small picture and the chapter's Lean output come from one function.
The intermediate grid has five digits and not four because the chapter's mechanism needs x to be
a tie on the intermediate grid (its last term is half that grid's spacing), and the script asserts
that it is.

Run from anywhere: python3 ch02_double_rounding.py [--out PNG]
Also writes a -mobile.png sibling, separating the two rounding steps and the direct route.
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

TWO = Fraction(2)


# ---- exact rounding, following the Lean definitions ------------------------------------

def magnitude(x: Fraction) -> int:
    """Core.lean `magnitude` in radix 2: 0 at zero, else floor(log2 |x|) + 1."""
    if x == 0:
        return 0
    ax = abs(x)
    k = ax.numerator.bit_length() - ax.denominator.bit_length()
    while TWO ** k > ax:
        k -= 1
    while TWO ** (k + 1) <= ax:
        k += 1
    assert TWO ** k <= ax < TWO ** (k + 1)
    return k + 1


def flx_exp(prec: int):
    """Formats.lean `flxExp prec`: e -> e - prec."""
    return lambda e: e - prec


def nearest_even(t: Fraction) -> int:
    """Rounding/Core.lean `nearestEven` on the integers."""
    f = math.floor(t)
    r = t - f
    if r < Fraction(1, 2):
        return f
    if r > Fraction(1, 2):
        return f + 1
    return f if f % 2 == 0 else f + 1


def round_grid(fexp, rnd, x: Fraction) -> Fraction:
    """Rounding/Core.lean `round`: rnd(x * 2^-cexp(x)) * 2^cexp(x) with cexp = fexp(magnitude)."""
    e = fexp(magnitude(x))
    return Fraction(rnd(x / TWO ** e)) * TWO ** e


def routes(target: int, wide: int, x: Fraction) -> tuple[Fraction, Fraction, Fraction]:
    """(direct rounding to target digits, rounding to wide digits, that rounded again to target)."""
    direct = round_grid(flx_exp(target), nearest_even, x)
    first = round_grid(flx_exp(wide), nearest_even, x)
    second = round_grid(flx_exp(target), nearest_even, first)
    return direct, first, second


def binary_mantissa(v: Fraction, prec: int) -> str:
    """The significand of a grid point with `prec` digits, written 1.xxx in base two."""
    e = magnitude(v) - prec
    m = v / TWO ** e
    assert m.denominator == 1 and TWO ** (prec - 1) <= m < TWO ** prec
    bits = bin(m.numerator)[2:]
    return bits[0] + "." + bits[1:]


# ---- the two instances -----------------------------------------------------------------

def chapter_instance() -> None:
    """The chapter's x at 24 and 53 digits, checked against its printed dyadics."""
    x = 1 + TWO ** -24 + TWO ** -53
    direct, first, second = routes(24, 53, x)
    assert direct == Fraction(8388609) * TWO ** -23, direct
    assert first == Fraction(4503599895805952) * TWO ** -52, first
    assert second == Fraction(8388608) * TWO ** -23, second


def small_instance(target: int = 3, wide: int = 5):
    x = 1 + TWO ** -target + TWO ** -(target + 2)
    assert wide == target + 2
    direct, first, second = routes(target, wide, x)
    assert direct != second, "the small grids must show the hazard"
    return x, direct, first, second


# ---- drawing ----------------------------------------------------------------------------

LO, HI = Fraction(1), Fraction(3, 2)             # the stretch of the line that is drawn


def tick(ax, x: float, y: float, half: float, **kwargs) -> None:
    ax.plot([x, x], [y - half, y + half], **kwargs)


def curved_arrow(ax, start, end, *, color, rad, linestyle="-", linewidth=1.4) -> None:
    ax.annotate("", xy=end, xytext=start,
                arrowprops=dict(arrowstyle="-|>", color=color, lw=linewidth,
                                linestyle=linestyle, shrinkA=3, shrinkB=3,
                                connectionstyle=f"arc3,rad={rad}"))


def build_mobile(target, wide, x, direct, first, second):
    """Show the same exact example on three short local grids."""
    assert (target, wide) == (3, 5)
    assert (x, direct, first, second) == (Fraction(37, 32), Fraction(5, 4),
                                        Fraction(9, 8), Fraction(1))
    fine_step = TWO ** (1 - wide)
    coarse_step = TWO ** (1 - target)
    assert x - first == first + fine_step - x == Fraction(1, 32)
    assert first - second == direct - first == coarse_step / 2
    assert (first / fine_step).numerator % 2 == 0
    assert (second / coarse_step).numerator % 2 == 0
    assert direct - x < x - second

    height = 9.0
    fig = plt.figure(figsize=(3.8, height))
    ax = fs.diagram_axes(fig, (0, 3.8), (0, height))
    ax.text(0.18, 8.78, "Rounding twice changes\nthe result", fontsize=15,
            weight="bold", va="top", linespacing=1.2)
    ax.text(0.18, 8.08, "Nearest, ties to even", fontsize=12, va="center")
    ax.text(0.18, 7.73, f"x = 1 + 1/8 + 1/32 = {float(x):g}", fontsize=12, va="center")
    ax.text(0.18, 7.40, "Significands below are in base 2.", fontsize=12,
            va="center", color=fs.MUTED)

    def local_grid(y, lo, hi, value, result, prec, *, direct_route=False):
        left, right = 0.48, 3.28

        def place(v):
            return left + float((v - lo) / (hi - lo)) * (right - left)

        colour = fs.GREEN if direct_route else fs.VERMILION
        ax.plot([left, right], [y, y], color=fs.INK, linewidth=1)
        for endpoint in (lo, hi):
            px = place(endpoint)
            tick(ax, px, y, 0.10, color=fs.INK, linewidth=1.2)
            ax.text(px, y - 0.18, f"{float(endpoint):g}", fontsize=12,
                    ha="center", va="top")
            ax.text(px, y - 0.45, binary_mantissa(endpoint, prec), fontsize=12,
                    ha="center", va="top", family="DejaVu Sans Mono")
        midpoint = (lo + hi) / 2
        ax.plot([place(midpoint)], [y], marker="o", markersize=5.5,
                markerfacecolor="white", markeredgecolor=fs.INK)
        if direct_route:
            ax.text(place(midpoint), y - 0.18, f"{float(midpoint):g}", fontsize=12,
                    ha="center", va="top")
        ax.plot([place(value)], [y + 0.15], marker="v", markersize=8, color=colour)
        ax.text(place(value), y + 0.36, "x" if value == x else f"{float(value):g}",
                fontsize=12, ha="center", va="bottom")
        curved_arrow(ax, (place(value), y + 0.02), (place(result), y + 0.02),
                     color=colour, rad=-0.35 if direct_route else 0.35,
                     linestyle="-" if direct_route else "--")
        ax.plot([place(result)], [y], marker="D" if direct_route else "o",
                markersize=7, color=colour)

    ax.text(0.18, 6.93, "First: 5 binary digits", fontsize=13, weight="bold", va="center")
    local_grid(6.18, first, first + fine_step, x, first, wide)
    ax.text(0.18, 5.37, "Halfway: even 1.0010 wins.", fontsize=12, va="center")

    # The dotted connector carries the intermediate value into the second rounding.
    ax.plot([0.48, 0.48], [5.11, 4.90], color=fs.VERMILION, linestyle=":", linewidth=1.4)
    ax.text(0.67, 5.00, f"carry {float(first):g}", fontsize=12, va="center")
    ax.text(0.18, 4.59, "Second: 3 binary digits", fontsize=13, weight="bold", va="center")
    local_grid(3.84, second, direct, first, second, target)
    ax.text(0.18, 3.03, "Halfway again: even 1.00 wins.", fontsize=12, va="center")

    ax.plot([0.18, 3.62], [2.70, 2.70], color=fs.LINE, linewidth=0.8)
    ax.text(0.18, 2.42, "Direct: 3 binary digits", fontsize=13, weight="bold", va="center")
    local_grid(1.67, second, direct, x, direct, target, direct_route=True)
    ax.text(0.18, 0.86, "x is above the midpoint: choose 1.25.", fontsize=12, va="center")
    ax.text(0.18, 0.33, "Twice: 1     Once: 1.25", fontsize=14, weight="bold", va="center")
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    chapter_instance()
    target, wide = 3, 5
    x, direct, first, second = small_instance(target, wide)
    xf = float(x)

    fs.setup()
    fig = plt.figure(figsize=(fs.WIDTH, 4.6))
    ax = fig.add_axes([0.01, 0.01, 0.98, 0.98])
    ax.set_xlim(0.945, 1.555)
    ax.set_ylim(0.0, 10.0)
    ax.axis("off")
    ax.grid(False)

    y_wide, y_target = 7.4, 2.6
    line_style = dict(color=fs.INK, linewidth=1.0, solid_capstyle="butt")
    for y in (y_wide, y_target):
        ax.plot([float(LO) - 0.012, float(HI) + 0.012], [y, y], **line_style)

    # Fine grid: five digits, spacing 2^-4 on [1, 2).
    step_wide = TWO ** (flx_exp(wide)(magnitude(LO)))
    step_target = TWO ** (flx_exp(target)(magnitude(LO)))
    assert step_wide == TWO ** -4 and step_target == TWO ** -2
    g = LO
    while g <= HI:
        tick(ax, float(g), y_wide, 0.22, color=fs.INK, linewidth=1.0)
        g += step_wide
    # Coarse grid: three digits, spacing 2^-2, drawn on both lines so the reader can line them up.
    g = LO
    while g <= HI:
        tick(ax, float(g), y_target, 0.42, color=fs.INK, linewidth=1.6)
        tick(ax, float(g), y_wide, 0.42, color=fs.INK, linewidth=1.6)
        ax.text(float(g), y_target - 0.6, f"{float(g):g} = ${binary_mantissa(g, target)}_2$",
                ha="center", va="top", fontsize=9.5)
        g += step_target
    # Midpoints of the coarse grid.
    m = LO + step_target / 2
    while m < HI:
        ax.plot([float(m)], [y_target], marker="o", markersize=5, markerfacecolor="white",
                markeredgecolor=fs.INK, markeredgewidth=1.0, linestyle="None", zorder=4)
        m += step_target

    # Labels for the two fine neighbours of x, with their five-digit significands.
    lower = first
    upper = first + step_wide
    assert lower < x < upper and x - lower == upper - x, "x is a tie on the five-digit grid"
    for v, dy in ((lower, 0), (upper, 0)):
        ax.text(float(v), y_wide - 0.5 + dy, f"{float(v):g}\n${binary_mantissa(v, wide)}_2$",
                ha="center", va="top", fontsize=9, color=fs.INK)

    # Row titles.
    ax.text(float(LO) - 0.012, y_wide + 1.55, "five binary digits (the intermediate; binary64's part)",
            ha="left", va="bottom", fontsize=10, color=fs.INK)
    ax.text(float(LO) - 0.012, y_target + 1.55, "three binary digits (the target; binary32's part)",
            ha="left", va="bottom", fontsize=10, color=fs.INK, zorder=5,
            bbox=dict(facecolor="white", edgecolor="none", pad=0.2))

    # The exact value x on both lines.
    x_style = dict(markersize=9, color=fs.VERMILION, markerfacecolor=fs.VERMILION,
                   linestyle="None", zorder=6)
    ax.plot([xf], [y_wide + 0.36], marker="v", **x_style)
    ax.plot([xf], [y_target - 0.36], marker="^", **x_style)
    ax.text(xf, y_wide + 0.95, r"$x = 1 + 2^{-3} + 2^{-5}$", ha="center", va="bottom",
            fontsize=10, color=fs.VERMILION)

    # Route one: round twice. First to five digits (a tie, to even), then to three (a tie again).
    twice = fs.VERMILION
    curved_arrow(ax, (xf, y_wide + 0.05), (float(first), y_wide + 0.05), color=twice, rad=0.55,
                 linestyle="--")
    ax.text(xf + 0.075, y_wide + 0.4,
            "first rounding: a tie between the two\nfive-digit neighbours, the even one wins",
            ha="left", va="bottom", fontsize=9, color=twice)
    ax.plot([float(first), float(first)], [y_wide - 1.3, y_target + 0.25], color=twice,
            linestyle=":", linewidth=1.2, zorder=3)
    ax.text(float(first) + 0.006, y_wide - 1.75,
            f"{float(first):g}: exactly a midpoint\nof the three-digit grid",
            ha="left", va="top", fontsize=9, color=twice)
    curved_arrow(ax, (float(first), y_target - 0.05), (float(second), y_target - 0.05),
                 color=twice, rad=-0.55, linestyle="--")
    ax.text((float(first) + float(second)) / 2, y_target - 1.35,
            f"second rounding: a tie again,\nthe even neighbour is {float(second):g}",
            ha="center", va="top", fontsize=9, color=twice)

    # Route two: round once, directly to three digits, drawn above the line.
    once = fs.GREEN
    curved_arrow(ax, (xf, y_target + 0.05), (float(direct), y_target + 0.05), color=once,
                 rad=-0.5)
    ax.text((xf + float(direct)) / 2 + 0.012, y_target + 0.85,
            f"one rounding: just above\nthe midpoint, so up to {float(direct):g}",
            ha="left", va="bottom", fontsize=9, color=once)

    # Results.
    ax.plot([float(second)], [y_target], marker="o", markersize=9, color=twice,
            markerfacecolor=twice, linestyle="None", zorder=6)
    ax.plot([float(direct)], [y_target], marker="D", markersize=8, color=once,
            markerfacecolor=once, linestyle="None", zorder=6)

    handles = [
        Line2D([], [], color=twice, linestyle="--", marker="o", markersize=8, linewidth=1.4,
               label=f"rounded twice, through five digits: {float(second):g}"),
        Line2D([], [], color=once, linestyle="-", marker="D", markersize=7, linewidth=1.4,
               label=f"rounded once, straight to three digits: {float(direct):g}"),
        Line2D([], [], color=fs.INK, marker="o", markersize=5, markerfacecolor="white",
               linestyle="None", label="midpoint of the three-digit grid"),
    ]
    ax.legend(handles=handles, loc="lower right", bbox_to_anchor=(1.0, 0.0), ncol=1,
              fontsize=9)

    out = fs.save(fig, "ch02-double-rounding.png", args.out)
    print(f"wrote {out}")
    mobile = out.with_name(f"{out.stem}-mobile{out.suffix}")
    print(f"wrote {fs.save(build_mobile(target, wide, x, direct, first, second), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
