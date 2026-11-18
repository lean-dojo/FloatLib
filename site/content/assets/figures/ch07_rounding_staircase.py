#!/usr/bin/env python3
"""Draw content/assets/ch07-rounding-staircase.png: round to nearest even as a step function.

The chapter on rounding defines rounding as scale, round the integer,
scale back, and remarks that the one difficulty is that two inputs may have different canonical
exponents. This figure draws the function on a grid with three binary digits across the powers
of two at 1 and 2, where the canonical exponent changes and the steps double in width. The
diagonal y = x carries the grid points, which rounding fixes; each horizontal step is the set of
reals sent to one grid point, and at a midpoint the filled end shows which neighbour the tie goes
to (the one with an even significand).

Sources: the grid is `flxExp 3` in radix 2 from
FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean, the function is `round` with
`nearestEven` from FloatLib/Floats/Formats/Flocq/Theory/Rounding/Core.lean on `magnitude` and
`cexp` from FloatLib/Floats/Formats/Flocq/Theory/Core.lean, all re-implemented below on exact
rationals. Three binary digits is the precision the chapter itself uses for a small example.

The phone companion keeps every step and endpoint, with the marker key below the plot. The
worked tie (1.125 goes to 1) is checked here and described in the caption. --out writes both
images beside the supplied path.

Run from anywhere: python3 ch07_rounding_staircase.py [--out PNG]
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
PREC = 3


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
    return k + 1


def fexp(e: int) -> int:
    """Formats.lean `flxExp PREC`."""
    return e - PREC


def nearest_even(t: Fraction) -> int:
    """Rounding/Core.lean `nearestEven`."""
    f = math.floor(t)
    r = t - f
    if r < Fraction(1, 2):
        return f
    if r > Fraction(1, 2):
        return f + 1
    return f if f % 2 == 0 else f + 1


def round_ne(x: Fraction) -> Fraction:
    """Rounding/Core.lean `round` at `nearestEven` on the `flxExp PREC` grid."""
    e = fexp(magnitude(x))
    return Fraction(nearest_even(x / TWO ** e)) * TWO ** e


def grid_points(lo: Fraction, hi: Fraction) -> list[Fraction]:
    """Every grid point in [lo, hi], binade by binade: m * 2^(e - PREC) for 2^(PREC-1) <= m < 2^PREC."""
    points = []
    for e in range(magnitude(lo), magnitude(hi) + 1):
        for m in range(2 ** (PREC - 1), 2 ** PREC):
            v = Fraction(m) * TWO ** (e - PREC)
            if lo <= v <= hi:
                points.append(v)
    return points


def significand(v: Fraction) -> str:
    e = magnitude(v) - PREC
    m = v / TWO ** e
    assert m.denominator == 1
    bits = bin(m.numerator)[2:]
    return bits[0] + "." + bits[1:]


def check_rounding(points: list[Fraction], lo: Fraction, hi: Fraction) -> None:
    """Check the scale-round-scale rule against nearest points using exact distances."""
    assert [fexp(magnitude(v)) for v in (lo, Fraction(1), Fraction(2))] == [-3, -2, -1]
    assert all(round_ne(v) == v for v in points)
    # This bounded mesh includes each midpoint between displayed grid points
    # and samples each open step in the displayed input interval.
    for numerator in range(int(lo * 256), int(hi * 256) + 1):
        x = Fraction(numerator, 256)
        distance = min(abs(x - v) for v in points)
        candidates = [v for v in points if abs(x - v) == distance]
        if len(candidates) == 2:
            candidates = [v for v in candidates
                          if int(v / TWO ** fexp(magnitude(v))) % 2 == 0]
        assert len(candidates) == 1
        assert round_ne(x) == candidates[0]
        assert round_ne(-x) == -candidates[0]
    assert round_ne(Fraction(9, 8)) == 1


STEP = fs.ROLE["main"]


def key(filled: dict, opened: dict, width: float, square: float) -> list:
    """Legend handles shared by both arrangements."""
    return [
        Line2D([], [], color=STEP, linewidth=width, label="reals rounded to one grid point"),
        Line2D([], [], label="tie rounded to this point", **filled),
        Line2D([], [], label="tie rounded to the neighbour", **opened),
        Line2D([], [], marker="s", markersize=square, color=fs.INK, linestyle="None",
               label="grid point"),
        Line2D([], [], color=fs.MUTED, linewidth=fs.LW_REF, label="$y = x$"),
    ]


def draw_mobile(points: list[Fraction], lo: Fraction, hi: Fraction):
    fig = plt.figure(figsize=(fs.MOBILE_WIDTH, 5.6))
    ax = fig.add_axes([0.19, 0.40, 0.78, 0.53])
    span = (float(lo) - 0.06, float(hi) + 0.28)
    ax.set(xlim=span, ylim=span, aspect="equal")
    ax.axvspan(1, 2, color=fs.PAPER_2, zorder=0, linewidth=0)
    for power in (1, 2):
        ax.axvline(power, color=fs.MUTED, linestyle=":", linewidth=0.9, zorder=1)
    ax.plot(span, span, color=fs.MUTED, linewidth=0.9, zorder=2)
    filled = dict(marker="o", markersize=4.6, markerfacecolor=STEP,
                  markeredgecolor=STEP, linestyle="None", zorder=5)
    opened = dict(marker="o", markersize=4.6, markerfacecolor="white",
                  markeredgecolor=STEP, markeredgewidth=1.0, linestyle="None", zorder=5)
    fs.value_grid(ax, "both")
    for i, value in enumerate(points):
        if not lo <= value <= hi:
            continue
        left, right = (points[i - 1] + value) / 2, (value + points[i + 1]) / 2
        ax.plot([float(left), float(right)], [float(value)] * 2, color=STEP,
                linewidth=fs.LW_DATA, solid_capstyle="butt", zorder=4)
        for midpoint in (left, right):
            ax.plot(float(midpoint), float(value), **(filled if round_ne(midpoint) == value else opened))
        ax.plot(float(value), float(value), marker="s", markersize=3.4, color=fs.INK,
                linestyle="None", zorder=6)
    ticks = [float(v) for v in points if lo <= v <= hi]
    ax.set_xticks(ticks, labels=[f"{v:g}" for v in ticks], fontsize=fs.SIZE_SMALL)
    ax.set_yticks(ticks, labels=[f"{v:g}" for v in ticks], fontsize=fs.SIZE_SMALL)
    ax.tick_params(axis="x", labelrotation=90)
    ax.set_xlabel("$x$")
    ax.set_ylabel("$x$ rounded to nearest even")
    fs.legend(fig, handles=key(filled, opened, fs.LW_DATA, 3.4), loc="upper left",
              bbox_to_anchor=(0.06, 0.25))
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    lo, hi = Fraction(1, 2), Fraction(5, 2)
    # One extra point on each side so every drawn step has both neighbours.
    points = grid_points(lo / 2, hi * 2)
    inside = [g for g in points if lo <= g <= hi]
    check_rounding(points, lo, hi)

    fs.setup()
    fig = plt.figure(figsize=(fs.WIDTH, 5.6))
    ax = fig.add_axes([0.09, 0.12, 0.58, 0.86])
    fs.value_grid(ax, "both")
    span = (float(lo) - 0.06, float(hi) + 0.28)   # room above the last step for the spacing labels
    ax.set_xlim(*span)
    ax.set_ylim(*span)
    ax.set_aspect("equal")

    # Binades, shaded alternately, with the spacing written at the top of each.
    for i, e in enumerate(range(magnitude(lo), magnitude(hi) + 1)):
        left, right = TWO ** (e - 1), TWO ** e
        if i % 2 == 1:
            ax.axvspan(float(left), float(right), color=fs.PAPER_2, zorder=0, linewidth=0)
        ax.text(float(max(left, lo) + min(right, hi)) / 2, span[1] - 0.05,
                f"spacing $2^{{{fexp(e)}}}$", ha="center", va="top", fontsize=fs.SIZE_TICK, color=fs.MUTED)
    for p in (1, 2):
        ax.axvline(p, color=fs.MUTED, linestyle=":", linewidth=0.9, zorder=1)

    ax.plot(span, span, color=fs.MUTED, linewidth=0.9, zorder=2)

    # The staircase: for each grid point, the interval of reals that rounds to it.
    tie_style_in = dict(marker="o", markersize=5.5, markerfacecolor=STEP,
                        markeredgecolor=STEP, linestyle="None", zorder=5)
    tie_style_out = dict(marker="o", markersize=5.5, markerfacecolor="white",
                         markeredgecolor=STEP, markeredgewidth=1.2, linestyle="None", zorder=5)
    for i, g in enumerate(points):
        if not (lo <= g <= hi):
            continue
        pred, succ = points[i - 1], points[i + 1]
        m_lo, m_hi = (pred + g) / 2, (g + succ) / 2
        assert round_ne(m_lo) in (pred, g) and round_ne(m_hi) in (g, succ)
        # Everything strictly between the midpoints rounds to g; the script checks a sample.
        for t in (m_lo + (m_hi - m_lo) / 3, m_lo + 2 * (m_hi - m_lo) / 3):
            assert round_ne(t) == g
        ax.plot([float(m_lo), float(m_hi)], [float(g), float(g)], color=STEP,
                linewidth=2.2, solid_capstyle="butt", zorder=4)
        ax.plot([float(m_lo)], [float(g)], **(tie_style_in if round_ne(m_lo) == g else tie_style_out))
        ax.plot([float(m_hi)], [float(g)], **(tie_style_in if round_ne(m_hi) == g else tie_style_out))
        ax.plot([float(g)], [float(g)], marker="s", markersize=4, color=fs.INK,
                linestyle="None", zorder=6)

    ticks = [float(g) for g in inside]
    ax.set_xticks(ticks, labels=[f"{t:g}" for t in ticks], fontsize=fs.SIZE_SMALL)
    ax.set_yticks(ticks, labels=[f"{t:g}" for t in ticks], fontsize=fs.SIZE_SMALL)
    ax.tick_params(axis="x", labelrotation=90)
    ax.set_xlabel("$x$")
    ax.set_ylabel("$x$ rounded to nearest even")

    # One tie spelled out: 1.125 goes to 1 because 1.00 is even and 1.01 is odd.
    t = Fraction(9, 8)
    r = round_ne(t)
    assert r == 1
    assert significand(r) == "1.00" and significand(t + Fraction(1, 8)) == "1.01"

    fs.legend(fig, handles=key(tie_style_in, tie_style_out, 2.2, 4), loc="center left",
              bbox_to_anchor=(0.67, 0.55))

    out = fs.save(fig, "ch07-rounding-staircase.png", args.out)
    print(f"wrote {out}")
    mobile = fs.mobile_path(out)
    print(f"wrote {fs.save(draw_mobile(points, lo, hi), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
