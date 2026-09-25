#!/usr/bin/env python3
"""Draw content/assets/ch07-rounding-staircase.png: round to nearest even as a step function.

Chapter 07 ("Rounding as a function on the reals") defines rounding as scale, round the integer,
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

The phone companion keeps every step and endpoint, with spacing labels, the marker key and
the worked tie outside the plot. --out writes both images beside the supplied path.

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


def draw_mobile(points: list[Fraction], lo: Fraction, hi: Fraction):
    fig = plt.figure(figsize=(3.8, 8.1))
    fig.text(0.04, 0.98, "Rounding to nearest even", fontsize=14, weight="bold", va="top")
    fig.text(0.04, 0.925, "Three binary digits; grid points 0.5 to 2.5", fontsize=11.5, va="top")
    for x, label, exponent in zip(
            (0.20, 0.52, 0.84),
            (r"$0.5 \leq x < 1$", r"$1 \leq x < 2$", r"$2 \leq x < 4$"),
            (-3, -2, -1)):
        fig.text(x, 0.867, label, ha="center", fontsize=11.5)
        fig.text(x, 0.832, f"gap $2^{{{exponent}}}$", ha="center", fontsize=11.5, color=fs.MUTED)

    ax = fig.add_axes([0.19, 0.40, 0.78, 0.366])
    span = (float(lo) - 0.06, float(hi) + 0.28)
    ax.set(xlim=span, ylim=span, aspect="equal")
    ax.axvspan(1, 2, color=fs.PAPER_2, zorder=0, linewidth=0)
    for power in (1, 2):
        ax.axvline(power, color=fs.MUTED, linestyle=":", linewidth=0.9, zorder=1)
    ax.plot(span, span, color=fs.MUTED, linewidth=0.9, zorder=2)
    filled = dict(marker="o", markersize=4.6, markerfacecolor=fs.BLUE,
                  markeredgecolor=fs.BLUE, linestyle="None", zorder=5)
    opened = dict(marker="o", markersize=4.6, markerfacecolor="white",
                  markeredgecolor=fs.BLUE, markeredgewidth=1.0, linestyle="None", zorder=5)
    for i, value in enumerate(points):
        if not lo <= value <= hi:
            continue
        left, right = (points[i - 1] + value) / 2, (value + points[i + 1]) / 2
        ax.plot([float(left), float(right)], [float(value)] * 2, color=fs.BLUE,
                linewidth=1.8, solid_capstyle="butt", zorder=4)
        for midpoint in (left, right):
            ax.plot(float(midpoint), float(value), **(filled if round_ne(midpoint) == value else opened))
        ax.plot(float(value), float(value), marker="s", markersize=3.4, color=fs.INK,
                linestyle="None", zorder=6)
    ticks = [float(v) for v in points if lo <= v <= hi]
    ax.set_xticks(ticks, labels=[f"{v:g}" for v in ticks], fontsize=11.5)
    ax.set_yticks(ticks, labels=[f"{v:g}" for v in ticks], fontsize=11.5)
    ax.tick_params(axis="x", labelrotation=90)
    ax.set_xlabel("input $x$", fontsize=12)
    ax.set_ylabel("rounded value", fontsize=12)
    ax.annotate("tie", (1.125, 1), xytext=(1.50, 0.68), fontsize=12,
                arrowprops=dict(arrowstyle="->", color=fs.INK, lw=1), va="center")
    handles = [
        Line2D([], [], color=fs.BLUE, linewidth=1.8, label="inputs sent to one grid point"),
        Line2D([], [], label="tie lands here", **filled),
        Line2D([], [], label="tie goes to the other neighbor", **opened),
        Line2D([], [], marker="s", markersize=3.4, color=fs.INK, linestyle="None",
               label="grid point: rounding fixes it"),
        Line2D([], [], color=fs.MUTED, linewidth=0.9, label="$y=x$"),
    ]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.035, 0.29),
               fontsize=11.5, labelspacing=0.55, handlelength=1.7, borderaxespad=0)
    fig.text(0.04, 0.09, "Tie: 1.125 → 1\nEven 1.00₂ wins over odd 1.01₂.",
             fontsize=12, va="top", linespacing=1.5)
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
    fig, ax = fs.figure(6.2)
    fig.subplots_adjust(left=0.1, right=0.98, bottom=0.1, top=0.97)
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
                f"spacing $2^{{{fexp(e)}}}$", ha="center", va="top", fontsize=9.5, color=fs.MUTED)
    for p in (1, 2):
        ax.axvline(p, color=fs.MUTED, linestyle=":", linewidth=0.9, zorder=1)

    ax.plot(span, span, color=fs.MUTED, linewidth=0.9, zorder=2)

    # The staircase: for each grid point, the interval of reals that rounds to it.
    tie_style_in = dict(marker="o", markersize=5.5, markerfacecolor=fs.BLUE,
                        markeredgecolor=fs.BLUE, linestyle="None", zorder=5)
    tie_style_out = dict(marker="o", markersize=5.5, markerfacecolor="white",
                         markeredgecolor=fs.BLUE, markeredgewidth=1.2, linestyle="None", zorder=5)
    for i, g in enumerate(points):
        if not (lo <= g <= hi):
            continue
        pred, succ = points[i - 1], points[i + 1]
        m_lo, m_hi = (pred + g) / 2, (g + succ) / 2
        assert round_ne(m_lo) in (pred, g) and round_ne(m_hi) in (g, succ)
        # Everything strictly between the midpoints rounds to g; the script checks a sample.
        for t in (m_lo + (m_hi - m_lo) / 3, m_lo + 2 * (m_hi - m_lo) / 3):
            assert round_ne(t) == g
        ax.plot([float(m_lo), float(m_hi)], [float(g), float(g)], color=fs.BLUE,
                linewidth=2.2, solid_capstyle="butt", zorder=4)
        ax.plot([float(m_lo)], [float(g)], **(tie_style_in if round_ne(m_lo) == g else tie_style_out))
        ax.plot([float(m_hi)], [float(g)], **(tie_style_in if round_ne(m_hi) == g else tie_style_out))
        ax.plot([float(g)], [float(g)], marker="s", markersize=4, color=fs.INK,
                linestyle="None", zorder=6)

    ticks = [float(g) for g in inside]
    ax.set_xticks(ticks, labels=[f"{t:g}" for t in ticks], fontsize=8.5)
    ax.set_yticks(ticks, labels=[f"{t:g}" for t in ticks], fontsize=8.5)
    ax.tick_params(axis="x", labelrotation=90)
    ax.set_xlabel("$x$")
    ax.set_ylabel("round to nearest even of $x$, three binary digits")

    # One tie spelled out: 1.125 goes to 1 because 1.00 is even and 1.01 is odd.
    t = Fraction(9, 8)
    r = round_ne(t)
    assert r == 1
    ax.annotate(f"the tie at {float(t):g} goes to {float(r):g},\n"
                f"significand ${significand(r)}_2$ even, ${significand(t + Fraction(1, 8))}_2$ odd",
                (float(t), float(r)), xytext=(float(t) + 0.12, float(r) - 0.42), fontsize=9,
                ha="left", va="top", zorder=7,
                bbox=dict(facecolor="white", edgecolor="none", pad=0.2),
                arrowprops=dict(arrowstyle="-|>", color=fs.INK, lw=0.9, shrinkA=2, shrinkB=4))

    handles = [
        Line2D([], [], color=fs.BLUE, linewidth=2.2, label="reals sent to one grid point"),
        Line2D([], [], label="a tie that lands here", **tie_style_in),
        Line2D([], [], label="a tie that goes to the other neighbour", **tie_style_out),
        Line2D([], [], marker="s", markersize=4, color=fs.INK, linestyle="None",
               label="grid point, fixed by rounding"),
        Line2D([], [], color=fs.MUTED, linewidth=0.9, label="$y = x$"),
    ]
    ax.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.0, 0.93), fontsize=9,
              frameon=True, facecolor="white", edgecolor="none", framealpha=1.0)

    out = fs.save(fig, "ch07-rounding-staircase.png", args.out)
    print(f"wrote {out}")
    mobile = out.with_name(out.stem + "-mobile.png")
    print(f"wrote {fs.save(draw_mobile(points, lo, hi), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
