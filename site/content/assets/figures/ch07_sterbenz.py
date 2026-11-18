#!/usr/bin/env python3
"""Draw content/assets/ch07-sterbenz.png: the region where subtraction is exact.

The chapter on rounding states Sterbenz's lemma: if y <= x <= 2y and both are
representable then x - y is representable, and in its order symmetric form
(`genericRepresentable_flx_sterbenz`) the hypothesis is y/2 <= x <= 2y. This figure shades that wedge
in the (x, y) plane and then checks the conclusion on a grid small enough to see: every pair of
grid points with three binary digits in [1/2, 4] is drawn, filled when x - y is on the grid and
open when it is not. Inside the wedge every marker is filled; the script asserts it. Outside, the
lemma promises nothing, and the picture shows both outcomes.

Sources: the wedge is the hypothesis of `genericRepresentable_flx_sterbenz` in
FloatLib/Floats/Formats/Flocq/Theory/Analysis/Sterbenz.lean (x <= 2y and y <= 2x); the grid is
`flxExp 3` in radix 2 from FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean, and
representability is `GenericRepresentable` (the scaled mantissa x * 2^-cexp(x) is an integer) with
`magnitude` and `cexp` from FloatLib/Floats/Formats/Flocq/Theory/Core.lean, re-implemented on
exact rationals below. Three binary digits is the precision the chapter uses for its own small
example.

The phone companion keeps all 169 pairs and moves the key below the plot. The counts (97 pairs
inside the wedge, 38 exact and 34 not outside it) are asserted here and stated in the caption.
--out writes both images beside the supplied path.

Run from anywhere: python3 ch07_sterbenz.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

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


def representable(v: Fraction) -> bool:
    """`GenericRepresentable`: the scaled mantissa v * 2^-cexp(v) is an integer (zero included)."""
    if v == 0:
        return True
    scaled = v / TWO ** fexp(magnitude(v))
    return scaled.denominator == 1


def grid_points(lo: Fraction, hi: Fraction) -> list[Fraction]:
    points = []
    for e in range(magnitude(lo), magnitude(hi) + 1):
        for m in range(2 ** (PREC - 1), 2 ** PREC):
            v = Fraction(m) * TWO ** (e - PREC)
            if lo <= v <= hi:
                points.append(v)
    return points


def in_wedge(x: Fraction, y: Fraction) -> bool:
    return x <= 2 * y and y <= 2 * x


EXACT = dict(marker="o", color=fs.ROLE["exact"], markerfacecolor=fs.ROLE["exact"],
             linestyle="None")
INEXACT = dict(marker="s", color=fs.ROLE["mark"], markerfacecolor="white",
               markeredgewidth=1.1, linestyle="None")


def key(size: float) -> list:
    """Legend handles shared by both arrangements."""
    return [
        Patch(facecolor=fs.SKY, alpha=0.28, edgecolor=fs.BLUE, label=r"$y/2 \leq x \leq 2y$"),
        Line2D([], [], label="$x - y$ is on the grid", markersize=size, **EXACT),
        Line2D([], [], label="$x - y$ is not on the grid", markersize=size, **INEXACT),
    ]


def draw_mobile(exact_in, exact_out, inexact_out):
    fig = plt.figure(figsize=(fs.MOBILE_WIDTH, 5.3))
    ax = fig.add_axes([0.19, 0.33, 0.78, 0.60])
    fs.value_grid(ax, "both")
    top = 4.6
    ax.set(xlim=(0, top), ylim=(0, top), aspect="equal")
    ax.fill_between([0, top], [0, top / 2], [0, 2 * top], color=fs.SKY,
                    alpha=0.28, linewidth=0, zorder=0)
    ax.plot([0, top], [0, top / 2], color=fs.BLUE, linewidth=1.2, zorder=1)
    ax.plot([0, top / 2], [0, top], color=fs.BLUE, linewidth=1.2, zorder=1)
    ax.text(2.48, 4.45, "$y=2x$", fontsize=fs.SIZE_TICK, va="top", color=fs.INK)
    ax.text(4.51, 2.66, "$x=2y$", fontsize=fs.SIZE_TICK, ha="right", color=fs.INK)
    exact_style = dict(EXACT, markersize=4.0)
    inexact_style = dict(INEXACT, markersize=4.0)
    for pairs in (exact_in, exact_out):
        ax.plot([x for x, _ in pairs], [y for _, y in pairs], zorder=3, **exact_style)
    ax.plot([x for x, _ in inexact_out], [y for _, y in inexact_out], zorder=3, **inexact_style)
    ticks = [0, 0.5, 1, 2, 3, 4]
    ax.set_xticks(ticks, labels=[f"{x:g}" for x in ticks])
    ax.set_yticks(ticks, labels=[f"{y:g}" for y in ticks])
    ax.set_xlabel("$x$")
    ax.set_ylabel("$y$")
    fs.legend(fig, handles=key(4.0), loc="upper left", bbox_to_anchor=(0.06, 0.2))
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    lo, hi = Fraction(1, 2), Fraction(4)
    points = grid_points(lo, hi)
    assert all(representable(p) for p in points)
    # Every input difference is a multiple of 1/8 in [-3.5, 3.5]. Enumerating that
    # portion of the format checks the scaled-mantissa test independently.
    positive_differences = grid_points(Fraction(1, 8), hi)
    difference_grid = {Fraction(0), *positive_differences, *(-p for p in positive_differences)}

    exact_in, exact_out, inexact_out = [], [], []
    for x in points:
        for y in points:
            exact = representable(x - y)
            assert exact == (x - y in difference_grid)
            if in_wedge(x, y):
                assert exact, (x, y)          # the lemma, checked on every pair in the wedge
                exact_in.append((float(x), float(y)))
            elif exact:
                exact_out.append((float(x), float(y)))
            else:
                inexact_out.append((float(x), float(y)))
    assert exact_out and inexact_out, "outside the wedge both outcomes should occur"
    assert (len(points), len(exact_in), len(exact_out), len(inexact_out)) == (13, 97, 38, 34)

    fs.setup()
    fig = plt.figure(figsize=(fs.WIDTH, 5.6))
    ax = fig.add_axes([0.08, 0.11, 0.58, 0.87])
    fs.value_grid(ax, "both")
    top = float(hi) + 0.6                     # room beyond the grid for the two line labels
    ax.set_xlim(0, top)
    ax.set_ylim(0, top)
    ax.set_aspect("equal")

    # The wedge y/2 <= x <= 2y, between the lines y = x/2 and y = 2x.
    ax.fill_between([0, top], [0, top / 2], [0, 2 * top], color=fs.SKY, alpha=0.28,
                    linewidth=0, zorder=0)
    ax.plot([0, top], [0, top / 2], color=fs.BLUE, linewidth=1.2, zorder=1)
    ax.plot([0, top / 2], [0, top], color=fs.BLUE, linewidth=1.2, zorder=1)
    ax.annotate("$x = 2y$", (top - 0.06, (top - 0.06) / 2),
                xytext=(0, -22), textcoords="offset points",
                ha="right", va="top", fontsize=fs.SIZE_TICK, color=fs.INK,
                bbox=dict(facecolor="white", edgecolor="none", pad=0.2))
    ax.text(top / 2 + 0.1, top - 0.06, "$y = 2x$", ha="left", va="top", fontsize=fs.SIZE_TICK,
            color=fs.INK)

    exact_style = dict(EXACT, markersize=4.5)
    inexact_style = dict(INEXACT, markersize=4.5)
    for pairs in (exact_in, exact_out):
        ax.plot([p[0] for p in pairs], [p[1] for p in pairs], zorder=3, **exact_style)
    ax.plot([p[0] for p in inexact_out], [p[1] for p in inexact_out], zorder=3, **inexact_style)

    ax.set_xlabel("$x$")
    ax.set_ylabel("$y$")
    ax.set_xticks([0, 0.5, 1, 2, 3, 4])
    ax.set_yticks([0, 0.5, 1, 2, 3, 4])

    fs.legend(fig, handles=key(4.5), loc="center left", bbox_to_anchor=(0.67, 0.55))

    out = fs.save(fig, "ch07-sterbenz.png", args.out)
    print(f"wrote {out}")
    mobile = fs.mobile_path(out)
    print(f"wrote {fs.save(draw_mobile(exact_in, exact_out, inexact_out), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
