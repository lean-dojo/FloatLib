#!/usr/bin/env python3
"""Draw content/assets/ch01-rounding-directions.png: the four IEEE rounding directions.

Chapter 02 introduces the four rounding directions a binary format must provide, the four
constructors of `Model.IEEERoundingMode`, and shows them on integers with `roundToIntegral`,
where the representable set is the integers and the inputs 2.5, 3.5 and -2.5 are exact
midpoints. The figure draws those three inputs on the integer line and, one row per direction,
an arrow from each input to the integer that direction chooses.

Sources:

* the five results the chapter evaluates
  (site/content/chapters/02-from-reals-to-machine-numbers.md, the `roundToIntegral` block):
  2.5 to 2 and 3.5 to 4 under `.nearestEven`, 2.5 to 2 under `.towardZero`, 2.5 to 3 under
  `.towardPositiveInfinity`, and -2.5 to -3 under `.towardNegativeInfinity`; the script asserts
  each of them;
* the remaining seven cells follow from the chapter's description of the four theorems
  `toReal_roundToIntegral_*`: the result is the nearest-even integer, the truncation, the
  ceiling or the floor of the input. They are computed here with Python's `round` (which
  rounds halves to even), `math.trunc`, `math.ceil` and `math.floor` on exact fractions.

Run from anywhere: python3 ch01_rounding_directions.py [--out PNG]
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

INPUTS = [Fraction(-5, 2), Fraction(5, 2), Fraction(7, 2)]

# (description, Lean constructor, rounding function); drawn top to bottom in this order.
DIRECTIONS = [
    ("nearest, ties to even", ".nearestEven", lambda x: round(x)),
    ("toward zero", ".towardZero", math.trunc),
    ("toward positive", ".towardPositiveInfinity", math.ceil),
    ("toward negative", ".towardNegativeInfinity", math.floor),
]

# The cells the chapter evaluates in Lean, as (input, constructor, result).
CHAPTER_RESULTS = [
    (Fraction(5, 2), ".nearestEven", 2),
    (Fraction(7, 2), ".nearestEven", 4),
    (Fraction(5, 2), ".towardZero", 2),
    (Fraction(5, 2), ".towardPositiveInfinity", 3),
    (Fraction(-5, 2), ".towardNegativeInfinity", -3),
]

MONO = "DejaVu Sans Mono"
LABEL_X = -4.3          # right edge of the row labels
LINE_LO, LINE_HI = -4, 4


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    table = {(x, name): int(fn(x)) for _d, name, fn in DIRECTIONS for x in INPUTS}
    for x, name, expected in CHAPTER_RESULTS:
        assert table[(x, name)] == expected, (x, name, table[(x, name)], expected)

    fig, ax = fs.figure(3.6)
    fig.subplots_adjust(left=0.01, right=0.99, top=0.99, bottom=0.01)
    ax.set_xlim(-9.8, 7.6)
    ax.set_ylim(-1.05, 5.15)
    ax.axis("off")
    ax.grid(False)

    rows = [3.7, 2.75, 1.8, 0.85]
    # The representable set: the integers, as a number line with a light guide above each one.
    ax.plot([LINE_LO - 0.3, LINE_HI + 0.3], [0, 0], color=fs.INK, linewidth=1.0, zorder=1)
    for n in range(LINE_LO, LINE_HI + 1):
        ax.plot([n, n], [0, rows[0] + 0.25], color=fs.LINE, linewidth=0.7, zorder=0)
        ax.plot([n], [0], marker="o", markersize=5, color=fs.INK, zorder=3)
        ax.text(n, -0.22, str(n), ha="center", va="top", fontsize=9.5, color=fs.INK)

    for (description, constructor, _fn), y in zip(DIRECTIONS, rows):
        ax.text(LABEL_X, y + 0.05, description, ha="right", va="bottom", fontsize=9.5,
                color=fs.INK)
        ax.text(LABEL_X, y - 0.05, constructor, ha="right", va="top", fontsize=9, family=MONO,
                color=fs.MUTED)
        for x in INPUTS:
            target = table[(x, constructor)]
            fs.arrow(ax, (float(x), y), (target, y), color=fs.BLUE, linewidth=1.6, shrink=0.0)
            ax.plot([float(x)], [y], marker="D", markersize=6.5, markerfacecolor="white",
                    markeredgecolor=fs.VERMILION, markeredgewidth=1.5, zorder=4)
    for x in INPUTS:
        ax.text(float(x), rows[0] + 0.32, f"{float(x)}", ha="center", va="bottom", fontsize=9.5,
                color=fs.VERMILION)
    ax.text(LINE_HI + 0.55, rows[0], "every input here is a midpoint,\nso the tie goes to the "
            "even integer", ha="left", va="center", fontsize=9, color=fs.MUTED, linespacing=1.25)
    ax.text(LINE_HI + 0.55, rows[1], "discards the excess:\nthe neighbour nearer zero",
            ha="left", va="center", fontsize=9, color=fs.MUTED, linespacing=1.25)
    ax.text(LINE_HI + 0.55, rows[2], "the neighbour above", ha="left", va="center", fontsize=9,
            color=fs.MUTED)
    ax.text(LINE_HI + 0.55, rows[3], "the neighbour below", ha="left", va="center", fontsize=9,
            color=fs.MUTED)

    ax.text(-9.8, 5.1, "Rounding to an integer under the four directions of "
            "Model.IEEERoundingMode (the representable values are the integers)",
            ha="left", va="top", fontsize=10.5, color=fs.INK)
    ax.text(-9.8, -0.95, "open diamond: the exact input x; arrow: the representable value the "
            "direction chooses, as the chapter's roundToIntegral examples print it",
            ha="left", va="bottom", fontsize=9, color=fs.MUTED)

    out = fs.save(fig, "ch01-rounding-directions.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
