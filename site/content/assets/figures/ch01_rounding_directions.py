#!/usr/bin/env python3
"""Draw the four IEEE rounding directions on three exact integer-grid midpoint inputs.

The values -2.5, 2.5 and 3.5 and the four modes come from chapter 02. This is rounding to
integers, not a claim that these are adjacent values in binary32. Each small number line has
its own labelled integer neighbours. All twelve results are computed from Fractions; the
chapter's displayed results are asserted below. Constructor names stay in source and prose.

Run from anywhere: python3 ch01_rounding_directions.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
import math
from fractions import Fraction
from pathlib import Path

import figstyle as fs

OUT_NAME = "ch01-rounding-directions.png"
INPUTS = [Fraction(-5, 2), Fraction(5, 2), Fraction(7, 2)]
DIRECTIONS = [
    ("Nearest even", ".nearestEven", round, fs.BLUE),
    ("Toward zero", ".towardZero", math.trunc, fs.ORANGE),
    ("Toward +∞", ".towardPositiveInfinity", math.ceil, fs.GREEN),
    ("Toward −∞", ".towardNegativeInfinity", math.floor, fs.VERMILION),
]
RESULTS = [[fn(value) for value in INPUTS] for _, _, fn, _ in DIRECTIONS]
assert RESULTS == [[-2, 2, 4], [-2, 2, 3], [-2, 3, 4], [-3, 2, 3]]


def integer_text(value):
    return str(value).replace("-", "−")


def round_arrow(ax, left, right, y, value, result, colour):
    low, high = math.floor(value), math.ceil(value)
    assert high == low + 1 and result in (low, high)
    middle = (left + right) / 2
    target = left if result == low else right
    ax.plot([left, right], [y, y], color=fs.LINE, lw=0.9, zorder=0)
    ax.plot([left, right], [y, y], "|", color=fs.MUTED, markersize=7, zorder=1)
    ax.annotate("", xy=(target, y), xytext=(middle, y),
                arrowprops=dict(arrowstyle="-|>", color=colour, lw=1.5, shrinkA=4, shrinkB=5))
    ax.plot(middle, y, marker="D", markersize=6.5, markerfacecolor="white",
            markeredgecolor=fs.INK, markeredgewidth=1.1, zorder=3)
    ax.plot(target, y, "o", color=colour, markersize=6, zorder=3)


def legend(ax, width, y):
    left = 0.28 if width < 4 else 2.65
    ax.plot(left, y, marker="D", markersize=6, markerfacecolor="white",
            markeredgecolor=fs.INK, markeredgewidth=1.1)
    ax.text(left + 0.15, y, "Exact input", fontsize=11.5, va="center")
    next_x = 1.88 if width < 4 else 4.65
    ax.plot(next_x, y, "o", color=fs.INK, markersize=6)
    ax.text(next_x + 0.15, y, "Rounded integer", fontsize=11.5, va="center")


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 8.2) if mobile else (9.0, 4.2)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18,
            "Rounding halfway inputs\nto integers" if mobile else "Rounding halfway inputs to integers",
            fontsize=14 if mobile else 16, weight="bold", va="top")
    if mobile:
        for column, value in enumerate(INPUTS):
            top = 6.94 - column * 2.14
            ax.text(0.23, top, f"x = {integer_text(float(value))}", fontsize=13,
                    weight="bold", va="center")
            left, right = 2.03, 3.52
            for x, integer in ((left, math.floor(value)), (right, math.ceil(value))):
                ax.text(x, top, integer_text(integer), fontsize=12, ha="center", va="center")
                ax.plot([x, x], [top - 0.29, top - 1.70], color=fs.LINE, lw=0.6, linestyle=":")
            for row, (label, _, _, colour) in enumerate(DIRECTIONS):
                y = top - 0.43 - row * 0.40
                ax.text(0.23, y, label, fontsize=11.5, va="center")
                round_arrow(ax, left, right, y, value, RESULTS[row][column], colour)
            if column < len(INPUTS) - 1:
                ax.plot([0.23, 3.57], [top - 1.89, top - 1.89], color=fs.LINE, lw=0.7)
        legend(ax, width, 0.36)
    else:
        for row, (label, _, _, colour) in enumerate(DIRECTIONS):
            y = 2.58 - row * 0.62
            ax.text(0.25, y, label, fontsize=12.5, va="center")
        for column, value in enumerate(INPUTS):
            left, right = 2.30 + column * 2.28, 3.86 + column * 2.28
            ax.text((left + right) / 2, 3.34, f"x = {integer_text(float(value))}",
                    ha="center", va="center", fontsize=13, weight="bold")
            for x, integer in ((left, math.floor(value)), (right, math.ceil(value))):
                ax.text(x, 2.97, integer_text(integer), ha="center", va="center", fontsize=12)
                ax.plot([x, x], [2.77, 0.58], color=fs.LINE, lw=0.6, linestyle=":")
            for row, (_, _, _, colour) in enumerate(DIRECTIONS):
                round_arrow(ax, left, right, 2.58 - row * 0.62, value, RESULTS[row][column], colour)
        legend(ax, width, 0.22)
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
