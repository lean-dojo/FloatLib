#!/usr/bin/env python3
"""Draw ordered input-pair counts with one logarithmic scale and illustrative time labels.

For a w-bit format there are 2^w words and 2^(2w) ordered pairs. The widths (8, 16, 32, 64),
one-billion-checks-per-second assumption, and pair counts are those in chapter 04. All bit
patterns count, including zeros, infinities and NaNs where a format has them. Time is derived
from that one hypothetical rate; it is neither a measured runtime nor a hardware forecast.
A year is 365.25 days, as in the original figure. No secondary time or exponent axis is used.

Run from anywhere: python3 ch02_state_space.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
import math
from fractions import Fraction
from pathlib import Path

import figstyle as fs
from matplotlib.patches import Rectangle

OUT_NAME = "ch02-state-space.png"
FORMATS = [("8-bit formats", 5, 2), ("binary16", 5, 10),
           ("binary32", 8, 23), ("binary64", 11, 52)]
RATE = 10 ** 9
SECONDS_PER_YEAR = Fraction(1461, 4) * 24 * 3600
WIDTHS = [1 + e + f for _, e, f in FORMATS]
PAIRS = [2 ** (2 * width) for width in WIDTHS]
TIMES = [Fraction(count, RATE) for count in PAIRS]
assert WIDTHS == [8, 16, 32, 64]
assert PAIRS == [65536, 4294967296, 18446744073709551616, 340282366920938463463374607431768211456]


def time_label(seconds: Fraction) -> str:
    if seconds < Fraction(1, 1000):
        return f"{float(seconds * 10 ** 6):.0f} μs"
    if seconds < 60:
        return f"{float(seconds):.1f} s"
    years = float(seconds / SECONDS_PER_YEAR)
    if years < 1000:
        return f"{round(years, -1):.0f} years"
    exponent = math.floor(math.log10(years))
    mantissa = years / 10 ** exponent
    return rf"${mantissa:.1f}\times 10^{{{exponent}}}$ years"


assert [time_label(seconds) for seconds in TIMES[:3]] == ["66 μs", "4.3 s", "580 years"]
assert time_label(TIMES[3]) == r"$1.1\times 10^{22}$ years"


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 6.5) if mobile else (9.0, 6.0)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18, r"$w$-bit inputs give $2^{2w}$ pairs", fontsize=14 if mobile else 16,
            weight="bold", va="top")
    ax.text(0.18, height - 0.70, "At 1 billion checks/s (illustrative)", fontsize=11.5,
            va="top", color=fs.MUTED)
    left, right = 0.25, width - 0.25
    first_y, step = (4.60, 1.03) if mobile else (4.17, 1.00)
    colours = [fs.BLUE, fs.ORANGE, fs.GREEN, fs.VERMILION]
    # A linear position in log2(count) is exactly a logarithmic count axis. Bar lengths
    # therefore encode log counts, not a linear ratio of the actual pair counts.
    for index, ((name, _, _), bits, seconds, colour) in enumerate(zip(FORMATS, WIDTHS, TIMES, colours)):
        y = first_y - index * step
        ax.text(left, y + 0.47, name, fontsize=12.5, weight="bold", va="center")
        ax.text(right, y + 0.47, rf"$2^{{{2 * bits}}}$ pairs", fontsize=14 if mobile else 12.5,
                ha="right", va="center")
        ax.add_patch(Rectangle((left, y + 0.07), (right - left) * (2 * bits) / 128, 0.17,
                               facecolor=colour, edgecolor="none"))
        label = time_label(seconds)
        ax.text(left, y - 0.17, label, fontsize=14 if "$" in label else 11.5, va="center")
    axis_y = 0.79 if mobile else 0.63
    ax.plot([left, right], [axis_y, axis_y], color=fs.INK, lw=0.8)
    for exponent in [0, 32, 64, 96, 128]:
        x = left + (right - left) * exponent / 128
        ax.plot([x, x], [axis_y - 0.05, axis_y + 0.05], color=fs.INK, lw=0.8)
        label = "1" if exponent == 0 else rf"$2^{{{exponent}}}$"
        ax.text(x, axis_y - 0.24, label, ha="center", va="center", fontsize=14 if mobile else 12.5)
    ax.text(width / 2, 0.16, "Ordered input pairs (log scale)", fontsize=11.5,
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
