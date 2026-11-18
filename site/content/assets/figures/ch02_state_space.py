#!/usr/bin/env python3
"""Draw ordered input-pair counts with one logarithmic scale and illustrative time labels.

For a w-bit format there are 2^w words and 2^(2w) ordered pairs. The widths (8, 16, 32, 64),
one-billion-checks-per-second assumption, and pair counts are those in the chapter on floating-point representations. All bit
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
    width, height = (fs.MOBILE_WIDTH, 3.4) if mobile else (fs.WIDTH, 2.9)
    fig, ax = fs.plt.subplots(figsize=(width, height))
    names = [name for name, _, _ in FORMATS]
    exponents = [2 * bits for bits in WIDTHS]
    positions = range(len(names))
    # A linear position in log2(count) is exactly a logarithmic count axis. Bar lengths
    # therefore encode log counts, not a linear ratio of the actual pair counts.
    ax.barh(positions, exponents, height=0.5, color=fs.ROLE["main"])
    for position, exponent, seconds in zip(positions, exponents, TIMES):
        ax.text(exponent + 2, position, time_label(seconds), va="center", ha="left",
                fontsize=fs.SIZE_TICK)
    ax.set_yticks(list(positions), labels=names)
    ax.invert_yaxis()
    ax.set_xlim(0, 215 if mobile else 152)
    ticks = [0, 64, 128] if mobile else [0, 32, 64, 96, 128]
    ax.set_xticks(ticks, labels=["1" if tick == 0 else rf"$2^{{{tick}}}$" for tick in ticks])
    ax.set_xlabel("ordered input pairs")
    ax.tick_params(axis="y", length=0)
    fs.value_grid(ax, "x")
    fig.tight_layout()
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    target = args.out or fs.ASSETS / OUT_NAME
    for mobile in (False, True):
        path = fs.mobile_path(target) if mobile else target
        print(f"wrote {fs.save(build_figure(mobile), OUT_NAME, path)}")


if __name__ == "__main__":
    main()
