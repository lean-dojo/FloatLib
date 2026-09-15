#!/usr/bin/env python3
"""Draw content/assets/ch02-state-space.png: how exhaustive testing grows with width.

The correctness chapter ("The state space") counts the ordered input pairs of a binary operation at four
encoded widths and converts each count to a running time at a billion tests per second. This
figure puts those four points on one log axis and reads them twice, as a count on the left and
as a time on the right. At the assumed rate, enumerating binary32 and binary64 is impractical.

Sources:
* widths: the descriptors in FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean,
  each 1 + expWidth + fracWidth bits: e5m2 (5 + 2) and e4m3fn (4 + 3) for eight bits,
  binary16 (5 + 10), binary32 (8 + 23), binary64 (11 + 52);
* the count 2^(2w) at width w and the hypothetical rate of 10^9 tests per second are from
  the chapter. The figure does not claim a universal feasibility cutoff or that the full
  binary16 comparison has been run;
* every time label is count / 10^9 seconds, converted with 3600 s per hour, 86400 s per day and
  365.25 days per year, and printed to two significant figures, which is how chapter 15 rounds
  its speed-ups. The chapter's own figures ("a few hundred years", "about 10^22 years") are
  what these labels round to.

No binary128 point is drawn, because the section does not discuss that width.

Run from anywhere: python3 ch02_state_space.py [--out PNG]
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

# (label, expWidth, fracWidth) as declared in Catalog.lean.
FORMATS = (
    ("eight-bit formats", 5, 2),
    ("binary16", 5, 10),
    ("binary32", 8, 23),
    ("binary64", 11, 52),
)
RATE = 10 ** 9                                   # tests per second, from the chapter
SECONDS_PER_HOUR = 3600
SECONDS_PER_DAY = 86400
SECONDS_PER_YEAR = 365.25 * SECONDS_PER_DAY
SMALL_WIDTHS = {8, 16}

XLABEL = "encoded width of each operand (bits)"
YLABEL = "ordered input pairs of one binary operation, $2^{2w}$ at width $w$"
Y2LABEL = "time to run them all at a billion tests per second (seconds)"
LEGEND_SMALL = "8 and 16 bits: feasible to enumerate at the assumed rate"
LEGEND_LARGE = "binary32 and binary64: impractical to enumerate at the assumed rate"


def encoded_width(exp_width: int, frac_width: int) -> int:
    return 1 + exp_width + frac_width


def two_figures(value: float) -> str:
    """Two significant figures, printed without an exponent."""
    exponent = math.floor(math.log10(value))
    rounded = round(value, 1 - exponent)
    if rounded >= 10:
        return f"{int(round(rounded))}"
    return f"{rounded:.1f}"


def time_label(seconds: float) -> str:
    if seconds < 1e-3:
        return f"{two_figures(seconds * 1e6)} microseconds"
    if seconds < 60:
        return f"{two_figures(seconds)} seconds"
    if seconds < SECONDS_PER_DAY:
        return f"{two_figures(seconds / SECONDS_PER_HOUR)} hours"
    if seconds < SECONDS_PER_YEAR:
        return f"{two_figures(seconds / SECONDS_PER_DAY)} days"
    years = seconds / SECONDS_PER_YEAR
    if years < 1e4:
        return f"{two_figures(years)} years"
    exponent = math.floor(math.log10(years))
    mantissa = round(years / 10 ** exponent, 1)
    return rf"${mantissa} \times 10^{{{exponent}}}$ years"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    widths = [encoded_width(e, f) for _, e, f in FORMATS]
    pairs = [2 ** (2 * w) for w in widths]

    fig, ax = fs.figure(5.2)
    fig.subplots_adjust(left=0.1, right=0.88, bottom=0.11, top=0.83)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xlim(2 ** 2.7, 2 ** 7.3)
    ylim = (1e1, 1e42)   # room under the eight-bit point for its two-line label
    ax.set_ylim(*ylim)
    ax.set_xticks(widths, labels=[str(w) for w in widths])
    ax.minorticks_off()
    ax.set_xlabel(XLABEL)
    ax.set_ylabel(YLABEL)

    # Reference durations, drawn where count / RATE equals one second, hour, year.
    for seconds, name in ((1, "one second"), (SECONDS_PER_HOUR, "one hour"),
                          (SECONDS_PER_YEAR, "one year")):
        y = seconds * RATE
        ax.axhline(y, color=fs.MUTED, linestyle=":", linewidth=0.9, zorder=1)
        ax.text(2 ** 7.25, y, name, ha="right", va="bottom", fontsize=9, color=fs.MUTED)

    ax.plot(widths, pairs, color=fs.MUTED, linewidth=1.2, zorder=2)
    small_style = dict(marker="o", markersize=8, color=fs.BLUE, markerfacecolor=fs.BLUE,
                            markeredgewidth=1.6, linestyle="None")
    large_style = dict(marker="s", markersize=8, color=fs.VERMILION, markerfacecolor="white",
                         markeredgewidth=1.6, linestyle="None")
    for (label, _e, _f), w, count in zip(FORMATS, widths, pairs):
        style = small_style if w in SMALL_WIDTHS else large_style
        ax.plot([w], [count], zorder=4, **style)
        text = f"{label}: $2^{{{2 * w}}}$ pairs\n{time_label(count / RATE)}"
        ax.annotate(text, (w, count), textcoords="offset points", xytext=(11, -2),
                    ha="left", va="top", fontsize=9,
                    bbox=dict(facecolor="white", edgecolor="none", pad=1.5), zorder=5)

    # Right axis: the same points read as seconds at the chapter's rate.
    ax2 = ax.twinx()
    ax2.set_yscale("log")
    ax2.set_ylim(ylim[0] / RATE, ylim[1] / RATE)
    ax2.set_ylabel(Y2LABEL)
    ax2.grid(False)
    ax2.spines["right"].set_visible(True)
    ax2.spines["left"].set_visible(False)
    ax2.spines["top"].set_visible(False)
    ax2.minorticks_off()

    handles = [Line2D([], [], label=LEGEND_SMALL, **small_style),
               Line2D([], [], label=LEGEND_LARGE, **large_style)]
    fig.legend(handles=handles, loc="upper center", ncol=1, bbox_to_anchor=(0.5, 0.97))

    out = fs.save(fig, "ch02-state-space.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
