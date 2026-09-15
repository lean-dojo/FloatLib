#!/usr/bin/env python3
"""Draw content/assets/ch03-incident-timeline.png: the five incidents of the history chapter on one time line.

Each incident sits at the date the history chapter (site/content/chapters/03-a-short-history-of-floating-point.md)
gives for it, and is marked by the kind of failure the chapter attributes to it after reading the
primary source. Every date, number and attribution below is copied from the chapter text and the
sources it cites; nothing is estimated.

* Vancouver Stock Exchange index: launched January 1982 at 1000.000, closed Friday 25 November
  1983 at 524.811, recomputed to 1098.892; each recomputation truncated to three decimals
  (Quinn 1983, Lilley 1983). Drawn as a span from January 1982 to the 25 November 1983 close,
  because the loss accumulated over those 22 months.
* Patriot battery, Dhahran: 25 February 1991; clock time truncated to 23 fraction bits, 0.3433 s
  short after 100 hours (GAO/IMTEC-92-26, Skeel 1992).
* Sleipner A: 23 August 1991; not an arithmetic failure, a finite element mesh too coarse, shear
  stresses underestimated by about 47 percent (Jakobsen and Rosendahl 1994; Selby, Vecchio and
  Collins 1997).
* Pentium FDIV bug: noticed June 1994, reported to Intel 24 October 1994; five cells missing from
  the SRT division table, relative error up to about 6e-5 (Coe, Mathisen, Moler and Pratt 1995;
  Edelman 1997). Placed at the 24 October report, the day the chapter dates.
* Ariane 5 flight 501: 4 June 1996; a binary64 to 16-bit signed integer conversion overflowed,
  rounding played no part (Lions 1996).

Colour and marker encode the kind of failure; the text beside each marker repeats it, so identity
never rests on colour alone. Okabe and Ito colours from figstyle.

Run from anywhere: python3 ch03_incident_timeline.py [--out PATH]
"""

from __future__ import annotations

import argparse
import datetime as dt
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

import matplotlib.dates as mdates  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

OUT_NAME = "ch03-incident-timeline.png"

# Kind of failure -> legend label and mark. Order follows figstyle.PALETTE; the incident that was
# not an arithmetic failure is drawn hollow in black so that it reads as the odd one out.
KINDS = {
    "truncation": dict(label="truncation that accumulated", color=fs.BLUE, marker="o",
                       face=fs.BLUE),
    "overflow": dict(label="narrowing conversion overflow, not a rounding error",
                     color=fs.ORANGE, marker="s", face=fs.ORANGE),
    "table": dict(label="hardware division table error", color=fs.GREEN, marker="D",
                  face=fs.GREEN),
    "none": dict(label="not an arithmetic failure", color=fs.BLACK, marker="o", face="white"),
}

# Top row first. `side` says on which side of the marker the label sits.
INCIDENTS = [
    dict(name="Vancouver Stock Exchange index, January 1982 to 25 November 1983",
         date=dt.date(1983, 11, 25), start=dt.date(1982, 1, 1), kind="truncation", side="right",
         what=["every recomputation truncated to three decimals,",
               "574 points lost in 22 months"]),
    dict(name="Patriot battery, Dhahran, 25 February 1991",
         date=dt.date(1991, 2, 25), kind="truncation", side="left",
         what=["clock time truncated to 23 fraction bits,",
               "0.3433 s of drift after 100 hours"]),
    dict(name="Sleipner A, Gandsfjord, 23 August 1991",
         date=dt.date(1991, 8, 23), kind="none", side="left",
         what=["not arithmetic: a finite element mesh too coarse,",
               "shear stresses underestimated by about 47 percent"]),
    dict(name="Pentium FDIV bug, reported to Intel 24 October 1994",
         date=dt.date(1994, 10, 24), kind="table", side="left",
         what=["five cells missing from the SRT division table,",
               r"quotients off by up to about $6 \times 10^{-5}$ relative"]),
    dict(name="Ariane 5 flight 501, Kourou, 4 June 1996",
         date=dt.date(1996, 6, 4), kind="overflow", side="left",
         what=["binary64 to 16-bit signed integer conversion overflowed,",
               "rounding played no part"]),
]

X_START = dt.date(1981, 7, 1)
X_END = dt.date(1998, 1, 1)
MARKER_SIZE = 9.5
LABEL_GAP = 13  # points between marker and label


def draw(out: Path | None) -> Path:
    fs.setup()
    fig, ax = fs.figure(5.3)
    rows = len(INCIDENTS)

    for row, incident in enumerate(INCIDENTS):
        y = rows - 1 - row
        kind = KINDS[incident["kind"]]
        x = mdates.date2num(incident["date"])
        if "start" in incident:
            x0 = mdates.date2num(incident["start"])
            ax.plot([x0, x], [y, y], color=kind["color"], linewidth=5, alpha=0.3,
                    solid_capstyle="butt", zorder=1)
            ax.plot([x0], [y], marker="|", color=kind["color"], markersize=11,
                    markeredgewidth=1.6, linestyle="None", zorder=2)
        ax.plot([x], [y], marker=kind["marker"], color=kind["color"],
                markerfacecolor=kind["face"], markeredgecolor=kind["color"],
                markeredgewidth=1.6, markersize=MARKER_SIZE, linestyle="None", zorder=3)
        sign = 1 if incident["side"] == "right" else -1
        ha = "left" if sign > 0 else "right"
        ax.annotate(incident["name"], (x, y), xytext=(sign * LABEL_GAP, 7),
                    textcoords="offset points", ha=ha, va="bottom", fontsize=9.5,
                    fontweight="bold", color=fs.INK)
        ax.annotate("\n".join(incident["what"]), (x, y), xytext=(sign * LABEL_GAP, -4),
                    textcoords="offset points", ha=ha, va="top", fontsize=9, color=fs.MUTED,
                    linespacing=1.25)

    ax.set_xlim(mdates.date2num(X_START), mdates.date2num(X_END))
    ax.set_ylim(-0.85, rows - 0.3)
    ax.xaxis.set_major_locator(mdates.YearLocator(1))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%Y"))
    ax.yaxis.set_visible(False)
    ax.spines["left"].set_visible(False)
    ax.grid(False, axis="y")
    ax.grid(True, axis="x")
    ax.tick_params(axis="x", length=3)

    handles = [Line2D([], [], linestyle="None", marker=k["marker"], color=k["color"],
                      markerfacecolor=k["face"], markeredgecolor=k["color"],
                      markeredgewidth=1.6, markersize=8, label=k["label"])
               for k in KINDS.values()]
    ax.legend(handles=handles, loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=2,
              frameon=False, handletextpad=0.6, columnspacing=2.0)
    return fs.save(fig, OUT_NAME, out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    print(f"wrote {draw(args.out)}")


if __name__ == "__main__":
    main()
