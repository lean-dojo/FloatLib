#!/usr/bin/env python3
"""Draw the mechanisms of five incidents from chapter 03, in chronological order.

The full dates and quantitative detail remain in that chapter and its cited primary sources:
* Vancouver: January 1982 to 25 November 1983; three-decimal truncation on each update.
  The close was 524.811, recomputed to 1098.892, a difference of 574.081 (Quinn/Lilley 1983).
* Patriot: 25 February 1991; inconsistent clock conversions at different precisions make
  elapsed-time errors grow with uptime. The truncated conversion is short by 0.3433 s after
  100 hours (GAO/IMTEC-92-26; Skeel 1992). Mere cancellation of two equally converted times
  would not explain the failure, so the diagram explicitly names the inconsistent conversions.
* Sleipner A: 23 August 1991; a coarse finite-element mesh underestimated shear stress by
  about 47 percent. This is a model/discretization error, not an arithmetic error
  (Jakobsen/Rosendahl 1994; Selby/Vecchio/Collins 1997).
* Pentium FDIV: reported to Intel on 24 October 1994; five missing SRT table cells,
  quotient relative errors up to about 6e-5 (Coe et al. 1995; Edelman 1997).
* Ariane 5 flight 501: 4 June 1996; binary64 to signed Int16 conversion outside range,
  followed by an unhandled exception. Rounding played no part (Lions 1996).

Rows are ordered by date, not laid out on a quantitative time axis. Arrows connect a failure
mechanism to its consequence, not one incident to the next. All five incidents are retained.
Run from anywhere: python3 ch03_incident_timeline.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import figstyle as fs

OUT_NAME = "ch03-incident-timeline.png"
# name, year/span, mechanism, consequence, colour
INCIDENTS = [
    ("Vancouver index", "1982/83", "Repeated truncation", "Downward index bias", fs.BLUE),
    ("Patriot", "1991", "Unequal clock conversions", "Timing error grows with uptime", fs.BLUE),
    ("Sleipner A", "1991", "Coarse mesh (model error)", "Shear stress underestimated", fs.INK),
    ("Pentium FDIV", "1994", "Missing lookup-table entries", "Wrong quotients", fs.GREEN),
    ("Ariane 5", "1996", "Float → Int16 outside range", "Inertial unit shuts down", fs.ORANGE),
]


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 8.5) if mobile else (9.0, 5.8)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18,
            "Five failures,\nfive mechanisms" if mobile else "Five failures, five mechanisms",
            fontsize=14 if mobile else 16, weight="bold", va="top")
    if mobile:
        for index, (name, year, mechanism, consequence, colour) in enumerate(INCIDENTS):
            y = 7.26 - index * 1.42
            ax.text(0.23, y, f"{name} · {year}", fontsize=12.5, weight="bold", va="center")
            ax.text(0.23, y - 0.38, mechanism, fontsize=11.5, va="center")
            fs.arrow(ax, (0.34, y - 0.56), (0.34, y - 0.90), color=colour)
            ax.text(0.56, y - 0.85, consequence, fontsize=11.5, va="center")
            if index < len(INCIDENTS) - 1:
                ax.plot([0.23, 3.57], [y - 1.15, y - 1.15], color=fs.LINE, lw=0.7)
    else:
        for x, label in ((0.25, "Incident"), (2.65, "Mechanism"), (6.25, "Consequence")):
            ax.text(x, 4.82, label, fontsize=11.5, color=fs.MUTED, va="center")
        mechanisms = ["Truncate every\nindex update", "Mix clock-conversion\nprecisions",
                      "Coarse mesh\n(model error)", "Missing division-\ntable entries",
                      "Float → Int16\noutside range"]
        consequences = ["Persistent\ndownward bias", "Uptime-dependent\ntiming error",
                        "Shear stress\nunderestimated", "Wrong quotients\nfor some inputs",
                        "Inertial unit\nshuts down"]
        for index, ((name, year, _, _, colour), mechanism, consequence) in enumerate(
                zip(INCIDENTS, mechanisms, consequences)):
            y = 4.17 - index * 0.86
            ax.text(0.25, y + 0.12, name, fontsize=12.5, weight="bold", va="center")
            ax.text(0.25, y - 0.18, year, fontsize=11.5, color=fs.MUTED, va="center")
            ax.text(2.65, y, mechanism, fontsize=12, va="center", linespacing=1.3)
            fs.arrow(ax, (5.58, y), (6.05, y), color=colour)
            ax.text(6.25, y, consequence, fontsize=12, va="center", linespacing=1.3)
            if index < len(INCIDENTS) - 1:
                ax.plot([0.25, 8.75], [y - 0.43, y - 0.43], color=fs.LINE, lw=0.7)
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
