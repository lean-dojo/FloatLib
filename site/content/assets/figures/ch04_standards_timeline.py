#!/usr/bin/env python3
"""Draw five milestones from the history chapter, with a stacked mobile arrangement.

The complete dated source inventory is retained in EVENTS. The diagram selects the Z3,
IEEE 754-1985, the 2008 revision, OCP's 2023 specifications, and the P3109 interim report.
Contextual hardware, verification and format history stays in chapter 03. Spacing expresses
chronological order, not elapsed years. The hollow P3109 marker and explicit interim label
avoid presenting a working-group report as an approved standard.

The pinned P3109 date is the 4.0.3 report release, 1 September 2026 (P3109/Public revision
34f5964, also cited by chapter 10). Other years and descriptions follow chapter 03's sources.
Run from anywhere: python3 ch04_standards_timeline.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import figstyle as fs

OUT_NAME = "ch04-standards-timeline.png"

# Source chronology; only the selected milestones below are drawn.
EVENTS = [
    (1914, "hardware", "Torres y Quevedo: a mechanical unit with a floating decimal point", False),
    (1941, "hardware", "Zuse Z3: binary, 14 significand bits, 7-bit exponent, infinite and undefined codes", False),
    (1964, "hardware", "IBM System/360: hexadecimal, 24 stored bits deliver as few as 21 of precision", False),
    (1964, "hardware", "CDC 6600: 60-bit words, 11-bit exponent, 48-bit coefficient, not correctly rounded", False),
    (1976, "hardware", "Cray-1: underflow flushed to zero with no flag", False),
    (1980, "hardware", "Intel 8087: correct rounding, gradual underflow, infinities, NaNs, sticky flags", False),
    (1985, "standard", "IEEE 754-1985: radix 2, hidden bit, gradual underflow, 4 rounding modes, 5 flags", False),
    (1987, "standard", "IEEE 854-1987: the same rules for radix 2 or 10, no bit layout fixed", False),
    (1994, "hardware", "Pentium FDIV bug: missing division table entries, about 475 million dollars", False),
    (1998, "verification", "AMD5K86 division microcode verified in ACL2 (Moore, Lynch, Kaufmann)", False),
    (1998, "verification", "AMD-K7 multiplication, division and square root verified (Russinoff)", False),
    (1999, "verification", "HOL Light theory of floating point (Harrison), then used by Intel", False),
    (2008, "standard", "IEEE 754-2008: decimal32/64/128, binary16, fused multiply-add required", False),
    (2017, "format", "Posits proposed (Gustafson and Yonemoto): run-length regime, one NaR, the quire", False),
    (2018, "format", "Mixed-precision training in binary16 with binary32 master weights (Micikevicius)", False),
    (2019, "standard", "IEEE 754-2019: minimum, maximum replace minNum, maxNum; augmented operations", False),
    (2022, "format", "E5M2 and E4M3 proposed (Micikevicius and colleagues)", False),
    (2022, "hardware", "NVIDIA H100 ships tensor cores for E5M2 and E4M3", False),
    (2022, "standard", "Posit Standard 2022: exponent field fixed at two bits, width alone names a posit", False),
    (2023, "standard", "OCP OFP8: E5M2 with IEEE conventions, E4M3FN with no infinity", False),
    (2023, "standard", "OCP Microscaling (MX): blocks share one E8M0 scale; FP6 and FP4 elements, no NaN", False),
    (2026, "standard", "P3109: interim report 4.0.3 released 1 September 2026", True),
]

# (source event index, short title, short explanation). OFP8 and MX share their 2023 node.
MILESTONES = [
    (1, "Z3", "Binary floating point"),
    (6, "IEEE 754", "Shared binary rules"),
    (12, "IEEE 754", "Decimal + required FMA"),
    (19, "OCP", "OFP8 + microscaling"),
    (21, "P3109", "Interim report 4.0.3"),
]
assert [EVENTS[index][0] for index, _, _ in MILESTONES] == [1941, 1985, 2008, 2023, 2026]
assert EVENTS[19][0] == EVENTS[20][0] == 2023
assert EVENTS[MILESTONES[-1][0]][3]


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 6.4) if mobile else (9.0, 3.2)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18, "Selected milestones", fontsize=14 if mobile else 16,
            weight="bold", va="top")
    ax.text(0.18, height - 0.66, "Hardware, standards and proposals", fontsize=11.5,
            va="top", color=fs.MUTED)
    if mobile:
        ys = [5.15 - i * 1.01 for i in range(len(MILESTONES))]
        ax.plot([0.40, 0.40], [ys[-1], ys[0]], color=fs.LINE, lw=1.5)
        for (index, title, detail), y in zip(MILESTONES, ys):
            year, kind, _, interim = EVENTS[index]
            colour = fs.GREEN if kind == "hardware" else fs.BLUE
            ax.plot(0.40, y, marker="^" if kind == "hardware" else "s", markersize=8,
                    markerfacecolor="white" if interim else colour, markeredgecolor=colour,
                    markeredgewidth=1.5)
            ax.text(0.73, y + 0.08, f"{year} · {title}", fontsize=13, weight="bold",
                    va="center")
            ax.text(0.73, y - 0.27, detail, fontsize=11.5, va="center")
        ax.text(0.18, 0.30, "Order shown; spacing is schematic.", fontsize=11.5,
                va="center", color=fs.MUTED)
    else:
        xs = [0.85 + i * 1.82 for i in range(len(MILESTONES))]
        ax.plot([xs[0], xs[-1]], [1.74, 1.74], color=fs.LINE, lw=1.5)
        details = ["Binary floating\npoint", "Shared binary\nrules", "Decimal +\nrequired FMA",
                   "OFP8 +\nmicroscaling", "Interim report\n4.0.3"]
        for (index, title, _), x, detail in zip(MILESTONES, xs, details):
            year, kind, _, interim = EVENTS[index]
            colour = fs.GREEN if kind == "hardware" else fs.BLUE
            ax.plot(x, 1.74, marker="^" if kind == "hardware" else "s", markersize=9,
                    markerfacecolor="white" if interim else colour, markeredgecolor=colour,
                    markeredgewidth=1.5)
            ax.text(x, 2.08, str(year), ha="center", va="center", fontsize=13, weight="bold")
            ax.text(x, 1.35, title, ha="center", va="center", fontsize=13, weight="bold")
            ax.text(x, 0.87, detail, ha="center", va="center", fontsize=11.5, linespacing=1.4)
        ax.text(4.50, 0.23, "Chronological order; spacing is schematic.", ha="center",
                va="center", fontsize=11.5, color=fs.MUTED)
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
