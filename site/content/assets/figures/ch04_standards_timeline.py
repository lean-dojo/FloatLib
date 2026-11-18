#!/usr/bin/env python3
"""Draw five milestones from the history chapter, with a stacked mobile arrangement.

The complete dated source inventory is retained in EVENTS. The diagram selects the Z3,
IEEE 754-1985, the 2008 revision, OCP's 2023 specifications, and the P3109 interim report.
Contextual hardware, verification and format history stays in the chapter on floating-point representations. Spacing expresses
chronological order, not elapsed years. The hollow P3109 marker and explicit interim label
avoid presenting a working-group report as an approved standard.

The pinned P3109 date is the 4.1 report release, 14 September 2026 (P3109/Public revision
2d45cf2, the version the library follows). Other years and descriptions follow the sources in the chapter on floating-point representations.
Run from anywhere: python3 ch04_standards_timeline.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import figstyle as fs
from matplotlib.lines import Line2D

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
    (2023, "standard", "OCP OFP8: E5M2 with IEEE conventions, E4M3 with no infinity", False),
    (2023, "standard", "OCP Microscaling (MX): blocks share one E8M0 scale; FP6 and FP4 elements, no NaN", False),
    (2026, "standard", "P3109: interim report 4.1 released 14 September 2026", True),
]

# (source event index, short title, short explanation). OFP8 and MX share their 2023 node.
MILESTONES = [
    (1, "Z3", "binary floating point"),
    (6, "IEEE 754", "shared binary rules"),
    (12, "IEEE 754", "decimal formats, required FMA"),
    (19, "OCP", "OFP8 and microscaling"),
    (21, "P3109", "interim report 4.1"),
]
assert [EVENTS[index][0] for index, _, _ in MILESTONES] == [1941, 1985, 2008, 2023, 2026]
assert EVENTS[19][0] == EVENTS[20][0] == 2023
assert EVENTS[MILESTONES[-1][0]][3]


def marker(kind: str, interim: bool) -> dict:
    """One mark per kind of milestone: a machine, a published standard, an interim report."""
    return dict(marker="^" if kind == "hardware" else "s",
                markerfacecolor="white" if interim else fs.ROLE["main"],
                markeredgecolor=fs.ROLE["main"], markeredgewidth=1.5)


def key(ax, x: float, y: float, columns: int) -> None:
    handles = [
        Line2D([], [], linestyle="none", markersize=8, label=label, **marker(kind, interim))
        for kind, interim, label in (("hardware", False, "machine"),
                                     ("standard", False, "standard"),
                                     ("standard", True, "interim report"))
    ]
    fs.legend(ax, handles=handles, loc="center", bbox_to_anchor=(x, y),
              bbox_transform=ax.transData, ncols=columns)


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (fs.MOBILE_WIDTH, 5.6) if mobile else (fs.WIDTH, 2.5)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    if mobile:
        ys = [5.15 - i * 1.01 for i in range(len(MILESTONES))]
        ax.plot([0.40, 0.40], [ys[-1], ys[0]], color=fs.LINE, lw=1.5)
        for (index, title, detail), y in zip(MILESTONES, ys):
            year, kind, _, interim = EVENTS[index]
            ax.plot(0.40, y, markersize=8, **marker(kind, interim))
            ax.text(0.73, y + 0.08, f"{year} · {title}", fontsize=fs.SIZE_LABEL,
                    va="center")
            ax.text(0.73, y - 0.27, detail, fontsize=fs.SIZE_TICK, va="center", color=fs.MUTED)
        key(ax, width / 2, 0.30, 1)
    else:
        xs = [0.85 + i * 1.82 for i in range(len(MILESTONES))]
        ax.plot([xs[0], xs[-1]], [1.74, 1.74], color=fs.LINE, lw=1.5)
        details = ["binary floating\npoint", "shared binary\nrules", "decimal formats,\nrequired FMA",
                   "OFP8 and\nmicroscaling", "interim report\n4.1"]
        for (index, title, _), x, detail in zip(MILESTONES, xs, details):
            year, kind, _, interim = EVENTS[index]
            ax.plot(x, 1.74, markersize=9, **marker(kind, interim))
            ax.text(x, 2.08, str(year), ha="center", va="center", fontsize=fs.SIZE_LABEL)
            ax.text(x, 1.35, title, ha="center", va="center", fontsize=fs.SIZE_LABEL)
            ax.text(x, 0.87, detail, ha="center", va="center", fontsize=fs.SIZE_TICK, linespacing=1.4,
                    color=fs.MUTED)
        key(ax, width / 2, 0.23, 3)
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
