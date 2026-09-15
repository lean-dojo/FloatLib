#!/usr/bin/env python3
"""Draw content/assets/ch04-standards-timeline.png: the dated events of the history chapter on one ruler.

The history chapter (site/content/chapters/03-a-short-history-of-floating-point.md) dates the machines
before the standard, the IEEE standards and their revisions, the hardware verification work that
followed the Pentium bug, the machine learning formats and their specifications, and the posit
standard. Every event below is one the chapter text gives a year for, at that year, in the
chapter's words; events the chapter mentions without a year in its prose (the VAX formats,
bfloat16, the ONNX FNUZ variants, TF32) are left out rather than dated from memory. P3109 is
drawn hollow for the working group's interim report v4.0.3, released 1 September 2026.
The PDF cover at P3109/Public revision 34f5964 supplies the release date; chapter 10 cites it.

The ruler on the left is to scale; the labels on the right are evenly spaced so that the dense
years read, and a leader joins each label to its exact place on the ruler. Two events in one year
sit side by side on the ruler. Colour and marker encode the kind of event, and the marker is
repeated before each label, so identity never rests on colour alone. Okabe and Ito colours from
figstyle, assigned in the palette's fixed order.

Run from anywhere: python3 ch04_standards_timeline.py [--out PATH]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.lines import Line2D  # noqa: E402

OUT_NAME = "ch04-standards-timeline.png"

KINDS = {
    "standard": dict(label="standard or specification", color=fs.BLUE, marker="s"),
    "format": dict(label="format family", color=fs.ORANGE, marker="o"),
    "hardware": dict(label="hardware", color=fs.GREEN, marker="^"),
    "verification": dict(label="verification", color=fs.VERMILION, marker="D"),
}

# (year, kind, text, interim). Chronological; same-year events keep the chapter's order.
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

RULER_X = 0.65          # inches from the left edge of the figure
RULER_TOP, RULER_BOTTOM = 1910, 2030
SLOT_STEP = 0.17        # horizontal offset between marker slots beside the ruler
SLOT_MIN_YEARS = 3      # markers closer than this in years never share a slot
GUTTER_X = 1.5          # leaders run level from the marker to here, then slant to the label
LABEL_MARK_X = 2.35     # the repeated marker before each label
YEAR_X = 2.5
TEXT_X = 2.92
LABEL_TOP, LABEL_BOTTOM = 1913, 2027   # the evenly spaced label column, in ruler years
HEIGHT = 7.0
MARKER_SIZE = 7.5


def assign_slots(years: list[int]) -> list[int]:
    """Give each event the leftmost slot whose previous occupant is at least SLOT_MIN_YEARS away,
    so that markers a year or two apart never overlap on the ruler."""
    last_in_slot: list[int] = []
    slots = []
    for year in years:
        for slot, last in enumerate(last_in_slot):
            if year - last >= SLOT_MIN_YEARS:
                break
        else:
            slot = len(last_in_slot)
            last_in_slot.append(year)
        last_in_slot[slot] = year
        slots.append(slot)
    return slots


def marker_kwargs(kind: str, interim: bool, size: float = MARKER_SIZE) -> dict:
    k = KINDS[kind]
    return dict(marker=k["marker"], color=k["color"], markerfacecolor="white" if interim else k["color"],
                markeredgecolor=k["color"], markeredgewidth=1.4, markersize=size, linestyle="None")


def draw(out: Path | None) -> Path:
    fs.setup()
    fig = fs.figure(HEIGHT)[0]
    fig.clf()
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, fs.WIDTH)
    ax.set_ylim(RULER_BOTTOM + 6, RULER_TOP - 14)   # years increase downwards; room at the top
    ax.axis("off")
    ax.grid(False)

    # The ruler, to scale, with a labelled tick every ten years.
    ax.plot([RULER_X, RULER_X], [RULER_TOP, RULER_BOTTOM], color=fs.INK, linewidth=1.0, zorder=2)
    for year in range(RULER_TOP, RULER_BOTTOM + 1, 10):
        ax.plot([RULER_X - 0.07, RULER_X], [year, year], color=fs.INK, linewidth=0.8, zorder=2)
        ax.text(RULER_X - 0.12, year, str(year), ha="right", va="center", fontsize=9,
                color=fs.MUTED)

    # Labels are evenly spaced; markers sit at their exact year, in slots beside the ruler so
    # that near-coincident years stay apart. A leader runs level from the marker to the gutter
    # and then slants to its label, so no slanted line passes behind another year's marker.
    n = len(EVENTS)
    label_ys = [LABEL_TOP + i * (LABEL_BOTTOM - LABEL_TOP) / (n - 1) for i in range(n)]
    slots = assign_slots([year for year, _kind, _text, _interim in EVENTS])
    for (year, kind, text, interim), slot, y_label in zip(EVENTS, slots, label_ys):
        x_mark = RULER_X + slot * SLOT_STEP
        ax.plot([x_mark, GUTTER_X, LABEL_MARK_X - 0.1], [year, year, y_label], color=fs.LINE,
                linewidth=0.9, zorder=1, solid_joinstyle="round")
        ax.plot([x_mark], [year], zorder=3, **marker_kwargs(kind, interim))
        ax.plot([LABEL_MARK_X], [y_label], zorder=3, **marker_kwargs(kind, interim, size=6.5))
        ax.text(YEAR_X, y_label, str(year), ha="left", va="center", fontsize=9,
                fontweight="bold", color=fs.INK)
        ax.text(TEXT_X, y_label, text, ha="left", va="center", fontsize=9, color=fs.INK)

    handles = [Line2D([], [], label=k["label"], **marker_kwargs(kind, False, size=7))
               for kind, k in KINDS.items()]
    handles.append(Line2D([], [], label="interim report (hollow)",
                          **marker_kwargs("standard", True, size=7)))
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.5, 0.995), ncol=5,
               frameon=False, handletextpad=0.5, columnspacing=1.8)
    return fs.save(fig, OUT_NAME, out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    print(f"wrote {draw(args.out)}")


if __name__ == "__main__":
    main()
