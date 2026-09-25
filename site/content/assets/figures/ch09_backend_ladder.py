#!/usr/bin/env python3
"""Draw eligibility, estimated cost, and selection for one configured addition.

The example is ExecFloat.Binary 4 3 (IEEE E4M3, not E4M3FN), using UInt8 storage and
Policy.default. Chapter 14 supplies the worked example. Numerical inputs come from:

* Descriptor/Plan/Estimates.lean: tableGenerationCost, tableEstimate, nativeWordEstimate,
  genericEstimate (addition work 22 per table entry, 3 per lookup, 12 word, 18 baseline).
* Configured/Plan/Estimates.lean: directByteEstimate and modelAdapterEstimate
  (zero table marshalling, three units for the word and baseline's two inputs and output).
* ExecFloat/Backends/Selection/Policy.lean and Scoring.lean: 100000 expected calls,
  32 per allocation, 64 bytes per memory block, and a one-MiB resident limit.

These are planning estimates, not benchmark timings. Optional candidates must fit the
format/carrier and policy limits; the exact baseline is always retained. Every candidate
already carries run_eq_spec. A selected word dispatcher can still fall back to the exact
reference when its operand guards decline; its certificate covers both paths.

Run from anywhere: python3 ch09_backend_ladder.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import figstyle as fs
from matplotlib.colors import to_rgba

OUT_NAME = "ch09-backend-ladder.png"
CALLS = 100_000
TABLE_ENTRIES = 2 ** (2 * (1 + 4 + 3))
TABLE_COLD = TABLE_ENTRIES * 22 + 32 + TABLE_ENTRIES // 64
SCORES = (
    ("Word", CALLS * (12 + 3)),
    ("Table", CALLS * 3 + TABLE_COLD),
    ("Baseline", CALLS * (18 + 3)),
)
assert TABLE_ENTRIES == 65_536 <= 1024 * 1024
assert TABLE_COLD == 1_442_848
assert [score for _, score in SCORES] == [1_500_000, 1_742_848, 2_100_000]
assert (TABLE_COLD + (15 - 3) - 1) // (15 - 3) == 120_238


def heading(ax, x, y, number, label):
    ax.text(x, y, f"{number}  {label}", fontsize=13, weight="bold", va="center")


def cost_rows(ax, left, right, top):
    for index, (name, score) in enumerate(SCORES):
        y = top - index * 0.38
        ax.plot([left, right], [y - 0.18, y - 0.18], color=fs.LINE, lw=0.6)
        ax.text(left, y, name, va="center", fontsize=12,
                weight="bold" if name == "Word" else "normal", color=fs.INK)
        ax.text(right, y, f"{score:,}", ha="right", va="center", fontsize=12,
                weight="bold" if name == "Word" else "normal", color=fs.INK)


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 7.3) if mobile else (9.0, 4.0)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18,
            "Choosing a proved\naddition kernel" if mobile else "Choosing a proved addition kernel",
            fontsize=14 if mobile else 16, weight="bold", va="top")
    ax.text(0.18, height - (0.91 if mobile else 0.64),
            "E4M3 (IEEE) · UInt8\nDefault: 100,000 expected calls" if mobile
            else "E4M3 (IEEE) · UInt8 carrier · Default policy: 100,000 expected calls",
            fontsize=11.5, va="top", color=fs.MUTED, linespacing=1.5)
    if mobile:
        heading(ax, 0.25, 5.53, 1, "Eligibility")
        ax.text(0.25, 5.14, "Table + word are eligible.", fontsize=12, va="center")
        ax.text(0.25, 4.80, "64 KiB table ≤ 1 MiB limit", fontsize=11.5, va="center")
        ax.text(0.25, 4.46, "Baseline is always retained.", fontsize=11.5, va="center")
        fs.arrow(ax, (1.90, 4.22), (1.90, 3.90))
        heading(ax, 0.25, 3.70, 2, "Estimated costs")
        ax.text(0.25, 3.33, "100,000 × warm + cold", fontsize=11.5, va="center")
        cost_rows(ax, 0.25, 3.55, 2.94)
        fs.arrow(ax, (1.90, 1.92), (1.90, 1.62))
        heading(ax, 0.25, 1.42, 3, "Selected implementation")
        fs.box(ax, 0.25, 0.61, 3.30, 0.58, "Word kernel", fontsize=13, weight="bold",
               facecolor=to_rgba(fs.GREEN, 0.08), edgecolor=fs.GREEN)
        ax.text(1.90, 0.29, "Every candidate proves run = spec.",
                ha="center", va="center", fontsize=11.5)
    else:
        heading(ax, 0.25, 2.82, 1, "Eligibility")
        ax.text(0.25, 2.28, "Table + word are eligible.", fontsize=11.5, va="center")
        ax.text(0.25, 1.88, "64 KiB table ≤ 1 MiB limit", fontsize=11.5, va="center")
        ax.text(0.25, 1.48, "Baseline always retained.", fontsize=11.5, va="center")
        fs.arrow(ax, (2.77, 2.03), (3.13, 2.03))
        heading(ax, 3.25, 2.82, 2, "Estimated costs")
        ax.text(3.25, 2.40, "100,000 × warm + cold", fontsize=11.5, va="center")
        cost_rows(ax, 3.25, 5.94, 2.01)
        fs.arrow(ax, (6.05, 2.03), (6.42, 2.03))
        heading(ax, 6.55, 2.82, 3, "Selected")
        fs.box(ax, 6.55, 1.65, 2.20, 0.78, "Word kernel", fontsize=13, weight="bold",
               facecolor=to_rgba(fs.GREEN, 0.08), edgecolor=fs.GREEN)
        ax.text(7.65, 1.29, "Under this policy", ha="center", va="center", fontsize=11.5)
        ax.text(4.50, 0.66, "Every candidate already proves run = spec.",
                ha="center", va="center", fontsize=12)
        ax.text(4.50, 0.24, "Scores are planning estimates; the choice depends on format, carrier and policy.",
                ha="center", va="center", fontsize=11.5, color=fs.MUTED)
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
