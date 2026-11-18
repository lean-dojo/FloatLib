#!/usr/bin/env python3
"""Draw the planner's estimated cost of three implementations of one configured addition.

One bar per eligible implementation, with its estimate written at the end; the lowest estimate
is the selected implementation. The eligibility rules and the policy are stated in the caption.

The example is ExecFloat.Binary 4 3 (an IEEE encoding with infinities), using UInt8 storage and
Policy.default. Numerical inputs come from:

* Descriptor/Plan/Estimates.lean: tableGenerationCost, tableEstimate, nativeWordEstimate,
  genericEstimate (addition work 22 per table entry, 3 per lookup, 12 word, 18 baseline).
* Configured/Plan/Estimates.lean: directByteEstimate and modelAdapterEstimate
  (zero table marshalling, three units for the word and baseline's two inputs and output).
* ExecFloat/Backends/Compiled/Selection/Policy.lean and Scoring.lean: 100000 expected calls,
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
from matplotlib.patches import Patch

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


LABELS = {"Word": "word kernel", "Table": "table", "Baseline": "baseline"}


def build_figure(mobile: bool = False):
    """The planner's three estimates as bars; the lowest is the selected implementation."""
    fs.setup()
    width, height = (fs.MOBILE_WIDTH, 2.9) if mobile else (fs.WIDTH, 2.4)
    fig, ax = fs.plt.subplots(figsize=(width, height))
    names = [LABELS[name] for name, _ in SCORES]
    scores = [score for _, score in SCORES]
    best = min(scores)
    assert scores[0] == best and scores.count(best) == 1
    positions = range(len(SCORES))
    selected = dict(facecolor=fs.ROLE["main"], edgecolor=fs.ROLE["main"])
    other = dict(facecolor="white", edgecolor=fs.ROLE["main"], hatch="///")
    for position, score in zip(positions, scores):
        ax.barh(position, score, height=0.5, linewidth=fs.LW_AXIS,
                **(selected if score == best else other))
        ax.text(score + 30_000, position, f"{score:,}", va="center", ha="left",
                fontsize=fs.SIZE_TICK)
    ax.set_yticks(list(positions), labels=names)
    ax.invert_yaxis()
    ax.tick_params(axis="y", length=0)
    ax.set_xlim(0, 3_150_000 if mobile else 2_600_000)
    ticks = [0, 2_000_000] if mobile else [0, 1_000_000, 2_000_000]
    ax.set_xticks(ticks, labels=[f"{tick:,}" for tick in ticks])
    ax.set_xlabel("estimated cost (planner units)")
    fs.value_grid(ax, "x")
    handles = [Patch(label="selected", linewidth=fs.LW_AXIS, **selected),
               Patch(label="not selected", linewidth=fs.LW_AXIS, **other)]
    fs.legend(fig, handles=handles, loc="lower center", bbox_to_anchor=(0.5, 0.0), ncols=2)
    fig.tight_layout(rect=(0, 0.12, 1, 1))
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
