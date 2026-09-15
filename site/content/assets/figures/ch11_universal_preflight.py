#!/usr/bin/env python3
"""Draw the Stillwater Universal comparisons made before timing.

The benchmark times a Universal operation at a given width only after its outputs agree with
FloatLib on every benchmark input. This figure reads those comparison results directly.

Source:
benchmarks/results/main/release/benchmark/environment/external-posit-conformance.csv.

Run from anywhere: python3 ch11_universal_preflight.py [--out PNG]
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.patches import Patch, Rectangle  # noqa: E402

PREFLIGHT = (fs.REPO / "benchmarks" / "results" / "main" / "release" / "benchmark" /
             "environment" / "external-posit-conformance.csv")
METADATA = (fs.REPO / "benchmarks" / "results" / "main" / "release" / "benchmark" /
            "metadata.txt")
OUT_NAME = "ch11-universal-preflight.png"

OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")

PASS_STYLE = dict(facecolor=fs.BLUE, edgecolor="white", linewidth=1.5)
REJECT_STYLE = dict(facecolor="white", edgecolor=fs.VERMILION, hatch="xxx", linewidth=1.2)
MISSING_STYLE = dict(facecolor=fs.LINE, edgecolor="white", linewidth=1.5)

XLABEL = "posit width (bits)"


def read_cells() -> dict[tuple[int, str], str]:
    """Map each (width, operation) pair to its comparison result."""
    cells: dict[tuple[int, str], str] = {}
    with PREFLIGHT.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            key = (int(row["totalBits"]), row["operation"])
            if key in cells:
                raise SystemExit(f"duplicate preflight cell {key}")
            status = row["status"]
            if status not in {"pass", "reject"}:
                raise SystemExit(f"unknown preflight status at {key}: {status}")
            cells[key] = status
    return cells


def planned_widths() -> list[int]:
    for line in METADATA.read_text(encoding="utf-8").splitlines():
        if line.startswith("widths="):
            widths = [int(value) for value in line.removeprefix("widths=").split()]
            return [width for width in widths if width >= 5 and width not in {24, 48}]
    raise SystemExit(f"missing widths entry in {METADATA}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    cells = read_cells()
    widths = planned_widths()
    expected = {(width, operation) for width in widths for operation in OPERATIONS}
    actual = set(cells)
    if actual != expected:
        raise SystemExit(
            "Universal preflight grid differs: "
            f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
        )
    total = len(expected)
    passed = sum(1 for status in cells.values() if status == "pass")
    rejected = total - passed

    fig, ax = fs.figure(4.1)
    fig.subplots_adjust(left=0.07, right=0.90, bottom=0.14, top=0.68)
    ax.grid(False)
    for spine in ax.spines.values():
        spine.set_visible(False)

    n_cols = len(widths)
    n_rows = len(OPERATIONS)
    for col, width in enumerate(widths):
        for row, op in enumerate(OPERATIONS):
            status = cells[(width, op)]
            style = PASS_STYLE if status == "pass" else REJECT_STYLE
            ax.add_patch(Rectangle((col, n_rows - 1 - row), 1, 1, **style))
    for row, op in enumerate(OPERATIONS):
        row_total = len(widths)
        row_pass = sum(1 for w in widths if cells.get((w, op)) == "pass")
        ax.text(n_cols + 0.25, n_rows - 1 - row + 0.5, f"{row_pass} of {row_total}",
                ha="left", va="center", fontsize=9, color=fs.INK)

    ax.set_xlim(0, n_cols)
    ax.set_ylim(0, n_rows)
    ax.set_aspect("equal")
    ax.set_xticks([i + 0.5 for i in range(n_cols)], labels=[str(w) for w in widths])
    ax.set_yticks([n_rows - 1 - i + 0.5 for i in range(n_rows)], labels=OPERATIONS)
    ax.tick_params(length=0)
    ax.set_xlabel(XLABEL)

    handles = [
        Patch(label=f"All 16 inputs agree ({passed})", **PASS_STYLE),
        Patch(label=f"Excluded from timings ({rejected})",
              **REJECT_STYLE),
    ]
    fig.legend(handles=handles, loc="upper center", ncol=2, bbox_to_anchor=(0.5, 0.93),
               handlelength=1.6)
    fig.suptitle(f"Checking Universal before timing: {passed} of {total} comparisons matched",
                 y=0.99, fontsize=11)

    target = fs.save(fig, OUT_NAME, out=args.out)
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
