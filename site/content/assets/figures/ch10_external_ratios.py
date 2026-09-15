#!/usr/bin/env python3
"""Draw FloatLib median time divided by each external lane at equal encoded width.

We keep this as a derived view rather than a second benchmark. Every point comes from the ratio
table generated beside the retained release campaign. A value above one means FloatLib took
longer; a value below one means it took less time.

Source: benchmarks/results/main/release/benchmark/plots/ratios.csv. The benchmark runner creates
that file from the same nine-trial summary used by the headline plot. The adjacent metadata.txt
and environment/lscpu.txt supply the host in the footer. Stillwater's software and
hardware-assisted configurations stay separate because they are different implementations. A
series with no points for the three operations in this figure is omitted instead of being shown
as an empty legend entry.

Run from anywhere: python3 ch10_external_ratios.py [--out PNG]
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.lines import Line2D  # noqa: E402

RATIOS = (fs.REPO / "benchmarks" / "results" / "main" / "release" / "benchmark" / "plots" /
          "ratios.csv")
OUT_NAME = "ch10-external-ratios.png"

OPERATIONS = ("add", "mul", "div")

# Keep Flocq grey, distinct from the green FloatLib posit curve in the other figures.
SERIES = (
    ("binarySoftwareOverMPFRBinaryCompanion", "FloatLib binary / MPFR",
     dict(color=fs.ORANGE, marker="^", linestyle=":", markersize=6)),
    ("binarySoftwareOverFlocq", "FloatLib binary / extracted Flocq*",
     dict(color="#60646c", marker="D", linestyle="-.", markersize=5)),
    ("execPositOverUniversalSoftware", "FloatLib posit / Universal software",
     dict(color=fs.PURPLE, marker="P", linestyle="--", markersize=6.5)),
    ("execPositOverUniversalHardwareAssisted",
     "FloatLib posit / Universal hardware-assisted",
     dict(color=fs.SKY, marker="X", linestyle="-", markersize=6)),
)

TITLE = "FloatLib time / external implementation time"
XLABEL = "encoded width (bits)"
YLABEL = "ratio of medians (log scale)"
EQUAL = "equal time"


def read_ratios() -> dict[tuple[str, str], list[tuple[int, float]]]:
    """Map (column, operation) to (width, ratio) pairs sorted by width, empty cells skipped."""
    table: dict[tuple[str, str], list[tuple[int, float]]] = {}
    with RATIOS.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            for column, _label, _style in SERIES:
                value = row[column]
                if value:
                    table.setdefault((column, row["operation"]), []).append(
                        (int(row["totalBits"]), float(value)))
    for points in table.values():
        points.sort()
    return table


def width_labels(widths: list[int]) -> list[str]:
    """Tick labels; 5, 6 and 7 bits keep their tick without a label, and the remaining labels
    alternate between two rows so that 128, 256 and 512 do not run together in a narrow panel."""
    labels = []
    row = 0
    for width in widths:
        if width in (5, 6, 7):
            labels.append("")
            continue
        text = f"{width // 1024}k" if width >= 1024 else str(width)
        labels.append(text if row % 2 == 0 else "\n" + text)
        row += 1
    return labels


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    table = read_ratios()

    fig, axes = fs.figure(4.7, ncols=3, sharey=True)
    fig.subplots_adjust(left=0.075, right=0.99, bottom=0.27, top=0.70, wspace=0.08)

    for ax, op in zip(axes, OPERATIONS):
        widths: set[int] = set()
        for column, _label, style in SERIES:
            points = table.get((column, op), [])
            if not points:
                continue
            widths.update(w for w, _ in points)
            ax.plot([w for w, _ in points], [r for _, r in points], **style)
        ax.axhline(1.0, color=fs.INK, linewidth=0.9, zorder=1)
        ordered = sorted(widths)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        ax.set_xticks(ordered, labels=width_labels(ordered))
        ax.minorticks_off()
        ax.set_title(op, loc="left")
        ax.set_xlabel(XLABEL)
    axes[0].set_ylabel(YLABEL)
    axes[0].annotate(EQUAL, (4096, 1.0), textcoords="offset points", xytext=(0, 4), ha="right",
                     va="bottom", fontsize=9, color=fs.MUTED)

    handles = [
        Line2D([], [], label=label, **style)
        for column, label, style in SERIES
        if any(table.get((column, op)) for op in OPERATIONS)
    ]
    fig.legend(handles=handles, loc="upper center", ncol=2, bbox_to_anchor=(0.5, 0.895),
               columnspacing=1.4, handlelength=2.6)
    fig.suptitle(TITLE, y=0.985, fontsize=11)
    metadata = dict(line.split("=", 1) for line in
                    (RATIOS.parent.parent / "metadata.txt").read_text().splitlines()
                    if "=" in line)
    host = next(line.split(":", 1)[1].strip() for line in
                (RATIOS.parent.parent / "environment/lscpu.txt").read_text().splitlines()
                if line.startswith("Model name:"))
    fig.text(0.5, 0.065,
             f"{host} · CPU {metadata['benchmarkCPU']}\n"
             f"{metadata['runs']} trials · above 1: FloatLib took longer · equal encoded widths\n"
             "*Flocq uses different input rounding; see the performance chapter.",
             ha="center", va="center", fontsize=8.5, color=fs.MUTED)

    target = fs.save(fig, OUT_NAME, out=args.out)
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
