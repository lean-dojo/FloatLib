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

sys.path.insert(0, str(fs.REPO / "benchmarks" / "plots"))
from format_comparison import (  # noqa: E402
    OPERATION_LABEL, compact_operation_layout, save_operation_svg, write_operation_series,
)

RATIOS = (fs.REPO / "benchmarks" / "results" / "main" / "release" / "benchmark" / "plots" /
          "ratios.csv")
OUT_NAME = "ch10-external-ratios.png"

OPERATIONS = ("add", "mul", "div")

# Flocq's matched measurements use a separate campaign and figure.
SERIES = (
    ("binarySoftwareOverMPFRBinaryCompanion", "FloatLib binary / MPFR",
     dict(color=fs.ORANGE, marker="^", linestyle=":", markersize=6)),
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

    def draw_panel(ax, op):
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

    for ax, op in zip(axes, OPERATIONS):
        draw_panel(ax, op)
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
             f"{metadata['runs']} trials · above 1: FloatLib took longer · equal encoded widths",
             ha="center", va="center", fontsize=8.5, color=fs.MUTED)

    limits = {op: (ax.get_xlim(), ax.get_ylim()) for op, ax in zip(OPERATIONS, axes)}
    target = fs.save(fig, OUT_NAME, out=args.out)
    descriptions = {}
    for operation in OPERATIONS:
        single, ax = fs.plt.subplots()
        draw_panel(ax, operation)
        ax.set_xlim(limits[operation][0])
        ax.set_ylim(limits[operation][1])
        ax.set_xlabel("Encoded width (bits, log₂ scale)")
        ax.set_ylabel("Ratio of medians (log scale)")
        ax.annotate(
            "1 = equal time", (1, 1.0), xycoords=("axes fraction", "data"),
            textcoords="offset points", xytext=(-3, 5), ha="right", va="bottom",
            fontsize=11, color=fs.INK,
            bbox=dict(facecolor="white", edgecolor="none", alpha=0.9, pad=1),
        )
        selected = [(column, label, style) for column, label, style in SERIES
                    if table.get((column, operation))]
        compact_operation_layout(
            single, ax, title=OPERATION_LABEL[operation],
            context="FloatLib time / external time",
            handles=[Line2D([], [], **style) for _column, _label, style in selected],
            labels=[label for _column, label, _style in selected],
            notes=(
                f"Ratio of {metadata['runs']}-trial medians. Above 1: FloatLib took longer.",
                "Equal encoded widths; different format contracts.",
                f"{host.replace('(R)', '')}; CPU {metadata['benchmarkCPU']}.",
            ),
        )
        fs.check_no_dashes(single)
        save_operation_svg(single, target, operation)
        descriptions[operation] = (
            f"{OPERATION_LABEL[operation]}: FloatLib median time divided by the external "
            "implementation's median time against equal encoded width, on logarithmic axes. "
            "The horizontal line at 1 means equal time; above 1 means FloatLib took longer. "
            "Series: " + "; ".join(label for _column, label, _style in selected)
            + f". Ratios of {metadata['runs']}-trial medians."
        )
    write_operation_series(
        target, descriptions,
        overview_alt="Addition, multiplication, and division: FloatLib median time divided "
        "by MPFR for binary arithmetic and by Stillwater Universal for posit arithmetic "
        "at equal encoded widths, on logarithmic axes. A ratio of 1 means equal time; "
        "above 1 means FloatLib took longer.",
    )
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
