#!/usr/bin/env python3
"""Draw the host FPU beside FloatLib's proved binary32 and binary64 kernels.

This figure compares the implementations at the IEEE widths where the host FPU exists.
Both use the same method of choosing the next input from the previous result, so the
comparison includes the same loop, call, input-selection, and checksum work.

Sources:

* benchmarks/results/main/release/benchmark/plots/summary.csv;
* benchmarks/results/main/release/benchmark/plots/ratios.csv.

The benchmark's metadata.txt and environment/lscpu.txt supply the trial count
and host model in the footer. The script checks that every printed ratio agrees with the two
medians it stands above.

Run from anywhere: python3 ch17_host_vs_software.py [--out PNG]
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.patches import Patch  # noqa: E402

sys.path.insert(0, str(fs.REPO / "benchmarks" / "plots"))
from format_comparison import (  # noqa: E402
    OPERATION_LABEL, compact_operation_layout, save_operation_svg, write_operation_series,
)

PLOTS = fs.REPO / "benchmarks" / "results" / "main" / "release" / "benchmark" / "plots"
SUMMARY = PLOTS / "summary.csv"
RATIOS = PLOTS / "ratios.csv"
OUT_NAME = "ch17-host-vs-software.png"

HOST = "Native C IEEE FPU"
OURS = "ExecFloat binary proved software"
OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
PANELS = ((32, "binary32"), (64, "binary64"))

HOST_STYLE = dict(facecolor=fs.ORANGE, hatch="////", edgecolor=fs.INK, linewidth=0.6)
OURS_STYLE = dict(facecolor=fs.BLUE, edgecolor=fs.INK, linewidth=0.6)
BAR_WIDTH = 0.38

TITLE = "Native C and FloatLib proved software"
LEGEND_HOST = "native C float / double"
LEGEND_OURS = "FloatLib binary"
YLABEL = "median time (ns/op, log scale)"
RATIO_NOTE = "Ratios: FloatLib median / native C median. Lower time is faster."


def medians() -> dict[tuple[str, int, str], float]:
    table: dict[tuple[str, int, str], float] = {}
    with SUMMARY.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["series"] in (HOST, OURS) and row["totalBits"] in ("32", "64"):
                key = (row["series"], int(row["totalBits"]), row["operation"])
                table[key] = float(row["medianNanosPerOp"])
    return table


def ratios() -> dict[tuple[int, str], float]:
    table: dict[tuple[int, str], float] = {}
    with RATIOS.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            value = row["binarySoftwareOverNativeFPU"]
            if value:
                table[(int(row["totalBits"]), row["operation"])] = float(value)
    return table


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    med = medians()
    rat = ratios()

    fig, axes = fs.figure(5.2, ncols=2, sharey=True)
    fig.subplots_adjust(left=0.085, right=0.99, bottom=0.17, top=0.75, wspace=0.06)

    xs = list(range(len(OPERATIONS)))
    for ax, (width, panel_title) in zip(axes, PANELS):
        host_values = [med[(HOST, width, op)] for op in OPERATIONS]
        ours_values = [med[(OURS, width, op)] for op in OPERATIONS]
        ax.bar([x - BAR_WIDTH / 2 for x in xs], host_values, width=BAR_WIDTH, **HOST_STYLE)
        ax.bar([x + BAR_WIDTH / 2 for x in xs], ours_values, width=BAR_WIDTH, **OURS_STYLE)
        ax.set_yscale("log")
        # Reserve a row above the tallest bar for every ratio. Placing labels at a multiple
        # of each bar's height previously clipped the three largest binary64 ratios.
        ax.set_ylim(6, max(med.values()) * 5)
        ax.set_xticks(xs, labels=OPERATIONS)
        ax.set_title(panel_title, loc="left")
        ax.grid(False, axis="x")
        for x, op, host, ours in zip(xs, OPERATIONS, host_values, ours_values):
            ratio = rat[(width, op)]
            quotient = ours / host
            if abs(ratio - quotient) / quotient > 0.005:
                raise SystemExit(f"ratios.csv disagrees with summary.csv at {width} {op}: "
                                 f"{ratio} vs {quotient}")
            ax.text(x, 0.93, f"{ratio:.1f}×", transform=ax.get_xaxis_transform(),
                    ha="center", va="center", fontsize=9, color=fs.INK, fontweight="bold")
    axes[0].set_ylabel(YLABEL)

    handles = [Patch(label=LEGEND_HOST, **HOST_STYLE), Patch(label=LEGEND_OURS, **OURS_STYLE)]
    fig.legend(handles=handles, loc="upper center", ncol=2, bbox_to_anchor=(0.5, 0.915),
               handlelength=1.6)
    fig.suptitle(TITLE, y=0.985, fontsize=11)
    fig.text(0.5, 0.835, RATIO_NOTE, ha="center", va="center", fontsize=9, color=fs.MUTED)
    metadata = dict(line.split("=", 1) for line in
                    (PLOTS.parent / "metadata.txt").read_text().splitlines() if "=" in line)
    host = next(line.split(":", 1)[1].strip() for line in
                (PLOTS.parent / "environment/lscpu.txt").read_text().splitlines()
                if line.startswith("Model name:"))
    fig.text(0.5, 0.055,
             f"{host}\n"
             f"{metadata['runs']} trials · times include input selection and checksums",
             ha="center", va="center", fontsize=8.5, color=fs.MUTED)

    target = fs.save(fig, OUT_NAME, out=args.out)
    descriptions = {}
    for operation in OPERATIONS:
        single, ax = fs.plt.subplots()
        xs = list(range(len(PANELS)))
        ax.bar(
            [x - BAR_WIDTH / 2 for x in xs],
            [med[(HOST, width, operation)] for width, _label in PANELS],
            width=BAR_WIDTH, **HOST_STYLE,
        )
        ax.bar(
            [x + BAR_WIDTH / 2 for x in xs],
            [med[(OURS, width, operation)] for width, _label in PANELS],
            width=BAR_WIDTH, **OURS_STYLE,
        )
        ax.set_yscale("log")
        ax.set_ylim(6, max(med.values()) * 5)
        ax.set_xticks(xs, labels=[label for _width, label in PANELS])
        ax.set_xlabel("IEEE format")
        ax.set_ylabel("Median time (ns/op, log scale)")
        ax.grid(False, axis="x")
        for x, (width, _label) in zip(xs, PANELS):
            ax.text(
                x, 0.93, f"{rat[(width, operation)]:.1f}×",
                transform=ax.get_xaxis_transform(),
                ha="center", va="center", fontsize=11, color=fs.INK, fontweight="bold",
            )
        compact_operation_layout(
            single, ax, title=OPERATION_LABEL[operation],
            context="Native C and FloatLib binary kernels",
            handles=handles, labels=[LEGEND_HOST, LEGEND_OURS],
            bold_labels={LEGEND_OURS},
            notes=(
                "Labels: FloatLib / native C median time. Lower time is faster.",
                f"{metadata['runs']} trials; same input-selection and checksum harness.",
                f"{host.replace('(R)', '')}.",
            ),
        )
        fs.check_no_dashes(single)
        save_operation_svg(single, target, operation)
        descriptions[operation] = (
            f"{OPERATION_LABEL[operation]}: native C and FloatLib binary32 and binary64 "
            "median times in nanoseconds per operation on a logarithmic vertical axis. "
            "Paired bars show absolute times; labels show FloatLib median / native C median. "
            f"{metadata['runs']} trials in the same input-selection and checksum harness."
        )
    write_operation_series(
        target, descriptions,
        overview_alt="Six operations for binary32 and binary64: paired native C and FloatLib "
        "bars show median nanoseconds per operation on logarithmic vertical axes. "
        "One label per pair gives FloatLib median / native C median. "
        f"{metadata['runs']} trials, with input selection and checksums included.",
    )
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
