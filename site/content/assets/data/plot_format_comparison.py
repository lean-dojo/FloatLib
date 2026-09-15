#!/usr/bin/env python3
"""Draw chapter 15's equal-width figures from the release benchmark.

The figures compare our proved binary and posit kernels with MPFR, Berkeley SoftFloat, extracted
Flocq, Stillwater Universal, native C, and CPython through a common scalar harness. Flocq is a
precision-model comparison whose input rounding and fixture traces need not match. The data comes from
``benchmarks/results/main/release/benchmark/plots/summary.csv``. The benchmark verifier
regenerates that CSV from all nine raw trials before accepting the bundle.

The focused figures pair mul with fma and div with sqrt. The reader shows a figure at most about
900 pixels wide, where six panels leave the tick labels and legend unreadable. The six-panel
overview, format-comparison-main.png, includes addition and subtraction for readers who want
every operation on one page. A second six-panel figure stops at 16 bits. We added that view because the
full 2-to-4096-bit axis cannot label 5, 6, and 7 bits legibly, and those are real measurements
rather than decorative points we are willing to hide.

Tick policy: the full-range x axis is log base 2 and labels powers of two. Every measured point
still appears, including 3, 5, 6, and 7 bits. The low-width figure labels every point. Lines connect
the measured widths for one implementation; backend changes remain available in
``backend-regimes.csv`` instead of being stamped across the public figures.

Every string drawn on a figure is checked for em and en dashes before saving, because the site's
text checks cannot see inside a PNG.

Run from anywhere: python3 plot_format_comparison.py [--out-dir DIR]
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BENCHMARK = REPO / "benchmarks" / "results" / "main" / "release" / "benchmark"
SUMMARY = BENCHMARK / "plots" / "summary.csv"
DEFAULT_OUT_DIR = HERE.parent

OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
OPERATION_LABEL = {
    "add": "Addition",
    "sub": "Subtraction",
    "mul": "Multiplication",
    "div": "Division",
    "sqrt": "Square root",
    "fma": "Fused multiply-add",
}
PAIRS = (
    ("mul-fma", ("mul", "fma")),
    ("div-sqrt", ("div", "sqrt")),
)

# Each series has a distinct marker and line style as well as a colour. FloatLib's two curves
# are heavier, with their own legend row. Grey keeps extracted Flocq distinct from green posits.
SERIES = (
    ("ExecFloat binary proved software", "FloatLib binary (proved)",
     dict(color="#2a78d6", marker="s", linestyle="-", linewidth=2.6, markersize=7, zorder=5)),
    ("Berkeley SoftFloat IEEE software", "Berkeley SoftFloat",
     dict(color="#7c3aed", marker="v", linestyle="-.", linewidth=1.8, markersize=6, zorder=3)),
    ("MPFR (binary) software reference", "MPFR",
     dict(color="#eb6834", marker="^", linestyle=":", linewidth=1.8, markersize=6, zorder=3)),
    ("Flocq binary reference (precision model)", "extracted Flocq*",
     dict(color="#60646c", marker="D", linestyle=":", linewidth=1.8, markersize=5.5, zorder=3)),
    ("Native C IEEE FPU", "native C FPU",
     dict(color="#eda100", marker="v", linestyle="-.", linewidth=1.8, markersize=7, zorder=3)),
    ("CPython float64 runtime", "CPython float",
     dict(color="#e87ba4", marker="X", linestyle="None", linewidth=1.8, markersize=8, zorder=3)),
    ("ExecFloat Posit proved software", "FloatLib posit (proved)",
     dict(color="#008300", marker="o", linestyle="-", linewidth=2.6, markersize=7, zorder=5)),
    ("Stillwater Universal Posit (software)", "Stillwater Universal posit (software)",
     dict(color="#4a3aa7", marker="P", linestyle="--", linewidth=1.8, markersize=7, zorder=3)),
    ("Stillwater Universal Posit (hardware-assisted)",
     "Stillwater Universal posit (host sqrt)",
     dict(color="#8b5cf6", marker="P", markerfacecolor="none", linestyle=":",
          linewidth=1.8, markersize=7, zorder=3)),
)
OURS = {"ExecFloat binary proved software", "ExecFloat Posit proved software"}

XLABEL = "Encoded width (bits, log\u2082 scale)"
YLABEL = "Median latency (ns/operation, log scale)"
MEASUREMENT_NOTE = (
    "Nine trials with 5th to 95th percentile bands. Lower values are faster."
)

DASHES = {"\u2014": "em dash", "\u2013": "en dash"}


def check_no_dashes(*texts: str) -> None:
    for text in texts:
        for dash, name in DASHES.items():
            if dash in text:
                raise SystemExit(f"figure text contains an {name}: {text!r}")


def read_rows(
    path: Path,
) -> dict[tuple[str, str], list[tuple[int, float, float, float, str]]]:
    """Map each series and operation to timed points with their concrete backend."""
    table: dict[
        tuple[str, str], list[tuple[int, float, float, float, str]]
    ] = {}
    with path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            key = (row["series"], row["operation"])
            table.setdefault(key, []).append((
                int(row["totalBits"]),
                float(row["medianNanosPerOp"]),
                float(row["p05NanosPerOp"]),
                float(row["p95NanosPerOp"]),
                row["backend"],
            ))
    for rows in table.values():
        rows.sort()
    return table


def width_label(width: int) -> str:
    """Compact label for a full-range power-of-two tick."""
    return f"{width // 1024}k" if width >= 1024 else str(width)


def style_axes() -> None:
    plt.rcParams.update({
        "font.size": 11,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "grid.color": "#d9d9d6",
        "grid.linewidth": 0.6,
        "axes.edgecolor": "#8a8a86",
        "xtick.color": "#4a4a47",
        "ytick.color": "#4a4a47",
        "axes.labelcolor": "#2b2b29",
        "text.color": "#2b2b29",
    })


def draw_panel(
    ax,
    table,
    operation: str,
    *,
    max_width: int | None = None,
    label_every_width: bool = False,
    series_filter: set[str] | None = None,
) -> set[str]:
    """Draw selected points and return exactly the series represented in this panel."""
    widths: set[int] = set()
    plotted: set[str] = set()
    for series, _label, style in SERIES:
        if series_filter is not None and series not in series_filter:
            continue
        rows = table.get((series, operation))
        if not rows:
            continue
        if max_width is not None:
            rows = [row for row in rows if row[0] <= max_width]
        if not rows:
            continue
        plotted.add(series)
        widths.update(w for (w, _m, _lo, _hi, _backend) in rows)
        xs = [w for (w, _m, _lo, _hi, _backend) in rows]
        medians = [m for (_w, m, _lo, _hi, _backend) in rows]
        ax.plot(xs, medians, **style)
        lows = [lo for (_w, _m, lo, _hi, _backend) in rows]
        highs = [hi for (_w, _m, _lo, hi, _backend) in rows]
        if (
            any(lo != hi for lo, hi in zip(lows, highs))
            and style["linestyle"] != "None"
        ):
            ax.fill_between(
                xs,
                lows,
                highs,
                color=style["color"],
                alpha=0.12,
                linewidth=0,
            )
    ordered = sorted(widths)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ticks = ordered if label_every_width else [
        width
        for width in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)
        if width in widths
    ]
    labels = [str(width) for width in ticks] if label_every_width else [
        width_label(width) for width in ticks
    ]
    ax.set_xticks(ticks, labels=labels)
    ax.minorticks_off()
    ax.set_title(OPERATION_LABEL[operation], loc="left", fontsize=13)
    ax.set_xlabel(XLABEL)
    return plotted


def add_legend(fig, included: set[str], anchor_y: float, ncol: int) -> None:
    add_filtered_legend(fig, included & OURS, anchor_y=anchor_y, ncol=2, fontsize=11)
    add_filtered_legend(
        fig, included - OURS,
        anchor_y=anchor_y - 0.045, ncol=ncol,
    )


def add_filtered_legend(
    fig,
    included: set[str],
    *,
    anchor_y: float,
    ncol: int,
    label_overrides: dict[str, str] | None = None,
    fontsize: float = 10.5,
) -> None:
    handles = []
    labels = []
    names = []
    for series, label, style in SERIES:
        if series in included:
            handles.append(Line2D([], [], **style))
            labels.append(
                label_overrides.get(series, label) if label_overrides else label
            )
            names.append(series)
    legend = fig.legend(
        handles,
        labels,
        loc="upper center",
        ncol=ncol,
        frameon=False,
        bbox_to_anchor=(0.5, anchor_y),
        fontsize=fontsize,
        columnspacing=1.4,
        handlelength=2.6,
    )
    for text, series in zip(legend.get_texts(), names, strict=True):
        if series in OURS:
            text.set_fontweight("bold")


def add_figure_heading(fig, title: str, *, title_y: float = 0.985) -> None:
    fig.suptitle(title, y=title_y, fontsize=14, fontweight="bold")
    fig.text(0.5, title_y - 0.055, MEASUREMENT_NOTE, ha="center", va="top", fontsize=10.5)
    fig.text(
        0.5,
        0.015,
        "Markers are measurements. Lines connect measured widths.\n"
        "*Flocq uses different input rounding; see the performance chapter.",
        ha="center",
        va="bottom",
        fontsize=9,
        color="#4a4a47",
    )


def draw_pair(table, name: str, operations: tuple[str, str], out_dir: Path) -> Path:
    title = (
        f"FloatLib performance: {OPERATION_LABEL[operations[0]].lower()} "
        f"and {OPERATION_LABEL[operations[1]].lower()}"
    )
    texts = [title, XLABEL, YLABEL, *operations, *(label for _s, label, _st in SERIES)]
    check_no_dashes(*texts)

    fig, axes = plt.subplots(1, 2, figsize=(12, 5.6), sharey=True)
    fig.subplots_adjust(left=0.075, right=0.99, bottom=0.16, top=0.64, wspace=0.08)
    plotted: set[str] = set()
    for ax, operation in zip(axes, operations):
        plotted.update(draw_panel(ax, table, operation))
    axes[0].set_ylabel(YLABEL)
    add_legend(fig, plotted, anchor_y=0.86, ncol=4)
    add_figure_heading(fig, title)
    out = out_dir / f"format-comparison-{name}.png"
    fig.savefig(out, dpi=200)
    plt.close(fig)
    return out


def draw_overview(table, out_dir: Path) -> Path:
    title = "FloatLib arithmetic performance from 2 to 4,096 bits"
    texts = [title, XLABEL, YLABEL, *OPERATIONS, *(label for _s, label, _st in SERIES)]
    check_no_dashes(*texts)

    fig, axes = plt.subplots(2, 3, figsize=(15.5, 10.0), sharey=True)
    fig.subplots_adjust(left=0.06, right=0.99, bottom=0.12, top=0.735, wspace=0.08, hspace=0.38)
    plotted: set[str] = set()
    for ax, operation in zip(axes.flat, OPERATIONS):
        plotted.update(draw_panel(ax, table, operation))
    for ax in axes[:, 0]:
        ax.set_ylabel(YLABEL)
    add_legend(fig, plotted, anchor_y=0.875, ncol=4)
    add_figure_heading(fig, title)
    out = out_dir / "format-comparison-main.png"
    fig.savefig(out, dpi=200)
    plt.close(fig)
    return out


def draw_low_width(table, out_dir: Path) -> Path:
    """Show every measured low-width tick that the full-range plot cannot label."""
    included = {
        "ExecFloat binary proved software",
        "ExecFloat Posit proved software",
        "MPFR (binary) software reference",
        "Flocq binary reference (precision model)",
        "Stillwater Universal Posit (software)",
        "Stillwater Universal Posit (hardware-assisted)",
    }
    title = "FloatLib low-width performance from 2 to 16 bits"
    texts = [
        title,
        XLABEL,
        YLABEL,
        *OPERATIONS,
        *(label for series, label, _style in SERIES if series in included),
    ]
    check_no_dashes(*texts)

    fig, axes = plt.subplots(2, 3, figsize=(15.5, 9.4), sharey=True)
    fig.subplots_adjust(
        left=0.06,
        right=0.99,
        bottom=0.11,
        top=0.70,
        wspace=0.08,
        hspace=0.42,
    )
    plotted: set[str] = set()
    for ax, operation in zip(axes.flat, OPERATIONS, strict=True):
        plotted.update(draw_panel(
            ax,
            table,
            operation,
            max_width=16,
            label_every_width=True,
            series_filter=included,
        ))
    for ax in axes[:, 0]:
        ax.set_ylabel(YLABEL)
    add_filtered_legend(
        fig,
        plotted,
        anchor_y=0.84,
        ncol=6,
        fontsize=9.5,
        label_overrides={
            "ExecFloat binary proved software": "FloatLib binary",
            "ExecFloat Posit proved software": "FloatLib posit",
            "MPFR (binary) software reference": "MPFR",
            "Flocq binary reference (precision model)": "extracted Flocq*",
            "Stillwater Universal Posit (software)": "Stillwater posit",
            "Stillwater Universal Posit (hardware-assisted)":
                "Stillwater posit (host sqrt)",
        },
    )
    add_figure_heading(fig, title)
    out = out_dir / "format-comparison-low-width.png"
    fig.savefig(out, dpi=200)
    plt.close(fig)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    table = read_rows(SUMMARY)
    style_axes()
    for name, operations in PAIRS:
        print(f"wrote {draw_pair(table, name, operations, args.out_dir)}")
    print(f"wrote {draw_overview(table, args.out_dir)}")
    print(f"wrote {draw_low_width(table, args.out_dir)}")


if __name__ == "__main__":
    main()
