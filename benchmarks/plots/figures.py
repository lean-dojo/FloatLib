#!/usr/bin/env python3
"""Every figure of FloatLib's speed work and of its standard benchmark suites, in one style.

    figures.py time RAW [--jobs 8] [--threads 24] [--only SECTION ...]
    figures.py install RAW
    figures.py draw [--only NAME ...]
    figures.py list

This file draws. Two modules next to it do the rest: `timing.py` starts the measurements and
`results.py` turns their logs into the result files.

`time` is the timing mode. It measures this checkout: it runs every benchmark runner whose
times a figure draws (`timing.py` lists them), the kernel sections one at a time and the others
after them at most `--jobs` at a time, with logs in RAW, a directory outside the checkout. Then it does what `install` and `draw` do. The measurement
record names the commit when a remote branch of the checkout has it and the tracked files are
unchanged; a commit that only this checkout has is not named, since nobody else could look it
up. A full run takes about as long as its longest section, the formats of 1,024 and 4,096 bits
(`timing.ROW_SECONDS`, `timing.FUNCTION_ROW_SECONDS`): two to three hours with 24 threads. The library has to be built already (`FLOATLIB_BUILD_DIR`, or `.lake/build` in the
checkout); the timing mode links the benchmark executables it starts and builds nothing else.

`install` turns the logs of a timing run into the result files under `benchmarks/results/`
(the tables and CSV files the runners' own table scripts write, and `figures/measured.json`,
which records the commit, the toolchain, the machine, the date and the exit code and time of
every section). A section that failed keeps the files of the run before it.

`draw` draws every figure from the result files, and writes for each figure NAME

    benchmarks/results/figures/NAME.png   for the site (9 inches wide at 200 dpi, white background)
    benchmarks/results/figures/NAME.pdf   vector, for papers
    benchmarks/results/figures/NAME.csv   the numbers that are drawn, one row per mark

and `benchmarks/results/FIGURES.md`: the figures numbered Figure 1, Figure 2, ..., each with
its files, its alt text, its caption (what it shows, what was measured and in which unit, the
scales, the machine and the toolchain), notes (how it was measured, where a recorded
number comes from, which numbers come from Lean and which from scripts), its CSV columns and
its inputs. It also writes the section `Figures` of the result READMEs that have figures, each
numbered from Figure 1. A figure whose input does not exist is skipped and listed, never drawn
from invented numbers.

What the timing mode does not measure, and where it comes from (`benchmarks/results/figures/
recorded/`, each file with its own provenance columns or README entry):

  * Coq 8.20.1 with Flocq 4.2.2: recorded once in a container; these times do not depend on
    FloatLib's commit.
  * Counts of the standard suites (bounds, vectors matched, proofs accepted) and of the
    interval corpora: correctness results, run once.

Style: the figure rules of the library, which hold for the guide's figures as well.

  * Inside an image there is only the plot: axes that name a quantity and its unit, tick labels,
    a legend with short series names, and for several panels a letter and a short panel title.
    No title, note, sentence, commit, toolchain or file name is drawn; `check_rules` refuses to
    save a figure that has one. Measurement details are in the caption and result files.
  * The look is the guide's `site/content/assets/figures/figstyle.py`: its fonts and sizes, its
    width (9 inches at 200 dpi), its Okabe and Ito colours and its saving routine.
  * Colour follows the library, never the figure, and a marker or a line style carries the
    same identity. The map is the guide's (`figstyle.SERIES`, where that module has it):
        FloatLib                                      blue       solid, filled circle
        FloatLib, the term as written                 blue       dashed, open circle
        Coq + Flocq, vm_compute                       vermilion  solid, square
        Coq + Flocq, lazy or conversion               orange     dashed, triangle
        MPFR                                          green      solid, diamond
        Berkeley SoftFloat                            purple     solid, inverted triangle
        anything else, named in the legend            two greys
  * A time axis is logarithmic when the data spans more than a decade and a half, and its ticks
    are plain numbers in the unit of its label. No second y axis, a light grid on the value axis
    only.
"""
from __future__ import annotations

import argparse
import csv
import datetime
import inspect
import json
import math
import re
import shutil
import statistics
import subprocess
import sys
import time
from collections import Counter, OrderedDict, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import timing  # noqa: E402
from results import (  # noqa: E402
    BASIC, EXTRAS, install, LOOPS, machine, MEASURED, Missing,
    need, number, OUT, positive, read_csv, REAL_FUNCTIONS, record_run,
    commit_of, RECORDED, relative, RESULTS, ROOT)

sys.path.insert(0, str(ROOT / "site" / "content" / "assets" / "figures"))
import figstyle  # noqa: E402  (the guide's shared style; this script only reads it)

import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402
from matplotlib.ticker import FixedLocator, FuncFormatter, MaxNLocator, NullFormatter, NullLocator  # noqa: E402

# ---- style ----------------------------------------------------------------------------------

BLUE, VERMILION, ORANGE, GREEN, PURPLE = (
    figstyle.BLUE, figstyle.VERMILION, figstyle.ORANGE, figstyle.GREEN, figstyle.PURPLE)
INK, MUTED = figstyle.INK, figstyle.MUTED
GREY_DARK, GREY_LIGHT, GREY_PALE = "#595959", "#999999", "#e6e6e6"
WIDTH = figstyle.WIDTH

# The short names of the series, as the legends print them.
NOW = "FloatLib"
COQ_NAME = "Coq 8.20.1 + Flocq 4.2.2"
MPFR_NAME, SOFTFLOAT_NAME = "MPFR", "SoftFloat"

# The series of these figures. The guide's map (`figstyle.SERIES`) decides the colour, marker and
# line style of every library it names, so that a library looks the same in every figure the
# library ships; `shared` is the name of a series there. The values here are the same map, for a
# `figstyle` that does not have it, and the series that only these figures have.
SERIES = {
    "now": dict(shared="FloatLib", color=BLUE, marker="o", ls="-", fill=True),
    "written": dict(color=BLUE, marker="o", ls="--", fill=False),
    "coq_vm": dict(shared="Flocq", color=VERMILION, marker="s", ls="-", fill=True),
    "coq_lazy": dict(shared="Flocq lazy", color=ORANGE, marker="^", ls="--", fill=True),
    "mpfr": dict(shared="MPFR", color=GREEN, marker="D", ls="-", fill=True),
    "softfloat": dict(shared="SoftFloat", color=PURPLE, marker="v", ls="-", fill=True),
    "other": dict(color=GREY_DARK, marker="X", ls=":", fill=True),
    "other2": dict(color=GREY_LIGHT, marker="P", ls=":", fill=True),
}


def setup() -> None:
    """The guide's rcParams, and what a vector file for a paper needs on top of them."""
    figstyle.setup()
    plt.rcParams.update({"pdf.fonttype": 42, "axes.titleweight": "normal"})


def small() -> float:
    """The size of the numbers drawn on bars: the guide's size for dense marks."""
    return float(getattr(figstyle, "SIZE_SMALL", plt.rcParams["xtick.labelsize"] - 1))


def spec(key: str) -> dict:
    """Colour, marker, line style and fill of a series, from the guide's map where it has it."""
    s = dict(SERIES[key])
    shared = getattr(figstyle, "SERIES", {}).get(s.pop("shared", None))
    if shared:
        s.update(color=shared["color"], marker=shared["marker"], ls=shared["linestyle"],
                 fill=shared.get("markerfacecolor", shared["color"]) != "white")
    elif key == "written":                    # the same library as `now`, drawn open and dashed
        s["color"] = spec("now")["color"]
    return s


def colour(key: str) -> str:
    return spec(key)["color"]


def style(key: str) -> dict:
    """Keyword arguments for `Axes.plot`, as `figstyle.series` gives them: an open marker is
    white inside, and nothing else is set on a marker."""
    s = spec(key)
    look = dict(color=s["color"], marker=s["marker"], linestyle=s["ls"])
    if not s["fill"]:
        look.update(markerfacecolor="white", markeredgewidth=1.3)
    return look


def handle(key: str, label: str, line: bool = True) -> Line2D:
    s = style(key)
    if not line:
        s["linestyle"] = "none"
    return Line2D([], [], label=label, **s)


def plain(value: float) -> str:
    """A tick or value label: 0.05, 1.5, 12, 1,200."""
    if value == 0:
        return "0"
    if abs(value) >= 100:
        return f"{value:,.0f}"
    if abs(value) >= 10:
        return f"{value:,.0f}" if float(value).is_integer() else f"{value:,.1f}"
    if abs(value) >= 1:
        return f"{value:.0f}" if float(value).is_integer() else f"{value:.1f}"
    return f"{value:.3g}"


TIME_UNITS = [(1e-9, "ns"), (1e-6, "µs"), (1e-3, "ms"), (1.0, "s")]


def log_ticks(axis, which: str, value=lambda v: v, long: float = 1e6) -> None:
    """Labelled ticks at every decade of a logarithmic axis, or at 1, 2 and 5 when the data
    covers less than two decades. `value` turns a tick into the number its label prints; an
    axis that spans `long` or more prints its decades as powers of ten."""
    target = axis.yaxis if which == "y" else axis.xaxis
    low, high = sorted(axis.get_ylim() if which == "y" else axis.get_xlim())
    if low <= 0:
        return
    if high / low >= long:
        label = lambda v: f"$10^{{{round(math.log10(value(v)))}}}$"
    else:
        label = lambda v: plain(float(f"{value(v):.6g}"))
    steps = (1, 2, 5) if high / low < 100 else (1,)
    ticks = [m * 10.0 ** e for e in range(math.floor(math.log10(low)) - 1, math.ceil(math.log10(high)) + 1)
             for m in steps]
    ticks = [t for t in ticks if low * 0.999 <= t <= high * 1.001]
    if len(ticks) >= 2:
        target.set_major_locator(FixedLocator(ticks))
    target.set_minor_locator(NullLocator())
    target.set_major_formatter(FuncFormatter(lambda v, _: label(v)))
    target.set_minor_formatter(NullFormatter())


def log_axis(axis, which: str = "y") -> None:
    """A logarithmic axis of plain numbers (a ratio or a count)."""
    (axis.set_yscale if which == "y" else axis.set_xscale)("log")
    log_ticks(axis, which, long=1e5)


def time_axis(axes, which: str = "y", base: float = 1e-6) -> str:
    """Make the time axis of every axes in `axes` logarithmic and label its ticks in one unit.

    The data is in units of `base` seconds. The unit is the largest one that is at most the
    geometric middle of the joint range, so the tick labels stay short; its name is returned,
    for the axis label ("time per operation (µs)").
    """
    axes = list(axes)
    for axis in axes:
        (axis.set_yscale if which == "y" else axis.set_xscale)("log")
    limits = [sorted(axis.get_ylim() if which == "y" else axis.get_xlim()) for axis in axes]
    low, high = min(l for l, _ in limits), max(h for _, h in limits)
    middle = math.sqrt(low * high) * base if low > 0 else high * base
    scale, unit = next(((s, u) for s, u in reversed(TIME_UNITS) if middle >= s), TIME_UNITS[0])
    for axis in axes:
        log_ticks(axis, which, lambda v: v * base / scale)
    return unit


def count_axis(axis, which: str = "x", ticks: int = 5) -> None:
    """A linear axis of counts: whole numbers with thousands separators, at most `ticks` intervals."""
    target = axis.xaxis if which == "x" else axis.yaxis
    target.set_major_locator(MaxNLocator(nbins=ticks, integer=True))
    target.set_major_formatter(FuncFormatter(lambda v, _: f"{v:,.0f}"))


def spans_decades(values, factor: float = 30.0) -> bool:
    values = [v for v in values if v and v > 0]
    return bool(values) and max(values) / min(values) >= factor


def width_axis(axis, widths) -> None:
    """Format widths on a base-two logarithmic axis, labelled where the width is a power of two."""
    widths = sorted(set(widths))
    axis.set_xscale("log", base=2)
    axis.xaxis.set_major_locator(FixedLocator(widths))
    axis.xaxis.set_minor_locator(NullLocator())
    powers = [w for w in widths if w & (w - 1) == 0 and w >= 8]
    if len(powers) > 5:                        # thin the labels, keeping the two ends
        keep = set(powers[::2]) | {powers[-1]}
        if powers[-2] in keep and powers[-1] / powers[-2] <= 4:
            keep.discard(powers[-2])
        powers = [w for w in powers if w in keep]
    if powers and widths[0] * 2 <= powers[0]:  # the smallest width, where it is not a power of two
        powers = [widths[0]] + powers
    labels = [f"{w:,}" if w in powers else "" for w in widths]
    axis.set_xticklabels(labels)
    axis.grid(True, axis="y")
    axis.grid(False, axis="x")


def panels(rows: int, cols: int, height: float, **kwargs):
    """A grid of panels on a canvas of the guide's width."""
    figure, axes = plt.subplots(rows, cols, figsize=(WIDTH, height), squeeze=False,
                                layout="constrained", **kwargs)
    figure.get_layout_engine().set(h_pad=0.07, w_pad=0.07, hspace=0.04, wspace=0.03)
    return figure, axes


def panel_title(axis, index: int, text: str) -> None:
    """The letter of a panel and the one thing that differs in it: `(b) subtraction`."""
    if hasattr(figstyle, "panel_title"):
        figstyle.panel_title(axis, index, text)
    else:
        axis.set_title(f"({chr(ord('a') + index)}) {text}", loc="left",
                       fontsize=plt.rcParams["axes.labelsize"])


def axis_labels(figure, x: str = None, y: str = None) -> None:
    """One y label for all panels, and the x label under the lowest visible panel of each column
    (a figure-level x label would collide with a legend placed below the panels)."""
    if x:
        grid = [a for a in figure.axes if a.axison and a.get_subplotspec() is not None]
        lowest = {}
        for axis in grid:
            spec = axis.get_subplotspec()
            column, row = spec.colspan.start, spec.rowspan.stop
            if column not in lowest or row > lowest[column][0]:
                lowest[column] = (row, axis)
        for _, axis in lowest.values():
            axis.set_xlabel(x)
    if y:
        figure.supylabel(y, fontsize=plt.rcParams["axes.labelsize"])


COMMIT = re.compile(r"\b(?=[0-9a-f]*[0-9])(?=[0-9a-f]*[a-f])[0-9a-f]{7,40}\b")
PROVENANCE = re.compile(r"recorded|measured|\bLean v?4\.\d|toolchain|benchmarks/|\.(lean|py|sh|csv|md)\b")


def check_rules(figure) -> None:
    """The figure rules, as far as a script can check them: no title over the figure, and no
    commit, toolchain, file name or sentence in any string that is drawn."""
    if getattr(figure, "_suptitle", None) is not None and figure._suptitle.get_text():
        raise SystemExit(f"a figure has a title: {figure._suptitle.get_text()!r}")
    for text in figstyle.all_text(figure):
        reason = ("a commit" if COMMIT.search(text) else
                  "provenance" if PROVENANCE.search(text) else
                  "a sentence" if text.rstrip().endswith((".", "?", "!")) and text.count(" ") >= 2 else "")
        if reason:
            raise SystemExit(f"figure text contains {reason}: {text!r}")


# ---- reading ---------------------------------------------------------------------------------


UNITS = {"ns": 1e-9, "µs": 1e-6, "us": 1e-6, "ms": 1e-3, "s": 1.0}


def seconds(cell: str, which: int = 0):
    """`74.9 µs / 40.4 µs` (cold / warm; `which` picks one), `1.52 ms`, `< 1 ms`, `failed`."""
    part = cell.split("/")[min(which, cell.count("/"))].strip() if cell else ""
    match = re.fullmatch(r"([0-9.,]+)\s*(ns|µs|us|ms|s)", part)
    return float(match.group(1).replace(",", "")) * UNITS[match.group(2)] if match else None


def md_tables(path: Path) -> dict:
    """The tables of a Markdown file: {section heading: [{column: cell}]} (first column: label)."""
    tables, section, header = OrderedDict(), "", None
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("#"):
            section, header = line.lstrip("# ").strip(), None
        elif line.startswith("|"):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if header is None:
                header = cells
            elif set("".join(cells)) <= set("-: "):
                continue
            else:
                tables.setdefault(section, []).append(dict(zip(header, cells)))
        else:
            header = None
    return tables


def cell_name(text: str) -> str:
    return text.strip().strip("`")


# ---- provenance and output --------------------------------------------------------------------


# The recorded Coq times, as the notes name them.
COQ = ("Coq 8.20.1 with Flocq 4.2.2, recorded 2026-11-15 in the image `leanfloat-flocq-bench:4.2.2`, one "
       "container at a time with 8 GB and two CPUs")


class Context:
    """Where the figures read and write, and what the last timing run measured."""

    def __init__(self):
        self.results = RESULTS
        self.out = OUT
        self.measured = json.loads(MEASURED.read_text()) if MEASURED.exists() else {}
        self.index = OrderedDict()

    def provenance(self, *sections) -> dict:
        """Toolchain, machine and dates of the timing sections used in the figure."""
        m = self.measured
        entries = [m.get("sections", {}).get(name) for name in sections]
        entries = [entry for entry in entries if entry] or [m]
        days = sorted({entry.get("date", "") for entry in entries} - {""})
        return dict(lean=entries[0].get("lean", m.get("lean", "")),
                    machine=m.get("machine", machine()), date=" and ".join(days))


def git_head(tree=ROOT, short: bool = True) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(tree), "rev-parse"] + (["--short=8"] if short else []) + ["HEAD"],
            text=True, stderr=subprocess.DEVNULL).strip()
    except (subprocess.CalledProcessError, OSError):
        return "unknown commit"


def published(commit: str, tree=ROOT) -> bool:
    """Whether a remote-tracking branch of the checkout contains `commit`."""
    try:
        branches = subprocess.check_output(
            ["git", "-C", str(tree), "branch", "--remotes", "--contains", commit],
            text=True, stderr=subprocess.DEVNULL)
    except (subprocess.CalledProcessError, OSError):
        return False
    return bool(branches.strip())


def where(prov: dict, more: str = "") -> str:
    """Measurement conditions for a figure caption."""
    text = "Measured"
    if prov.get("lean"):
        text += f" with Lean {prov['lean']}"
    text += f" ({prov['machine']}"
    if prov.get("date"):
        text += f", {prov['date']}"
    text += ")"
    return text + (f"; {more.rstrip('.')}." if more else ".")


def sources(lean: str, script: str) -> str:
    """The sentence of the notes that says who produced which numbers."""
    return f"From Lean: {lean}. From scripts: {script}."


def save(ctx: Context, figure, name: str, alt: str, caption: str, notes: str, columns: list,
         rows: list, inputs: list, command: str = "") -> None:
    """Write NAME.png, NAME.pdf and NAME.csv. A column is `name` or `name: what it holds`.

    `alt` describes the image, `caption` is the two to four plain sentences shown under it, and
    `notes` holds the rest (method, baselines, who produced which numbers).
    """
    check_rules(figure)
    for text in (alt, caption):
        if '"' in text or "`" in text:
            raise SystemExit(f"{name}: an alt text or caption is plain text, without quotes or code marks")
    if len(re.split(r"(?<=[.!?]) +(?=[A-Z])", caption)) > 4:
        raise SystemExit(f"{name}: a caption has at most four sentences; the rest belongs in the notes")
    ctx.out.mkdir(parents=True, exist_ok=True)
    figure.savefig(ctx.out / f"{name}.pdf", facecolor="white", bbox_inches="tight", pad_inches=0.15,
                   metadata={"CreationDate": None})
    # The PNG goes through the guide's routine, with its checks and its margin. The vector file
    # of these figures is the PDF, so a `figstyle` that writes an SVG as well is asked not to.
    options = {"vector": False} if "vector" in inspect.signature(figstyle.save).parameters else {}
    figstyle.save(figure, f"{name}.png", ctx.out / f"{name}.png", **options)   # closes the figure
    names = [c.split(":")[0].strip() for c in columns]
    with open(ctx.out / f"{name}.csv", "w", newline="", encoding="utf-8") as handle_:
        writer = csv.writer(handle_, lineterminator="\n")
        writer.writerow(names)
        writer.writerows([["" if c is None else c for c in row] for row in rows])
    ctx.index[name] = dict(name=name, alt=alt, caption=caption, notes=notes, columns=columns,
                           rows=len(rows), inputs=[relative(i) for i in inputs], command=command)
    print(f"  {name}: {len(rows)} rows")


def legend_below(figure, handles, columns=None) -> None:
    figure.legend(handles=handles, loc="outside lower center", ncol=columns or min(len(handles), 3),
                  handlelength=2.6, columnspacing=1.6)


def dumbbell(axis, labels, first, second, key_first: str, key_second: str) -> None:
    """Horizontal dumbbells: one row per label, two marks joined by a bar."""
    for row in range(len(labels)):
        a, b = first[row], second[row]
        if a and b:
            axis.plot([a, b], [row, row], color=plt.rcParams["grid.color"], linewidth=2.4, zorder=1,
                      solid_capstyle="round")
        if a:
            axis.plot([a], [row], zorder=3, **{**style(key_first), "linestyle": "none"})
        if b:
            axis.plot([b], [row], zorder=4, **{**style(key_second), "linestyle": "none"})
    axis.set_yticks(range(len(labels)))
    axis.set_yticklabels(labels)
    axis.set_ylim(len(labels) - 0.4, -0.6)
    axis.margins(x=0.06)
    axis.grid(True, axis="x")
    axis.grid(False, axis="y")
    axis.tick_params(axis="y", length=0)


def geometric_mean(values) -> float:
    values = [v for v in values if v and v > 0]
    return math.exp(sum(math.log(v) for v in values) / len(values)) if values else float("nan")


def times(value: float) -> str:
    return f"{value:,.0f}" if value >= 10 else f"{value:.1f}"


def ratio_range(ratios) -> str:
    """`2.1 to 528 times (geometric mean 28)` for the ratios of a figure's pairs."""
    ratios = [r for r in ratios if r and r > 0]
    if not ratios:
        return ""
    return f"{times(min(ratios))} to {times(max(ratios))} times (geometric mean {times(geometric_mean(ratios))})"


# ---- figures -----------------------------------------------------------------------------------

BASIC_NAMES = {"add": "addition", "sub": "subtraction", "mul": "multiplication",
               "div": "division", "sqrt": "square root", "fma": "fused multiply-add"}


def kernel_binary_rows(ctx):
    """{(series, operands, operation, bits): microseconds}, the median over the formats of a width.

    Series: `now` (the kernel path) and `written` (the public operations, the reference operations
    for the one-byte formats).
    """
    path = need(ctx.results / "backends/kernel-binary.csv", "kernel-binary.csv")
    data, inputs = defaultdict(list), [path]
    for row in read_csv(path):
        value = number(row["microseconds"])
        if value and row["commit"] == "now":
            data[("now", row["operands"], row["operation"], int(row["bits"]))].append(value)
    source = ctx.results / "kernel" / "as-written.csv"
    if source.exists():
        inputs.append(source)
        for row in read_csv(source):
            value = number(row["microseconds"])
            if value:
                data[("written", row["operands"], row["operation"], int(row["bits"]))].append(value)
    return inputs, {key: statistics.median(values) for key, values in data.items()}


def fig_kernel_binary(ctx):
    """Kernel time of one binary operation from 8 to 4,096 bits: as written and on the kernel path."""
    inputs, data = kernel_binary_rows(ctx)
    prov = ctx.provenance("kernel-binary", "kernel-public", "kernel-spec")
    widths = sorted({k[3] for k in data})
    ops = [op for op in BASIC if any(k[2] == op for k in data)]
    figure, axes = panels(2, 3, 5.6, sharex=True, sharey=True)
    rows, ratios = [], []
    present = {k[0] for k in data}
    for index, (axis, op) in enumerate(zip(axes.flat, ops)):
        for series in ("written", "now"):
            xs = [w for w in widths if (series, "normal", op, w) in data]
            ys = [data[(series, "normal", op, w)] for w in xs]
            if not xs:
                continue
            axis.plot(xs, ys, zorder=4 if series == "now" else 3,
                      **{**style(series), **({"linestyle": "none"} if series == "written" else {})})
            rows += [[op, series, w, y] for w, y in zip(xs, ys)]
        ratios += [data[("written", "normal", op, w)] / data[("now", "normal", op, w)] for w in widths
                   if ("written", "normal", op, w) in data and ("now", "normal", op, w) in data]
        width_axis(axis, widths)
        panel_title(axis, index, BASIC_NAMES[op])
    unit = time_axis(axes.flat)
    axis_labels(figure, "format width (bits)", f"kernel time per operation ({unit})")
    handles = []
    if "written" in present:
        handles.append(handle("written", "the operation as written", line=False))
    handles.append(handle("now", "the kernel path"))
    legend_below(figure, handles)
    summary = (f"Over the {len(ratios)} cells that have both, the operation as written costs "
               f"{ratio_range(ratios)} the kernel path. ") if ratios else ""
    save(ctx, figure, "kernel-binary",
         "Six panels, one per arithmetic operation: kernel time against format width, with open markers "
         "for the public operation as written up to 128 bits and a line for the kernel path up to 4,096 "
         "bits.",
         "Kernel time of one binary operation of FloatLib from 8 to 4,096 bits, as written and on the "
         "kernel path. A point is the time Lean's kernel takes for one operation on normal operands, "
         "rounded to nearest even, as the median over the formats of that width; as written is the public "
         "operation, and the kernel path is the term that float_decide checks. Both axes are logarithmic, "
         "lower is faster, and the public operations were not measured above 128 bits. " + where(prov),
         "Eight operand triples per cell, the fastest of three runs (`benchmarks/kernel/run.sh`). The "
         "formats of a width are E4M3 and E5M2 at 8 bits, binary16 and bfloat16 at 16, the IEEE layouts "
         "above, and two custom layouts of 24 and 80 bits. The public operation is `+`, `-`, `*`, `/`, "
         "`sqrt`, `fma` as written (for the two one-byte formats the reference operation, because the "
         "kernel cannot evaluate their table lookups). " + summary
         + sources("every time (`Lean.Kernel.whnf`, printed by Lean)",
                   "the medians over formats, the ratios and the drawing"),
         ["operation: add, sub, mul, div, sqrt or fma",
          "series: `written` (the public operation) or `now` (the kernel path)",
          "bits: format width", "microseconds: kernel time of one operation, median over the formats of that width"],
         rows, inputs, "python3 benchmarks/plots/figures.py time RAW --only kernel-binary kernel-public kernel-spec")


def fig_kernel_operands(ctx):
    """Kernel time by operand class: normal, subnormal, special."""
    inputs, data = kernel_binary_rows(ctx)
    prov = ctx.provenance("kernel-binary")
    data = {k: v for k, v in data.items() if k[0] == "now"}
    widths = sorted({k[3] for k in data})
    ops = [op for op in BASIC if any(k[2] == op for k in data)]
    classes = [("normal", "normal operands", "o", "-"), ("subnormal", "subnormal operands", "^", "--"),
               ("special", "special values", "s", ":")]
    figure, axes = panels(2, 3, 5.4, sharex=True, sharey=True)
    values = list(data.values())
    logy = spans_decades(values)
    rows = []
    for index, (axis, op) in enumerate(zip(axes.flat, ops)):
        for name, _, marker, line in classes:
            xs = [w for w in widths if ("now", name, op, w) in data]
            ys = [data[("now", name, op, w)] for w in xs]
            axis.plot(xs, ys, color=BLUE, marker=marker, linestyle=line)
            rows += [[op, name, w, y] for w, y in zip(xs, ys)]
        width_axis(axis, widths)
        if not logy:
            axis.set_ylim(0, 1.08 * max(values))
        panel_title(axis, index, BASIC_NAMES[op])
    unit = time_axis(axes.flat) if logy else "µs"
    axis_labels(figure, "format width (bits)", f"kernel time per operation ({unit})")
    legend_below(figure, [Line2D([], [], color=BLUE, marker=m, linestyle=l, label=label)
                          for _, label, m, l in classes])
    save(ctx, figure, "kernel-operands",
         "Six panels of lines, one per arithmetic operation: kernel time against format width for normal "
         "operands, subnormal operands and special values, all on the kernel path.",
         "Kernel time of one operation of FloatLib by operand class: normal operands, subnormal "
         "operands and special values. A point is the time Lean's kernel takes for one operation on the "
         "kernel path, as the median over the formats of that width. "
         + ("Both axes are logarithmic" if logy else "The width axis is logarithmic") + ", and lower is "
         "faster. " + where(prov),
         "Special values are zeros, the smallest subnormal, one, the largest finite value, infinities and "
         "NaNs. Eight operand triples per cell, the fastest of three runs. "
         + sources("every time (`Lean.Kernel.whnf`)", "the medians and the drawing"),
         ["operation", "operands: normal, subnormal or special", "bits",
          "microseconds: kernel time of one operation, median over the formats of that width"],
         rows, inputs[:1], "python3 benchmarks/plots/figures.py time RAW --only kernel-binary")


IEEE_GROUPS = [
    ("arithmetic (add to fma)", lambda n: n in ("addition", "subtraction", "multiplication",
                                                "division", "squareRoot", "fusedMultiplyAdd")),
    ("comparisons", lambda n: n.startswith(("compareQuiet", "compareSignaling"))),
    ("roundToIntegral", lambda n: n.startswith("roundToIntegral")),
    ("convertToInteger", lambda n: n.startswith("convertToInteger")),
    ("classification", lambda n: n in ("class", "isSignMinus", "isNormal", "isFinite", "isZero",
                                       "isSubnormal", "isInfinite", "isNaN", "isSignaling",
                                       "isCanonical", "radix")),
    ("minimum and maximum", lambda n: n.startswith(("minimum", "maximum"))),
    ("sign operations", lambda n: n in ("copy", "negate", "abs", "copySign")),
    ("total order", lambda n: n.startswith("totalOrder")),
    ("scaleB and logB", lambda n: n in ("scaleB", "logB")),
    ("neighbours, remainder", lambda n: n in ("nextUp", "nextDown", "remainder")),
    ("formatOf", lambda n: n.startswith("formatOf")),
    ("augmented", lambda n: n.startswith("augmented")),
    ("NaN payload", lambda n: "Payload" in n),
    ("reductions", lambda n: "elements" in n or "pairs" in n or n.startswith(("sum", "dot", "scaledProd"))),
    ("conversions", lambda n: n.startswith("convert") or "Character" in n),
    ("functions of 9.2", lambda n: True),
]


# A family as its panel names it, where the name in the CSV is too long for a panel title.
IEEE_TITLES = {"arithmetic (add to fma)": "arithmetic", "minimum and maximum": "minimum, maximum",
               "scaleB and logB": "scaleB, logB", "neighbours, remainder": "neighbours",
               "functions of 9.2": "functions"}


def ieee_group(name: str) -> str:
    return next(label for label, test in IEEE_GROUPS if test(name))


def fig_kernel_ieee2019(ctx):
    """Kernel time of the operations of IEEE 754-2019 by family and width, as written against the rules."""
    directory = need(ctx.results / "ieee2019", "ieee2019 results")
    path = need(directory / "kernel.csv", "ieee2019/kernel.csv")
    prov = ctx.provenance("ieee2019", "ieee2019-wide")
    # group -> bits -> (written, rules), each the time of every operation that has one
    groups = defaultdict(lambda: defaultdict(lambda: ({}, {})))
    for row in read_csv(path):
        if not row["format"].startswith(("binary", "e4f3")):
            continue
        written, rules = positive(row["as_written_microseconds"]), positive(row["with_rules_microseconds"])
        cell = groups[ieee_group(row["operation"])][int(row["bits"])]
        if written:
            cell[0][row["operation"]] = written
        if rules:
            cell[1][row["operation"]] = rules
    names = [label for label, _ in IEEE_GROUPS if label in groups]
    widths = sorted({bits for g in groups.values() for bits in g})
    cols = 4
    figure, axes = panels(math.ceil(len(names) / cols), cols,
                          1.95 * math.ceil(len(names) / cols) + 1.0, sharex=True, sharey=True)
    rows, sizes = [], []
    for index, (axis, name) in enumerate(zip(axes.flat, names)):
        for slot, key in ((0, "written"), (1, "now")):
            # A line is over one set of operations: it is drawn at the widths at which every
            # operation of the family has a time, so it never moves because one dropped out.
            family = set().union(*(groups[name][w][slot].keys() for w in widths))
            xs = [w for w in widths if family and groups[name][w][slot].keys() == family]
            times = {w: list(groups[name][w][slot].values()) for w in xs}
            mid = [statistics.median(times[w]) for w in xs]
            low = [min(times[w]) for w in xs]
            high = [max(times[w]) for w in xs]
            axis.fill_between(xs, low, high, color=colour(key), alpha=0.12, linewidth=0)
            axis.plot(xs, mid, zorder=3 if key == "now" else 2, **{**style(key), "markersize": 3.8})
            rows += [[name, "as written" if slot == 0 else "with rules", w, m, l, h,
                      len(times[w])] for w, m, l, h in zip(xs, mid, low, high)]
        width_axis(axis, widths)
        sizes.append((IEEE_TITLES.get(name, name), max(len(groups[name][w][1]) for w in widths)))
        panel_title(axis, index, IEEE_TITLES.get(name, name))
    used = list(axes.flat)[:len(names)]
    unit = time_axis(used)
    for axis in list(axes.flat)[len(names):]:
        axis.axis("off")
    for column in range(cols):                 # tick labels under the lowest panel of a column
        lowest = [axes[r][column] for r in range(axes.shape[0]) if axes[r][column] in used]
        if lowest:
            lowest[-1].tick_params(labelbottom=True)
    axis_labels(figure, "format width (bits)", f"kernel time per evaluation ({unit})")
    legend_below(figure, [handle("written", "as written"), handle("now", "with the kernel rules")])
    save(ctx, figure, "kernel-ieee2019",
         f"{len(names)} small panels of lines, one per family of operations of the standard: kernel time "
         "against format width from 8 to 4,096 bits, with a dashed line and band for the operation as "
         "written and a solid line and band for the same operation with the kernel rules.",
         "Kernel time of the operations of IEEE 754-2019 on binary formats, by family and format width, as "
         "written and with FloatLib's kernel rules. A line is the median over the operations of "
         "a family of the time Lean's kernel takes for one evaluation, at the widths at which every one "
         "of them has a time, and the band is their range; where "
         "the two lines coincide the family has no kernel rule. Both axes are logarithmic, and lower is "
         "faster. " + where(prov),
         "Each operation of clauses 5 and 9 is measured under its name in the standard, as written (the "
         "reference definition) and as `float_decide` rewrites it with the rules tagged "
         "`@[kernel_optimize]` (`benchmarks/kernel/ieee2019.sh 4 3`: four operand triples per cell, the "
         f"fastest of three); at 1,024 and 4,096 bits a row has {timing.ROW_SECONDS:,} seconds and a "
         f"certified function of clause 9.2 {timing.FUNCTION_ROW_SECONDS:,}. "
         "A line ends where an operation of its family has no time, because it takes longer than a "
         "row allows or its cell came out at zero or below. "
         "The panel neighbours holds "
         "`nextUp`, `nextDown` and `remainder`, and the panel functions the recommended functions of "
         "clause 9.2. Operations per family: "
         + ", ".join(f"{name} {count}" for name, count in sizes) + ". A cell is the difference of two "
         "folds, and the fold that is subtracted reads and stores its operand; for an operation that "
         "reads less of it (`radix`, `isCanonical` as written) the difference is zero or below, and "
         "such a cell is left out. The comparisons, the conversions to integers, the "
         "casts (`formatOf`, `convertFormat`) and the additions of the 2019 revision are all here; the "
         "decimal formats are in `ieee2019/README.md` and in `kernel-families`. "
         + sources("every time (`Lean.Kernel.whnf`)", "the grouping into families, medians and ranges"),
         ["family: group of operations (its members are in `ieee2019/kernel.csv`)",
          "path: `as written` or `with rules`", "bits: format width",
          "median_us: median over the family, microseconds", "min_us", "max_us",
          "operations: how many operations of the family have a value at that width"], rows, [path],
         "python3 benchmarks/plots/figures.py time RAW --only ieee2019 ieee2019-wide")


def fig_kernel_extras(ctx):
    """Status flags, comparisons, conversions, casts and literals: as written against the rules."""
    path = need(ctx.results / "kernel" / "extras.csv", "kernel/extras.csv")
    prov = ctx.provenance("extras")
    data = {(r["format"], r["term"]): (positive(r["as_written_microseconds"]),
                                       positive(r["with_rules_microseconds"])) for r in read_csv(path)}
    formats = [f for f in ("binary32", "binary64") if any(k[0] == f for k in data)]
    terms = [t for t in EXTRAS if any(k[1] == t for k in data)]
    figure, axes = panels(1, len(formats), 0.27 * len(terms) + 1.5, sharey=True, sharex=True)
    rows, ratios = [], []
    for index, (axis, fmt) in enumerate(zip(axes[0], formats)):
        first = [data.get((fmt, t), (None, None))[0] for t in terms]
        second = [data.get((fmt, t), (None, None))[1] for t in terms]
        dumbbell(axis, [EXTRAS[t] for t in terms], first, second, "written", "now")
        rows += [[fmt, t, EXTRAS[t], a, b] for t, a, b in zip(terms, first, second)]
        ratios += [a / b for a, b in zip(first, second) if a and b]
        panel_title(axis, index, fmt)
    unit = time_axis(axes[0], "x")
    axis_labels(figure, f"kernel time per evaluation ({unit})")
    legend_below(figure, [handle("written", "as written", line=False),
                          handle("now", "with the kernel rules", line=False)])
    summary = f"The rewritten term is {ratio_range(ratios)} cheaper. " if ratios else ""
    save(ctx, figure, "kernel-extras",
         "Two panels, binary32 and binary64, with one row per term: an open circle for the kernel time of "
         "the term as written and a filled circle for the term with the kernel rules, joined by a bar, on "
         "a logarithmic time axis.",
         "Kernel time of the terms beyond the six operations (status flags, comparisons, conversions, casts "
         "and literals), as written and with FloatLib's kernel rules. A mark is the time Lean's "
         "kernel takes for one evaluation on normal operands; as written goes through the public "
         "operation, and the other mark is the term after the rewrite of float_decide. The time axis is "
         "logarithmic, and lower is faster. " + where(prov),
         "64 operand triples or literals per cell, the fastest of five runs (`benchmarks/kernel/extras.sh "
         "64 5`). A row with `status := true` evaluates the value, the comparison of the flags with a "
         "record and the comparison of the ternary value with a constant, as a statement about an outcome "
         "does. " + summary + "A cell is the difference of two folds, and one that comes out at zero or "
         "below on a busy machine is left out. "
         + sources("every time (`Lean.Kernel.whnf`)", "the ratios and the drawing"),
         ["format: binary32 or binary64", "term: the row name of `extras.sh`", "label: the term as drawn",
          "as_written_us: microseconds through the public operation",
          "with_rules_us: microseconds after the rewrite of `float_decide`"],
         rows, [path], "python3 benchmarks/plots/figures.py time RAW --only extras")


def fig_kernel_vs_coq(ctx):
    """The same loops in Lean's kernel and in Coq with Flocq, under vm_compute and lazy."""
    path = need(ctx.results / "backends/matched.csv", "matched.csv")
    prov = ctx.provenance("matched")
    data = read_csv(path)
    ops = [op for op in BASIC if any(r["operation"] == op for r in data)]
    widths = sorted({int(r["bits"]) for r in data})
    figure, axes = panels(2, 3, 5.6, sharex=True, sharey=True)
    series = (("lean_kernel_us", "now"), ("flocq_vm_us", "coq_vm"), ("flocq_lazy_us", "coq_lazy"))
    top = max(number(r[c]) or 0 for r in data for c, _ in series)
    rows, absent = [], 0
    for index, (axis, op) in enumerate(zip(axes.flat, ops)):
        selected = sorted((r for r in data if r["operation"] == op), key=lambda r: int(r["bits"]))
        for column, key in series:
            points = [(int(r["bits"]), number(r[column])) for r in selected]
            xs = [x for x, y in points if y]
            axis.plot(xs, [y for _, y in points if y], zorder=3 if key == "now" else 2, **style(key))
            gone = [x for x, y in points if not y]
            if gone:
                absent += len(gone)
                axis.plot(gone, [top * 1.8] * len(gone), linestyle="none", marker="x",
                          color=colour(key), markersize=6, markeredgewidth=1.4, clip_on=False)
            rows += [[op, column, x, y] for x, y in points]
        width_axis(axis, widths)
        panel_title(axis, index, BASIC_NAMES[op])
    used = list(axes.flat)[:len(ops)]
    unit = time_axis(used)
    for axis in used:
        axis.tick_params(labelbottom=True)
    spare = list(axes.flat)[len(ops):]
    for axis in spare:
        axis.axis("off")
    handles = [handle("now", NOW), handle("coq_vm", f"{COQ_NAME}, vm_compute"),
               handle("coq_lazy", f"{COQ_NAME}, lazy")]
    if absent:
        handles.append(Line2D([], [], linestyle="none", marker="x", color=MUTED, markeredgewidth=1.4,
                              label="no result"))
    legend_below(figure, handles, columns=2)
    axis_labels(figure, "format width (bits)", f"time per operation ({unit})")
    lean = [number(r["lean_kernel_us"]) for r in data if number(r["lean_kernel_us"])]
    summary = (f"Lean's kernel takes {min(lean):.0f} to {max(lean):.0f} microseconds per operation "
               "over all widths. ") if lean else ""
    save(ctx, figure, "kernel-vs-coq",
         f"{len(ops)} panels of lines, one per operation: time per operation against format width for "
         "FloatLib in Lean's kernel and for Flocq in Coq under vm_compute and under lazy, with "
         "crosses along the top edge at the widths where Coq gave no result.",
         "Time of one floating-point operation inside the proof checker: FloatLib in Lean's kernel "
         "against Flocq 4.2.2 in Coq 8.20.1 under vm_compute and under lazy. A point is the time per "
         "operation in a loop of 100 operations (10 from 512 bits on) on the same operands; a cross at the "
         "top marks a width where Coq gave no result within 8 GB and 300 seconds. Both axes are "
         "logarithmic, and lower is faster. "
         + where(prov, "the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs"),
         "Lean: FloatLib's kernel path (`#kernel_cost rewritten`, `benchmarks/suite/matched.py`). Coq: "
         "Flocq's `Bplus`, `Bmult`, `Bdiv`, `Bsqrt` and `Bfma` (`BinarySingleNaN`, `mode_NE`). " + summary
         + "In the recorded run Coq printed the value that Lean computed in every row. " + COQ + "; these "
         "times do not depend on FloatLib's commit. "
         + sources("the Lean times (`Lean.Kernel.whnf`)",
                   "the Coq times (printed by Coq in a container) and the comparison of the values"),
         ["operation", "series: `lean_kernel_us` (measured), `flocq_vm_us` or `flocq_lazy_us` (recorded)",
          "bits: format width", "microseconds: time per operation, empty where Coq gave no result"],
         rows, [path, RECORDED / "coq-flocq.csv"],
         "python3 benchmarks/plots/figures.py time RAW --only matched")


def fig_kernel_loops(ctx):
    """Three theorems about loops of 1,000 steps: decide +kernel, float_decide, and Coq."""
    path = need(ctx.results / "kernel" / "loops.csv", "kernel/loops.csv")
    prov = ctx.provenance("loops")
    data = {(r["theorem"], r["path"]): number(r["seconds"]) for r in read_csv(path)}
    coq, inputs = {}, [path]
    if (RECORDED / "coq-loops.csv").exists():
        inputs.append(RECORDED / "coq-loops.csv")
        coq = {r["theorem"]: r for r in read_csv(RECORDED / "coq-loops.csv")}
    names = [n for n in LOOPS if any(k[0] == n for k in data)]
    figure, axes = panels(1, 1, 0.6 * len(names) + 1.7)
    axis = axes[0][0]
    public = [data.get((n, "public")) for n in names]
    kernel = [data.get((n, "kernel")) for n in names]
    dumbbell(axis, [LOOPS[n] for n in names], public, kernel, "written", "now")
    rows = []
    for index, name in enumerate(names):
        row = coq.get(name, {})
        conversion, vm = number(row.get("coq_kernel_conversion_seconds")), number(row.get("coq_vm_seconds"))
        if conversion:
            axis.plot([conversion], [index], zorder=3, **{**style("coq_lazy"), "linestyle": "none"})
        if vm:
            axis.plot([vm], [index], zorder=3, **{**style("coq_vm"), "linestyle": "none"})
        rows.append([name, LOOPS[name], public[index], kernel[index], conversion, vm])
    unit = time_axis([axis], "x", base=1.0)
    axis.set_xlabel(f"time to check the theorem ({unit})")
    legend_below(figure, [handle("written", f"{NOW}, decide +kernel", line=False),
                          handle("now", f"{NOW}, float_decide", line=False),
                          handle("coq_lazy", f"{COQ_NAME}, conversion", line=False),
                          handle("coq_vm", f"{COQ_NAME}, vm_compute", line=False)], columns=2)
    ratios = [a / b for a, b in zip(public, kernel) if a and b]
    summary = f"`float_decide` is {ratio_range(ratios)} faster than `decide +kernel`. " if ratios else ""
    save(ctx, figure, "kernel-loops",
         "Three rows, one per theorem, on a logarithmic time axis: an open circle for decide +kernel and a "
         "filled circle for float_decide in Lean, joined by a bar, and a triangle and a square for the "
         "same result in Coq by conversion and by vm_compute.",
         "Time to check a theorem about a loop of 1,000 floating-point operations: FloatLib by "
         "decide +kernel and by float_decide, and Flocq 4.2.2 in Coq 8.20.1. A mark is the time the proof "
         "checker spends on a theorem that states the encoding of the loop's result. The time axis is "
         "logarithmic, and lower is faster. "
         + where(prov, "the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs"),
         "Lean: the fastest of three runs (`benchmarks/kernel/loops.sh 3`, the `type checking` line of "
         "Lean's profiler), by `decide +kernel` on the public operations and by `float_decide`. " + summary + "Coq: the `Time Qed` lines of "
         "`benchmarks/kernel/FlocqConversion.v`, by kernel conversion at `Qed` and by `vm_compute`; " + COQ
         + ". "
         + sources("the Lean times (Lean's profiler)", "the Coq times (printed by Coq) and the ratios"),
         ["theorem: name in `benchmarks/kernel/Loops.lean`", "statement",
          "decide_kernel_seconds: `decide +kernel` on the public operations, this commit",
          "float_decide_seconds: `float_decide`, this commit",
          "coq_kernel_conversion_seconds: recorded", "coq_vm_seconds: recorded"],
         rows, inputs, "python3 benchmarks/plots/figures.py time RAW --only loops")


BLOCK_LABELS = {"MX": "MX block", "NVFP4": "NVFP4 block of 16"}


def fig_kernel_families(ctx):
    """One operation in the other families, as written against the tagged kernel rules."""
    path = need(ctx.results / "backends/families.csv", "families.csv")
    prov = ctx.provenance("families", "blocks", "ieee2019", "kernel-spec", "kernel-binary")
    inputs = [path]
    entries = [(r["operation"], number(r["as_written_us"]), number(r["rules_us"]))
               for r in read_csv(path)]
    ieee = ctx.results / "ieee2019" / "kernel.csv"
    if ieee.exists():                                   # the decimal operations under the standard's names
        entries = [e for e in entries if not e[0].startswith("decimal")]
        wanted = ["addition", "multiplication", "division", "squareRoot", "fusedMultiplyAdd",
                  "compareQuietLess", "quantize"]
        for row in read_csv(ieee):
            if row["format"] == "decimal64" and row["operation"] in wanted:
                entries.append((f"decimal64 {row['operation']}",
                                number(row["as_written_microseconds"]),
                                number(row["with_rules_microseconds"])))
        inputs.append(ieee)
    written = ctx.results / "kernel" / "as-written.csv"
    binary = ctx.results / "backends" / "kernel-binary.csv"
    if written.exists() and binary.exists():            # OCP FP8: the one-byte formats
        now = {(r["format"], r["operation"]): number(r["microseconds"]) for r in read_csv(binary)
               if r["commit"] == "now" and r["operands"] == "normal"}
        for row in read_csv(written):
            if row["path"] == "spec" and row["operands"] == "normal" and row["operation"] in ("add", "mul", "fma"):
                entries.append((f"ocp-fp8 {row['format']} {row['operation']}", number(row["microseconds"]),
                                now.get((row["format"], row["operation"]))))
        inputs += [written, binary]
    blocks = ctx.results / "kernel" / "blocks.csv"
    if blocks.exists():                                 # block formats: only the rewritten term is timed
        for row in read_csv(blocks):
            entries.append((f"{BLOCK_LABELS.get(row['family'], row['family'])}: {row['row']}", None,
                            number(row["with_rules_microseconds"])))
        inputs.append(blocks)
    family = lambda name: re.split(r"[ (\-0-9:]", name)[0]
    order = []
    for name, *_ in entries:
        if family(name) not in order:
            order.append(family(name))
    entries.sort(key=lambda e: order.index(family(e[0])))
    ruled = [not (a is not None and (not b or abs(a - b) / a <= 0.02)) for _, a, b in entries]
    figure, axes = panels(1, 1, 0.215 * len(entries) + 1.3)
    axis = axes[0][0]
    dumbbell(axis, [e[0].split(" (")[0] for e in entries], [e[1] for e in entries],
             [e[2] if has_rule else None for e, has_rule in zip(entries, ruled)], "written", "now")
    unit = time_axis([axis], "x")
    axis.set_xlabel(f"kernel time per evaluation ({unit})")
    legend_below(figure, [handle("written", "as written", line=False),
                          handle("now", "with the kernel rules", line=False)])
    ratios = [a / b for (_, a, b), has_rule in zip(entries, ruled) if has_rule and a and b]
    summary = f"Where both are timed, the rewritten term is {ratio_range(ratios)} cheaper. " if ratios else ""
    alone = sum(1 for _, a, _ in entries if a is None)
    save(ctx, figure, "kernel-families",
         f"{len(entries)} rows, one per operation of a format family, on a logarithmic time axis: an open "
         "circle for the kernel time of the operation as written and a filled circle for the operation "
         f"with the kernel rules, joined by a bar; the last {alone} rows, the block formats, have a filled "
         "circle only.",
         "Kernel time of one operation outside the binary interchange formats, as written and with the "
         "kernel rules of FloatLib: fixed point, logarithmic, P3109, posits and the quire, OCP MX "
         "elements and blocks, decimal, OCP FP8 and NVFP4 blocks. A mark is the time Lean's kernel takes "
         "for one evaluation; a row with one mark times the rewritten term alone. The time axis is "
         "logarithmic, and lower is faster. " + where(prov),
         "As written is the reference definition, and the other mark is the term as `float_decide` "
         "rewrites it with the rules tagged `@[kernel_optimize]`. " + summary + "The block rows "
         "(`benchmarks/kernel/MX.lean`, `NVFP4.lean`) time the rewritten term only. A single evaluation "
         "includes about 100 microseconds of fixed work. The OCP FP8 rows are the reference operation "
         "against the kernel path, eight operand triples per cell. The labels drop the constants a term is "
         "compared with; the CSV has the full names. There is no codebook row: no benchmark under "
         "`benchmarks/` times a codebook format in the kernel. "
         + sources("every time (`#kernel_cost`, the median of one evaluation; `Lean.Kernel.whnf` for the "
                   "decimal and FP8 rows)", "the ratios"),
         ["operation: family and operation", "as_written_us: microseconds as written (empty: not timed)",
          "with_rules_us: microseconds with the tagged kernel rules"],
         [[n, a, b] for n, a, b in entries], inputs,
         "python3 benchmarks/plots/figures.py time RAW --only families blocks ieee2019 kernel-spec kernel-binary")


def fig_kernel_all_pairs(ctx):
    """Statements about all pairs of encodings: the loop of float_decide against lane_decide."""
    path = need(ctx.results / "backends/exhaustive.csv", "exhaustive.csv")
    prov = ctx.provenance("exhaustive")
    data = read_csv(path)
    statements = list(OrderedDict.fromkeys(r["statement"] for r in data))
    loop = {r["statement"]: number(r["seconds"]) for r in data if "loop" in r["method"]}
    lanes = {r["statement"]: number(r["seconds"]) for r in data if "lane" in r["method"]}
    figure, axes = panels(1, 1, 0.34 * len(statements) + 1.4)
    axis = axes[0][0]
    dumbbell(axis, statements, [loop.get(s) for s in statements], [lanes.get(s) for s in statements],
             "written", "now")
    unit = time_axis([axis], "x", base=1.0)
    axis.set_xlabel(f"kernel time per statement ({unit})")
    legend_below(figure, [handle("written", "float_decide", line=False),
                          handle("now", "lane_decide", line=False)])
    ratios = [loop[s] / lanes[s] for s in statements if loop.get(s) and lanes.get(s)]
    summary = f"Where both ran, `lane_decide` is {ratio_range(ratios)} faster. " if ratios else ""
    save(ctx, figure, "kernel-all-pairs",
         f"{len(statements)} rows, one per statement, on a logarithmic time axis: an open circle for the "
         "loop of float_decide and a filled circle for lane_decide, joined by a bar where both were run.",
         "Kernel time to decide one statement about all 65,536 pairs of encodings, by the loop of "
         "float_decide and by lane_decide in FloatLib. A mark is the time Lean's kernel takes for a "
         "statement about all pairs of an 8-bit format, or about a slice of 65,536 pairs of binary16. The "
         "time axis is logarithmic, and lower is faster. " + where(prov),
         "The loop of `float_decide` runs over the pairs (`benchmarks/kernel/Exhaustive.lean`); "
         "`lane_decide` runs both sides once on rows that hold one pair per lane "
         "(`benchmarks/suite/Lanes.lean`). " + summary + "A lane time is the sum over the lane widths that "
         "were tried: a run that does not fit lanes of 16 bits is repeated with 32 and then 64. "
         "`add-table` is the kernel check of one packed table. A statement without a loop time was not run "
         "as a loop. "
         + sources("every time (Lean's profiler: the type checking of one theorem)",
                   "the sums over lane widths and the ratios"),
         ["statement", "loop_seconds: the loop of `float_decide`, empty if not run",
          "lanes_seconds: `lane_decide`"],
         [[s, loop.get(s), lanes.get(s)] for s in statements], [path],
         "python3 benchmarks/plots/figures.py time RAW --only exhaustive")


EXACT_PAIRS = [   # label, section, row as written, row on Numerics.Kernel, Coq row
    ("integer sum", "int", "a + b", "Z.add", "Z.add"),
    ("integer product", "int", "a * b", "Z.mul", None),
    ("integer comparison", "int", "decide (a ≤ b)", "Int.ble'", "Z.leb"),
    ("integer quotient", "int", "a / b", "Z.ediv", None),
    ("fraction sum and comparison", "rat", "a + b < c (Rat)", "a + b < c (Frac)",
     "Q: x + b < c, unreduced"),
    ("fraction product and comparison", "rat", "a * b < c (Rat)", "a * b < c (Frac)", None),
    ("bit length", "nat", "Nat.log2", "Kernel.size", None),
    ("one bit", "nat", "Nat.testBit", "Kernel.testBit", None),
    ("population count", "nat", "(Nat.digits 2 n).sum", "Kernel.popCount", None),
    ("integer square root", "nat", "Nat.sqrt", "Kernel.isqrt", None),
    ("modular power", "mod", "powModWindow 0 (binary)", "powMod", None),
    ("dyadic sum", "dyad", None, "Dyad.add", None),
    ("ball product", "ball", None, "Ball.mul", None),
    ("complex ball product", "complex", None, "CBall.mul", None),
    ("length of a list of 256", "list", "(List.range 256).map, length", "Seq.tabulate 256, Seq.len", None),
    ("entry 200 of a list of 256", "list", "(List.range 256).map, getD 200", "Seq.tabulate 256, Seq.getD 200", None),
]


def fig_kernel_exact_operations(ctx):
    """Exact kernel arithmetic: core Lean and Mathlib against Numerics.Kernel, and Coq."""
    directory = need(ctx.results / "exact", "exact results")
    path = need(directory / "operations.md", "exact/operations.md")
    prov = ctx.provenance("exact")
    tables = md_tables(path)
    coq = md_tables(directory / "coq.md") if (directory / "coq.md").exists() else {}
    coq_rows = {cell_name(r["operation"]): r for rows_ in coq.values() for r in rows_}

    def lookup(section, name, column):
        for row in tables.get(section, []):
            if cell_name(row.get("operation", "")) == name:
                return seconds(row.get(column, ""))
        return None

    sizes = ["64 bits", "1,024 bits"]
    pairs = [pair for pair in EXACT_PAIRS                       # a row the logs do not have is left out
             if any(lookup(pair[1], pair[3], size) for size in sizes)]
    figure, axes = panels(1, len(sizes), 0.3 * len(pairs) + 1.5, sharey=True)
    rows, ratios, with_coq = [], [], set()
    for index, (axis, size) in enumerate(zip(axes[0], sizes)):
        written = [lookup(s, w, size) if w else None for _, s, w, _, _ in pairs]
        kernel = [lookup(s, k, size) for _, s, _, k, _ in pairs]
        scale = 1e6
        first = [v * scale if v else None for v in written]
        second = [v * scale if v else None for v in kernel]
        ratios += [a / b for a, b in zip(first, second) if a and b]
        dumbbell(axis, [p[0] for p in pairs], first, second, "other", "now")
        for row, pair in enumerate(pairs):
            other = seconds(coq_rows.get(pair[4], {}).get(size, "")) if pair[4] else None
            if other:
                with_coq.add(pair[0])
                axis.plot([other * scale], [row], zorder=3, **{**style("coq_vm"), "linestyle": "none"})
            rows.append([pair[0], size, first[row], second[row], other * scale if other else None])
        panel_title(axis, index, f"operands of {size}")
    unit = time_axis(axes[0], "x")
    axis_labels(figure, f"kernel time per operation ({unit})")
    handles = [handle("other", "core Lean and Mathlib", line=False),
               handle("now", "FloatLib kernel layer", line=False)]
    if with_coq:
        handles.append(handle("coq_vm", "Coq 8.20.1, vm_compute", line=False))
    legend_below(figure, handles)
    summary = (f"Where both exist, the kernel layer is {ratio_range(ratios)} cheaper than the as-written "
               "form. ") if ratios else ""
    save(ctx, figure, "kernel-exact-operations",
         "Two panels, operands of 64 and of 1,024 bits, with one row per exact operation on a logarithmic "
         "time axis: a grey cross for the operation written with core Lean and Mathlib, a filled circle "
         f"for FloatLib's kernel layer, joined by a bar, and a square for Coq on {len(with_coq)} of the rows.",
         "Kernel time of one exact operation (integers, fractions, bit operations, roots, modular powers, "
         "dyadics, balls and lists), written with the types of core Lean and Mathlib and on the kernel "
         "layer of FloatLib, with Coq 8.20.1 where the operation is the same. A mark is the time the "
         "kernel takes for one operation in a fresh kernel state; a row with one mark is a type that only "
         "the kernel layer has. The time axis is logarithmic, and lower is faster. "
         + where(prov, "the Coq times were recorded on 2026-11-15 in a container"),
         "The kernel layer is `FloatLib.Numerics.Kernel` (`benchmarks/exact/Operations.lean`). " + summary
         + "The Coq marks are `Z` and `Q` under `vm_compute`, recorded 2026-11-15 in the image "
         "`leanfloat-flocq-bench:4.2.2` (`exact/coq.md`). "
         + sources("the Lean times (`Lean.Kernel.whnf`)",
                   "the Coq times (printed by Coq in a container) and the ratios"),
         ["operation", "size: operand size", "as_written_us: core Lean or Mathlib, microseconds",
          "kernel_us: `FloatLib.Numerics.Kernel`, microseconds", "coq_vm_us: Coq, recorded"], rows,
         [path, directory / "coq.md"], "python3 benchmarks/plots/figures.py time RAW --only exact")


EXACT_LIBRARY = [   # label, file, section, row
    ("grid interval product, 64 bits", "baseline.md", "grid", "mul`, 64 bits"),
    ("grid interval quotient, 64 bits", "baseline.md", "grid", "div?`, 64 bits"),
    ("exp enclosure, degree 20", "baseline.md", "elementary", "exp"),
    ("log enclosure, degree 20", "baseline.md", "elementary", "log"),
    ("sin enclosure, degree 20", "baseline.md", "elementary", "sin"),
    ("integer cube root, 4,096 bits", "baseline.md", "root", "4,096"),
    ("interval checker, 35 boxes", "baseline.md", "checker", ""),
    ("interval: x (1 - x) ≤ 13/50", "tactic.md", "interval", "x * (1 - x)"),
    ("interval: exp x ≤ 11/4", "tactic.md", "interval", "exp x ≤"),
    ("interval: x exp (-x) ≤ 2/5", "tactic.md", "interval", "x * exp"),
    ("interval: log x ≤ 7/10", "tactic.md", "interval", "log x"),
    ("interval: sin x ≤ x", "tactic.md", "interval", "sin x"),
]


def fig_kernel_exact_library(ctx):
    """Kernel time of FloatLib's exact layer and elaboration time of the interval tactic."""
    directory = need(ctx.results / "exact", "exact results")
    prov = ctx.provenance("exact")
    loaded = {name: md_tables(need(directory / name, f"exact/{name}"))
              for name in ("baseline.md", "tactic.md")}
    labels, values = [], []
    for label, name, section, key in EXACT_LIBRARY:
        row = next((r for r in loaded[name].get(section, []) if key in r.get("row", "")), None)
        if row and seconds(row.get("time", "")):
            labels.append(label)
            values.append(seconds(row["time"]) * 1e3)
    if not labels:
        raise Missing("no row of EXACT_LIBRARY found in baseline.md and tactic.md")
    figure, axes = panels(1, 1, 0.3 * len(labels) + 1.4)
    axis = axes[0][0]
    dumbbell(axis, labels, values, [None] * len(labels), "now", "now")
    unit = time_axis([axis], "x", base=1e-3)
    axis.set_xlabel(f"time per evaluation or example ({unit})")
    save(ctx, figure, "kernel-exact-library",
         f"{len(labels)} rows on a logarithmic time axis, seven for evaluations of the exact layer and "
         "five for calls of the interval tactic, each with one filled circle at its time.",
         "Time of FloatLib's own exact arithmetic and of the interval tactic. A mark is the kernel time of "
         "one evaluation, and for the interval rows the time to elaborate one whole example, reification "
         "included. The time axis is logarithmic, and lower is faster. " + where(prov),
         "The evaluations are those of `benchmarks/exact/Baseline.lean` (grid interval arithmetic, the "
         "enclosures of the elementary functions, the integer root and the interval checker) and the "
         "examples those of `benchmarks/exact/Tactic.lean`; the full tables are `exact/baseline.md` and "
         "`exact/tactic.md`. " + sources("every time", "nothing but the drawing"),
         ["row", "ms: milliseconds"],
         [[l, v] for l, v in zip(labels, values)],
         [directory / "baseline.md", directory / "tactic.md"],
         "python3 benchmarks/plots/figures.py time RAW --only exact")


def fig_kernel_exact_native(ctx):
    """decide +kernel on Numerics.Kernel against native_decide."""
    directory = need(ctx.results / "exact", "exact results")
    path = need(directory / "native.md", "exact/native.md")
    prov = ctx.provenance("exact-native")
    rows_ = [r for table in md_tables(path).values() for r in table]
    labels, kernel, native = [], [], []
    for row in rows_:
        k = seconds(row.get("`decide +kernel`", ""))
        n = seconds(row.get("`native_decide`", ""))
        if k:
            labels.append(row["statement"].replace("`", ""))
            kernel.append(k * 1e3)
            native.append(n * 1e3 if n else None)
    figure, axes = panels(1, 1, 0.34 * len(labels) + 1.4)
    axis = axes[0][0]
    dumbbell(axis, labels, native, kernel, "other", "now")
    axis.set_xlim(0, 1.12 * max(v for v in kernel + native if v))
    axis.set_xlabel("time to elaborate one example (ms)")
    legend_below(figure, [handle("now", f"{NOW}, decide +kernel", line=False),
                          handle("other", "native_decide", line=False)])
    failed = sum(1 for n in native if not n)
    save(ctx, figure, "kernel-exact-native",
         f"{len(labels)} rows, one per closed statement, on a linear time axis in milliseconds: a filled "
         "circle for decide +kernel and a grey cross for native_decide, joined by a bar; "
         + ("every row has both marks." if not failed else
            f"{failed} row{'s have' if failed > 1 else ' has'} no cross."),
         "Time to prove one closed statement by decide +kernel on the kernel layer of FloatLib and "
         "by native_decide. A mark is the time to elaborate one example, elaboration included; "
         "native_decide compiles the statement and trusts the compiler"
         + ("" if not failed else ", and a row without its mark is a statement on which it failed")
         + ". The time axis is linear, and lower is faster. " + where(prov),
         "The statements are closed Boolean statements on the functions of `Numerics.Kernel` "
         "(`exact/native.md`). FloatLib never uses `native_decide`. "
         + sources("every time", "nothing but the drawing"),
         ["statement", "kernel_ms: `decide +kernel`", "native_decide_ms: `native_decide`, empty where it fails"],
         [[l, k, n] for l, k, n in zip(labels, kernel, native)], [path],
         "python3 benchmarks/plots/figures.py time RAW --only exact-native")


def fig_interval_corpora(ctx):
    """Goals closed on four test corpora by `interval` and by two other tactics."""
    path = need(RECORDED / "interval-corpora.csv", "recorded/interval-corpora.csv")
    data = read_csv(path)
    corpora = [("floatlib", "FloatLib tests of interval"), ("mathlib", "Mathlib tests of dyadic_interval"),
               ("symlean", "SymLean tests of cega"), ("ieantn", "IEANTN floors")]
    engines = [("dyadic_interval", "other2", "Mathlib dyadic_interval", "//"),
               ("cega", "other", "SymLean cega", None),
               ("interval", "now", "FloatLib interval", None)]
    totals = Counter()
    for goal in {r["goal"] for r in data}:
        totals[goal.split("_")[0]] += 1
    figure, axes = panels(1, 1, 4.6)
    axis = axes[0][0]
    height, rows = 0.24, []
    for index, (corpus, label) in enumerate(corpora):
        for slot, (engine, key, name, hatch) in enumerate(engines):
            mine = [r for r in data if r["corpus"] == corpus and r["engine"] == engine]
            count = sum(1 for r in mine if r["closed"] == "yes")
            elapsed = [float(r["seconds"]) for r in mine if r["closed"] == "yes"]
            share = 100.0 * count / totals[corpus] if totals[corpus] else 0
            y = index + (slot - 1) * (height + 0.02)
            axis.barh(y, share, height=height, color=colour(key), hatch=hatch,
                      edgecolor="white", linewidth=0.6)
            axis.text(share + 1, y, f"{count} of {totals[corpus]}", va="center", ha="left",
                      fontsize=small(), color=INK)
            rows.append([label, name, count, totals[corpus],
                         round(statistics.median(elapsed), 2) if elapsed else None])
    axis.set_yticks(range(len(corpora)))
    axis.set_yticklabels([label for _, label in corpora])
    axis.invert_yaxis()
    axis.set_xlim(0, 114)
    axis.xaxis.set_major_locator(FixedLocator([0, 25, 50, 75, 100]))
    axis.set_xlabel("goals closed (% of the corpus)")
    axis.grid(True, axis="x")
    axis.grid(False, axis="y")
    axis.tick_params(axis="y", length=0)
    legend_below(figure, [Patch(facecolor=colour(key), hatch=hatch, edgecolor="white", label=name)
                          for _, key, name, hatch in engines], columns=2)
    closed = lambda engine: sum(1 for r in data if r["engine"] == engine and r["closed"] == "yes")
    save(ctx, figure, "interval-corpora",
         "Four groups of three horizontal bars, one group per test corpus and one bar per tactic, on an "
         "axis from 0 to 100 percent; each bar ends in its count of closed goals out of the goals of the "
         "corpus.",
         f"Goals closed on four test corpora ({sum(totals.values())} goals) by FloatLib's interval tactic, "
         "by Mathlib's dyadic_interval and by SymLean's cega. A bar is the "
         "share of a corpus that one tactic call per goal closes, with the count at its end; a count says "
         "what a tactic did on that corpus, not what it does on all goals. Recorded on 2026-11-16 with "
         "Lean 4.35.0, and not run again by the timing mode.",
         "Each goal is its own file with one tactic call and its axioms checked: Mathlib's "
         f"`dyadic_interval` ({closed('dyadic_interval')} closed), SymLean's `cega` ({closed('cega')}) and "
         f"`interval` ({closed('interval')}). The CSV has the median time of a closed goal, which is "
         "mostly the imports of its file. The corpora are other projects' test files and are not in this "
         "repository, so the timing mode does not run them; the time of `interval` on FloatLib's own "
         "examples is in `kernel-exact-library`. "
         + sources("whether each goal closed, and its time", "the counts and medians"),
         ["corpus", "engine", "closed: goals closed", "goals: goals in the corpus",
          "median_seconds: median wall time of a closed goal, imports included"], rows, [path])


def fig_correctly_rounded(ctx):
    """Compiled time of one call of each correctly rounded function, by precision."""
    prov = ctx.provenance("functions")
    real, inputs = defaultdict(dict), []
    path = ctx.results / "ieee2019" / "compiled.csv"
    if path.exists():
        for row in read_csv(path):
            value = number(row["nanoseconds"])
            if row["radix"] == "binary" and row["operation"] in REAL_FUNCTIONS and value:
                real[row["operation"]][int(row["bits"])] = value / 1e6
        inputs.append(path)
    complex_ = defaultdict(dict)
    source = RECORDED / "complex-times.csv"
    if source.exists():
        for row in read_csv(source):
            if row["format"] != "bfloat16" and number(row["milliseconds"]):
                complex_[row["function"]][int(row["bits"])] = float(row["milliseconds"])
        inputs.append(source)
    if not real and not complex_:
        raise Missing("ieee2019/compiled.csv and recorded/complex-times.csv")
    shown = [(data, label) for data, label in ((real, "real"), (complex_, "complex")) if data]
    figure, axes = panels(1, len(shown), 4.0, sharey=True)
    rows = []
    for index, (axis, (data, domain)) in enumerate(zip(axes[0], shown)):
        widths = sorted({b for f in data.values() for b in f})
        for function, points in data.items():
            xs = sorted(points)
            axis.plot(xs, [points[x] for x in xs], color=BLUE, linewidth=0.7, alpha=0.35)
            rows += [[domain, function, x, points[x]] for x in xs]
        median = [statistics.median(p[w] for p in data.values() if w in p) for w in widths]
        axis.plot(widths, median, zorder=4, **style("now"))
        rows += [[domain, "median", w, m] for w, m in zip(widths, median)]
        width_axis(axis, widths)
        panel_title(axis, index, f"{domain} functions")
    unit = time_axis(axes[0], base=1e-3)
    axis_labels(figure, "format width (bits)", f"time per call ({unit})")
    legend_below(figure, [Line2D([], [], color=BLUE, linewidth=0.7, alpha=0.6, label="one function"),
                          handle("now", "median of the functions")])
    save(ctx, figure, "correctly-rounded",
         "Two panels of lines, real functions and complex functions: compiled time per call against "
         "format width, with one thin line per function and a thick line with markers for their median.",
         f"Compiled time of one call of each correctly rounded function of FloatLib by format width: "
         f"{len(real)} real functions and {len(complex_)} complex functions. A thin line is one function, "
         "rounded to nearest even, and the thick line is the median over the functions. Both axes are "
         "logarithmic, and lower is faster. "
         + where(prov, "the complex times were recorded on 2026-11-16 with Lean 4.35.0"),
         "Real: the recommended functions of IEEE 754-2019, clause 9.2, on the descriptor model "
         "(`execFloatIEEE2019 functions FORMAT`): one pass over eight operands up to 128 bits, two at 256 "
         "bits, one at 1,024 and 4,096 bits, where a function without a result within 120 seconds has no "
         "point. Complex: the functions of C23 Annex G, as recorded: the "
         "average over each run of its comparison with GNU MPC, whose arguments differ from width to width "
         "(the hard grid weighs on binary64 and above), timed by a Python driver around the compiled "
         "oracle. No runner under `benchmarks/` times the complex functions, so the timing mode does not "
         "measure them again. "
         + sources("the times of the real functions (`IO.monoNanosNow` in the benchmark executable)",
                   "the times of the complex functions and the medians"),
         ["domain: real (measured) or complex (recorded)", "function: its name, or `median`",
          "bits: format width", "milliseconds: compiled time of one call"], rows, inputs,
         "python3 benchmarks/plots/figures.py time RAW --only functions")


def fig_compiled_precision(ctx):
    """Compiled arithmetic at every precision: FloatLib, MPFR, SoftFloat and the host FPU."""
    path = need(ctx.results / "backends/compiled-comparison.csv", "compiled-comparison.csv")
    calls = need(ctx.results / "public-binary/measurements.csv", "public-binary/measurements.csv")
    prov = ctx.provenance("compiled-comparison")
    data = read_csv(path)
    # At 32 and 64 bits the harness names the fixed-word kernels, and a public call selects other
    # proved kernels. Its times are the medians of the public-call campaign, as their own series.
    public, trials = "FloatLib public call", defaultdict(list)
    for r in read_csv(calls):
        if r["arm"] == "binary" and r["format"] in ("binary32", "binary64"):
            trials[r["operation"], r["width"]].append(number(r["ns_per_operation"]))
    data += [dict(operation=op, implementation=public, bits=bits,
                  nanoseconds=round(statistics.median(times), 1)) for (op, bits), times in trials.items()]
    keys = [("FloatLib", "now", f"{NOW}, fixed-word kernels at 32 and 64 bits"),
            (public, "written", f"{NOW}, public call"), ("MPFR", "mpfr", MPFR_NAME),
            ("SoftFloat", "softfloat", SOFTFLOAT_NAME), ("native FPU", "other", "host FPU")]
    ops = [op for op in BASIC if any(r["operation"] == op for r in data)]
    widths = sorted({int(r["bits"]) for r in data if r["implementation"] in ("FloatLib", "MPFR")})
    figure, axes = panels(2, 3, 5.6, sharex=True, sharey=True)
    rows, present = [], []
    for index, (axis, op) in enumerate(zip(axes.flat, ops)):
        for implementation, key, label in keys:
            points = sorted((int(r["bits"]), number(r["nanoseconds"])) for r in data
                            if r["operation"] == op and r["implementation"] == implementation)
            points = [(x, y) for x, y in points if y]
            if not points:
                continue
            if (key, label) not in present:
                present.append((key, label))
            lone = key == "other"
            axis.plot([x for x, _ in points], [y for _, y in points],
                      zorder={"now": 4, "written": 5}.get(key, 2),
                      **{**style(key), **({"linestyle": "none"} if lone else {})})
            rows += [[op, implementation, x, y] for x, y in points]
        width_axis(axis, widths)
        panel_title(axis, index, BASIC_NAMES[op])
    unit = time_axis(axes.flat, base=1e-9)
    axis_labels(figure, "format width (bits)", f"time per operation ({unit})")
    legend_below(figure, [handle(key, label, line=key != "other") for key, label in present], columns=3)
    save(ctx, figure, "compiled-precision",
         "Six panels of lines, one per arithmetic operation: compiled time per operation against format "
         "width for FloatLib and MPFR up to 4,096 bits, with SoftFloat, the host processor and "
         "FloatLib's public calls as short series at 32 and 64 bits, where the public calls lie below "
         "the FloatLib line in every panel.",
         "Time per operation against format width, both on logarithmic scales. In the comparison "
         "with MPFR, SoftFloat and the host processor, each result selects the next input. "
         + where(prov) + " The open circles show public FloatLib calls at 32 and 64 bits, timed "
         "on a fixed cycle of inputs (median of nine trials on one pinned core, Lean 4.35.0, 2026-10-31).",
         "The harness is `benchmarks/scripts/format-comparison.sh`: one development trial per cell, "
         "calibrated loops of about 200 ms, MPFR 4.1.0 and SoftFloat 3e. FloatLib's operations are proved "
         "and run in software; the host processor's own arithmetic is the unproved reference. The public "
         "calls are the `binary` arm of the public-call campaign "
         "(`benchmarks/results/public-binary/measurements.csv`, commit `8c88715`), whose loop feeds each "
         "result into a checksum, so the two FloatLib series come from two harnesses and two days. "
         + sources("the FloatLib times (`IO.monoNanosNow` in the benchmark executable)",
                   "the MPFR, SoftFloat and host times (C programs in the same run) and the medians of "
                   "the public calls"),
         ["operation", "implementation: FloatLib (this harness), FloatLib public call (the public-call "
          "campaign), MPFR, SoftFloat or native FPU", "bits: storage width",
          "nanoseconds: time per operation"], rows, [path, calls],
         "python3 benchmarks/plots/figures.py time RAW --only compiled-comparison")


def status_class(status: str) -> str:
    s = (status or "").lower()
    if s in ("proved", "matched", "bounded"):
        return "done"
    if "not_run" in s or s == "":
        return "not run"
    if "translation" in s or "capability" in s:
        return "not expressible"
    return "failed"


STATUS_STYLE = OrderedDict([("done", (BLUE, None)), ("failed", (GREY_DARK, None)),
                            ("not expressible", (GREY_LIGHT, "//")), ("not run", (GREY_PALE, None))])
# BLUE is FloatLib's colour in the guide's map as well; `fig_*` use it for marks of FloatLib alone.


def status_bars(axis, labels, counts) -> list:
    """Horizontal segmented bars of case counts by outcome; returns table rows."""
    rows = []
    for index, label in enumerate(labels):
        left = 0
        for name, (color, hatch) in STATUS_STYLE.items():
            value = counts[label].get(name, 0)
            if value:
                axis.barh(index, value, left=left, height=0.5, color=color, hatch=hatch,
                          edgecolor="white", linewidth=0.8)
                left += value
            rows.append([label, name, value])
    rows_axis(axis, labels)
    return rows


def rows_axis(axis, labels, show: bool = True) -> None:
    """One row per label, the first on top, with the same limits in every panel of a figure."""
    axis.set_yticks(range(len(labels)))
    axis.set_yticklabels(labels if show else [])
    axis.set_ylim(len(labels) - 0.5, -0.75)
    axis.grid(True, axis="x")
    axis.grid(False, axis="y")
    axis.tick_params(axis="y", length=0)


def status_legend(figure, counts, done: str, failed: str = "not proved",
                  inexpressible: str = "not translated", more=(), columns: int = 3) -> None:
    """A legend entry for every outcome that occurs in `counts`, then the handles in `more`."""
    names = {"done": done, "failed": failed, "not expressible": inexpressible, "not run": "not run"}
    present = {name for counter in counts.values() for name, value in counter.items() if value}
    handles = [Patch(facecolor=c, hatch=h, edgecolor="white", label=names[n])
               for n, (c, h) in STATUS_STYLE.items() if n in present]
    legend_below(figure, handles + list(more), columns=columns)


def strip(axis, index: int, values) -> None:
    """One row of a strip plot: a dot per value, and a tick at the median of three values or more."""
    axis.plot(values, [index] * len(values), linestyle="none", marker="o", color=BLUE, alpha=0.45,
              markersize=4.5, markeredgewidth=0)
    if len(values) >= 3:
        middle = statistics.median(values)
        axis.plot([middle, middle], [index - 0.3, index + 0.3], color=INK, linewidth=1.6)


def strip_handles(one: str) -> list:
    return [Line2D([], [], linestyle="none", marker="o", color=BLUE, alpha=0.6, markersize=4.5,
                   markeredgewidth=0, label=one),
            Line2D([], [], linestyle="none", marker="|", color=INK, markersize=11, markeredgewidth=1.6,
                   label="median")]


def suites_provenance(ctx, suite: str) -> dict:
    """Toolchain and dates of one standard suite's run (`suites/provenance.json`)."""
    path = need(ctx.results / "suites" / "provenance.json", "suites/provenance.json")
    record = json.loads(path.read_text()).get(suite, {})
    lean = re.search(r"version ([0-9.]+)", record.get("lean_version", ""))
    days = sorted({record.get("first_utc", "")[:10], record.get("last_utc", "")[:10]} - {""})
    return dict(lean="v" + lean.group(1) if lean else "", machine=ctx.measured.get("machine", machine()),
                date=" to ".join(days))


def exact_ratio(text: str):
    numerator, _, denominator = (text or "").partition("/")
    try:
        return float(numerator) / float(denominator or 1)
    except (ValueError, ZeroDivisionError):
        return None


def fig_suites_fpbench(ctx):
    """FPBench: what `roundoff` proves, and its bounds against FPTaylor and Gappa."""
    directory = ctx.results / "suites"
    path = need(directory / "fpbench.csv", "suites/fpbench.csv")
    prov = suites_provenance(ctx, "fpbench")
    counts = defaultdict(Counter)
    data = read_csv(path)
    for row in data:
        label = {"forward": "forward bound, conditional", "closed": "closed bound, conditional",
                 "backward": "backward statement"}[row["method"]]
        counts[label][status_class(row["status"])] += 1
        if row["method"] != "backward":
            numeric = row["numeric_status"]
            counts[f"{row['method']} bound, numerical"][
                "done" if numeric == "proved" else "not expressible" if numeric == "translation_refusal"
                else "failed"] += 1
    labels = [l for l in ("forward bound, conditional", "forward bound, numerical",
                          "closed bound, conditional", "closed bound, numerical", "backward statement")
              if l in counts]
    compare = directory / "fpbench-comparison.csv"
    ratios, inputs = OrderedDict(), [path]                 # drawn label -> (name in the CSV, values)
    if compare.exists():
        inputs.append(compare)
        joined = read_csv(compare)
        for tool, label, name in (("fptaylor", "FPTaylor 0.9.4", "FPTaylor 0.9.4, same export"),
                                  ("gappa", "Gappa 1.8.3", "Gappa 1.8.3, same export")):
            values = [v for row in joined for method in ("forward", "closed")
                      for v in [exact_ratio(row.get(f"{method}_{tool}_bound_ratio"))] if v]
            if values:
                ratios[label] = (name, values)
        published = []
        for row in joined:
            for method in ("forward", "closed"):
                for record in json.loads(row.get(f"{method}_fptaylor_published_ratios") or "[]"):
                    value = exact_ratio(record.get("bound_ratio"))
                    if value:
                        published.append(value)
        if published:
            ratios["FPTaylor, published"] = ("FPTaylor, published bounds", published)
    figure, axes = panels(1, 2 if ratios else 1, 0.42 * len(labels) + 2.0)
    rows = status_bars(axes[0][0], labels, counts)
    axes[0][0].set_xlabel("number of programs")
    count_axis(axes[0][0])
    if ratios:
        panel_title(axes[0][0], 0, "theorems")
        axis = axes[0][1]
        for index, (name, values) in enumerate(ratios.values()):
            strip(axis, index, values)
            rows += [[f"ratio to {name}", "bound ratio", v] for v in values]
        axis.axvline(1.0, color=MUTED, linewidth=0.9)
        log_axis(axis, "x")
        axis.set_yticks(range(len(ratios)))
        axis.set_yticklabels(list(ratios))
        axis.set_ylim(len(ratios) - 0.5, -0.75)
        axis.set_xlabel("bound ratio, FloatLib to tool")
        panel_title(axis, 1, "bound ratios")
        axis.grid(True, axis="x")
        axis.grid(False, axis="y")
        axis.tick_params(axis="y", length=0)
    status_legend(figure, counts, "proved", more=strip_handles("one program") if ratios else ())
    proved = lambda label: counts[label]["done"]
    medians = ", ".join(f"{label} {plain(float(f'{statistics.median(values):.3g}'))} over {len(values)} ratios"
                        if len(values) >= 3 else f"{label} {len(values)} ratios, no median drawn"
                        for label, (_, values) in ratios.items())
    save(ctx, figure, "suites-fpbench",
         ("Two panels. Left: five stacked horizontal bars, one per kind of theorem, split into programs "
          "proved, not proved and not translated. Right: three rows of dots on a logarithmic axis, one "
          "dot per program for the ratio of FloatLib's bound to another tool's, with a tick at the "
          "median of a row that has three ratios or more, and a vertical line at ratio one." if ratios else
          "Five stacked horizontal bars, one per kind of theorem, split into programs proved, not proved "
          "and not translated."),
         "FPBench: what FloatLib's roundoff tactic proves"
         + (", and its proved bounds against FPTaylor and Gappa. " if ratios else ". ")
         + "Panel (a) counts the 136 programs of twelve FPBench suite files, each in binary32 and in "
         "binary64, by outcome for each kind of theorem"
         + ("; panel (b) is FloatLib's proved numerical bound divided by the other tool's bound on the "
            "same program, on a logarithmic axis where 1 is equal and above 1 is looser. " if ratios else ". ")
         + where(prov),
         "Each program is translated to a Lean program and given to `roundoff` once per kind of theorem. A "
         "conditional theorem keeps its premises; a numerical bound is a second Lean proof that "
         "discharges them on the program's input box and proves one proposed bound (an untrusted estimate "
         "rounded up to a power of two, with no search for a tighter one). Conditional theorems proved: "
         f"{proved('forward bound, conditional')} forward, {proved('closed bound, conditional')} closed, "
         f"{proved('backward statement')} backward; numerical bounds: "
         f"{proved('forward bound, numerical')} forward, {proved('closed bound, numerical')} closed. Not "
         "proved means refused or over the time limit. "
         + (f"Panel (b) has one dot per program, precision and method, only where the two statements "
            f"bound the same thing (medians: {medians}); FPTaylor 0.9.4 and Gappa 1.8.3 ran on the same "
            "exported program, and the last row uses the bounds FPTaylor's regression files publish. "
            "Daisy's ratios are withheld (its literals pass through binary64). " if ratios else
            "No ratio to another tool can be drawn without a proved numerical bound. ")
         + "Every Lean process had 60 seconds and 4 GB, eight at a time. "
         + sources("every proof, its axioms and its time",
                   "the translation, the other tools' bounds (FPTaylor, Gappa, run on 2026-11-16; they "
                   "do not depend on FloatLib) and the ratios"),
         ["row: kind of theorem, or `ratio to TOOL`", "outcome_or_measure: `done` (proved), `failed`, "
          "`not expressible` (the translator refuses the program), or `bound ratio`",
          "value: number of programs, or FloatLib's bound over the tool's"], rows, inputs,
         "benchmarks/suites/run.sh fpbench, then benchmarks/suites/summarize.py (not part of the timing mode)")


def fig_suites_inequalities(ctx):
    """MetiTarski and Flyspeck inequalities: goals closed by `interval`, with and without the constraint engine."""
    path = need(ctx.results / "suites" / "inequalities.csv", "suites/inequalities.csv")
    prov = suites_provenance(ctx, "inequalities")
    counts, elapsed = OrderedDict(), defaultdict(list)
    names = {"metitarski": "MetiTarski", "flyspeck": "Flyspeck"}
    routes = {"interval": "interval", "constraint": "interval, constraint engine"}
    for suite in names:
        for route in routes:
            counts[f"{names[suite]}: {routes[route]}"] = Counter()
    for row in read_csv(path):
        suite = "flyspeck" if row["suite"].startswith("flyspeck") else row["suite"]
        label = f"{names[suite]}: {routes[row['method']]}"
        counts[label][status_class(row["status"])] += 1
        if row["status"] == "proved" and number(row["elapsed_ms"]):
            elapsed[label].append(float(row["elapsed_ms"]) / 1e3)
    labels = [l for l in counts if counts[l]]
    figure, axes = panels(1, 2, 0.55 * len(labels) + 2.0)
    rows = status_bars(axes[0][0], labels, counts)
    axes[0][0].set_xlabel("number of goals")
    count_axis(axes[0][0])
    panel_title(axes[0][0], 0, "goals")
    axis = axes[0][1]
    for index, label in enumerate(labels):
        if elapsed[label]:
            strip(axis, index, elapsed[label])
            rows += [[label, "seconds", t] for t in elapsed[label]]
    unit = time_axis([axis], "x", base=1.0) if any(elapsed.values()) else "s"
    rows_axis(axis, labels, show=False)
    axis.set_xlabel(f"elaboration time ({unit})")
    panel_title(axis, 1, "time per proved goal")
    status_legend(figure, counts, "proved", more=strip_handles("one proved goal"))
    proved = lambda label: counts[label]["done"]
    save(ctx, figure, "suites-inequalities",
         "Two panels with the same four rows, MetiTarski and Flyspeck each with interval alone and with "
         "the constraint engine. Left: stacked horizontal bars of goals proved, not proved and not "
         "translated. Right: one dot per proved goal on a logarithmic time axis, with a tick at the "
         "median of a row that has three goals or more.",
         "MetiTarski and Flyspeck inequalities given to FloatLib's interval tactic, alone and "
         "with the constraint engine. Panel (a) counts the goals by outcome (948 MetiTarski goals and 164 "
         "Flyspeck records, one tactic call each); panel (b) is the time Lean took to elaborate each "
         "proved goal, without the imports of its file, on a logarithmic axis where lower is faster. "
         + where(prov),
         "The Flyspeck records are 153 nonlinear inequalities and eleven examples. Each goal is translated "
         "to one Lean goal and given to `interval` once with `FloatLib.Tactic.Interval` alone (boxes and "
         "coefficients), and once with the constraint engine imported as well "
         "(`FloatLib.Tactic.Interval.Constraints`), which is `interval` as `import FloatLib` provides it. "
         f"MetiTarski: {proved('MetiTarski: interval')} proved by `interval`, "
         f"{proved('MetiTarski: interval, constraint engine')} with the constraint engine; Flyspeck: "
         f"{proved('Flyspeck: interval')} and {proved('Flyspeck: interval, constraint engine')}. Not "
         "proved means refused, over the limits, or out of memory. Every Lean process had 20 seconds and "
         "4 GB, eight at a time. The published times of MetiTarski, dReal and HOL Light are for other "
         "statements or other machines and are in the suite's README, not in this figure. "
         + sources("every proof, its axioms and its time", "the translation and the counts"),
         ["source: suite and route", "outcome_or_measure: `done` (proved), `failed`, `not expressible` "
          "(not translated), or `seconds`", "value: number of goals, or the seconds of one proved goal"],
         rows, [path],
         "benchmarks/suites/run.sh inequalities, then benchmarks/suites/summarize.py (not part of the timing mode)")


def fig_suites_hard_cases(ctx):
    """Hard-to-round inputs: FloatLib's correctly rounded functions against MPFR and CORE-MATH."""
    path = need(ctx.results / "suites" / "correct-rounding.csv", "suites/correct-rounding.csv")
    prov = suites_provenance(ctx, "correct-rounding")
    short = {"CORE-MATH": "CORE-MATH worst cases", "Lefèvre testlibm": "Lefèvre's hard cases",
             "CORE-MATH binary32 exhaustive input screen": "binary32 screen"}
    counts, elapsed, apart = OrderedDict(), defaultdict(dict), Counter()
    for row in read_csv(path):
        label = f"{row['domain']} {row['operation']}, binary{row['width']}, {short.get(row['source'], row['source'])}"
        counts.setdefault(label, Counter())[
            "done" if row["status"] == "matched" else "not expressible"] += int(row["cases"])
        if row["status"] != "matched":
            apart["unrepresentable" if row["status"] == "translation_refusal" else "left out"] += int(row["cases"])
        if row["status"] == "matched":
            for column, key in (("median_ns", "now"), ("mpfr_median_ns", "mpfr"),
                                ("core_math_median_ns", "other")):
                if number(row[column]):
                    elapsed[label][key] = float(row[column]) / 1e3
    labels = sorted(counts, key=lambda l: (l.split(" ")[0] != "real", l))
    figure, axes = panels(1, 2, 0.29 * len(labels) + 2.0)
    rows = status_bars(axes[0][0], labels, counts)
    axes[0][0].set_xlabel("number of inputs")
    count_axis(axes[0][0], ticks=3)
    panel_title(axes[0][0], 0, "inputs")
    axis = axes[0][1]
    for index, label in enumerate(labels):
        for key in ("now", "mpfr", "other"):
            value = elapsed[label].get(key)
            if value:
                axis.plot([value], [index], zorder=3, **{**style(key), "linestyle": "none"})
                rows.append([label, f"median_us_{key}", value])
    unit = time_axis([axis], "x") if any(elapsed.values()) else "µs"
    rows_axis(axis, labels, show=False)
    axis.set_xlabel(f"median time per call ({unit})")
    panel_title(axis, 1, "time per call")
    status_legend(figure, counts, "equal to the reference", inexpressible="not compared",
                  more=[handle("now", NOW, line=False), handle("mpfr", MPFR_NAME, line=False),
                        handle("other", "CORE-MATH", line=False)], columns=3)
    matched = lambda domain: sum(c["done"] for l, c in counts.items() if l.startswith(domain))
    save(ctx, figure, "suites-hard-cases",
         f"Two panels with the same {len(labels)} rows, one per function, format and source of inputs. "
         "Left: horizontal bars of the number of inputs whose result equals the reference. Right: the "
         "median time per call on a logarithmic axis, a filled circle for FloatLib, a diamond for "
         "MPFR and a grey cross for CORE-MATH; the complex rows have the FloatLib mark only.",
         "Hard-to-round inputs of exp, expm1, log and log1p: the results of FloatLib against MPFR, "
         "CORE-MATH and GNU MPC, and the time per call. Panel (a) counts the inputs whose result word "
         f"from FloatLib equals the reference ({matched('real'):,} real results and "
         f"{matched('complex'):,} parts of complex results, a complex input counting once per part); "
         "panel (b) is the median time of one compiled call, on a logarithmic axis where lower is faster. "
         "These are tests on listed inputs, not proofs. " + where(prov),
         "The inputs, rounded to nearest even, are 16,384 sampled worst cases per function from CORE-MATH, "
         "Lefèvre's `testlibm` and `hrcases` data, and 256 binary32 inputs per function from a screen of "
         "all 2^32 encodings. The real results are compared with MPFR and CORE-MATH, which must agree with "
         "each other first; the complex results at `z = x + i x` with GNU MPC. "
         + (f"{sum(apart.values()):,} inputs are not compared: " + " and ".join(
             ([f"{apart['unrepresentable']:,} whose input or result the format cannot represent"]
              if apart["unrepresentable"] else [])
             + ([f"{apart['left out']:,} that the suite leaves out (complex inputs at the origin, where "
                 "the comparison with MPC does not apply)"] if apart["left out"] else [])) + ". "
            if apart else "") + "MPFR and CORE-MATH do not "
         "prove their rounding in Lean, and CORE-MATH works in binary64 arithmetic. "
         + sources("FloatLib's result words and times (compiled Lean)",
                   "the reference results and times (MPFR, CORE-MATH, MPC) and the comparison"),
         ["case: domain, function, format and source", "outcome_or_measure: `done` (matches), "
          "`not expressible` (not compared: not representable, or left out by the suite), or `median_us_now` "
          "(FloatLib), `median_us_mpfr`, `median_us_other` (CORE-MATH)",
          "value: number of inputs, or microseconds"], rows, [path],
         "benchmarks/suites/run.sh correct-rounding, then benchmarks/suites/summarize.py (not part of the timing mode)")


def fig_suites_testfloat(ctx):
    """Berkeley TestFloat: campaigns run and vectors matched, by format."""
    path = need(ctx.results / "suites" / "testfloat.csv", "suites/testfloat.csv")
    prov = suites_provenance(ctx, "testfloat")
    names = {"f16": "binary16", "f32": "binary32", "f64": "binary64", "f128": "binary128",
             "bf16": "bfloat16"}
    counts, vectors, wrong, seconds_ = defaultdict(Counter), Counter(), Counter(), Counter()
    for row in read_csv(path):
        label = names.get(row["format"], row["format"])
        counts[label][status_class(row.get("status"))] += 1
        vectors[label] += int(number(row.get("cases")) or 0)
        wrong[label] += int((number(row.get("value_mismatches")) or 0)
                            + (number(row.get("flag_mismatches")) or 0))
        seconds_[label] += number(row.get("lean_check_seconds")) or 0
    labels = [n for n in names.values() if n in counts] + sorted(set(counts) - set(names.values()))
    figure, axes = panels(1, 2, 0.46 * len(labels) + 1.9)
    rows = status_bars(axes[0][0], labels, counts)
    axes[0][0].set_xlabel("number of campaigns")
    panel_title(axes[0][0], 0, "campaigns")
    axis = axes[0][1]
    for index, label in enumerate(labels):
        axis.barh(index, vectors[label] / 1e6, height=0.5, color=BLUE, edgecolor="white", linewidth=0.8)
        rows += [[label, "vectors", vectors[label]], [label, "mismatches", wrong[label]],
                 [label, "check_seconds", round(seconds_[label], 1)]]
    rows_axis(axis, labels, show=False)
    axis.set_xlabel("vectors checked (millions)")
    panel_title(axis, 1, "vectors")
    status_legend(figure, counts, "every vector matches", failed="a mismatch, or not finished",
                  inexpressible="no such campaign")
    total = sum(sum(c.values()) for c in counts.values())
    done = sum(c["done"] for c in counts.values())
    save(ctx, figure, "suites-testfloat",
         f"Two panels of horizontal bars with one row per format ({', '.join(labels)}). Left: the number "
         "of TestFloat campaigns, all in the colour of a campaign in which every vector matches. Right: "
         "the number of vectors checked, in millions.",
         f"Berkeley TestFloat, level 1: the campaigns FloatLib matches and the vectors they check, "
         f"by format. Panel (a) counts the {total} campaigns, one per operation and rounding direction in "
         f"each format, of which {done} match on every vector in value and in status flags; panel (b) is "
         f"the number of vectors of those campaigns, {sum(vectors.values()):,} in all with "
         f"{sum(wrong.values()):,} mismatches. A finite campaign is not a proof. " + where(prov),
         "The vectors are generated by TestFloat (seed 1) with SoftFloat as its reference and checked by a "
         "compiled Lean program on FloatLib's `logicalModel`. A campaign of the fused multiply-add has "
         "6,133,248 vectors. The CSV also has the seconds the compiled check took, summed over the "
         "campaigns of a format. "
         + sources("the comparison of each vector (compiled Lean)",
                   "the vectors (TestFloat's generator) and the counts"),
         ["format", "outcome_or_measure: `done` (campaigns that match), `failed`, `vectors`, "
          "`mismatches` or `check_seconds` (compiled Lean, summed over the campaigns)",
          "value"], rows, [path],
         "benchmarks/suites/run.sh testfloat, then benchmarks/suites/summarize.py (not part of the timing mode)")


def checker_files() -> list:
    """The CSV files of independent-checker times under `benchmarks/kernel/`."""
    return sorted(path for path in (ROOT / "benchmarks" / "kernel").glob("*.csv"))


def fig_kernel_checkers(ctx):
    """Independent kernel checkers on the kernel layer and the kernel benchmarks."""
    files = checker_files()
    if not files:
        raise Missing("a CSV of the independent checkers' times under benchmarks/kernel/ "
                      "(columns: one naming the checker, one naming what was checked, one with seconds)")
    data = [row for path in files for row in read_csv(path)]
    columns = list(data[0].keys())

    def column(*words, skip=()):
        return next((c for c in columns if c not in skip and any(w in c.lower() for w in words)), None)

    who = column("checker", "kernel", "tool")
    what = column("family", "target", "suite", "module", "what", "input", skip=(who,))
    seconds_ = column("seconds", "wall", "time")
    net = column("net")
    status = column("status", "result", "outcome", "accept", "exit")
    if not who or not seconds_:
        raise Missing(f"a checker column and a seconds column in {relative(files[0])} (found {columns})")
    checkers = list(OrderedDict.fromkeys(r[who] for r in data))
    targets = list(OrderedDict.fromkeys(r[what] for r in data)) if what else ["all"]
    cols = min(3, len(targets))
    grid_rows = math.ceil(len(targets) / cols)
    figure, axes = panels(grid_rows, cols, (0.3 * len(checkers) + 0.75) * grid_rows + 0.8, sharey=True)
    rows, refused = [], []
    for position, (axis, target) in enumerate(zip(axes.flat, targets)):
        for index, checker in enumerate(checkers):
            row = next((r for r in data if r[who] == checker and (not what or r[what] == target)), None)
            total = number(row[seconds_]) if row else None
            extra = number(row[net]) if row and net else None
            verdict = (row.get(status, "") if row and status else "")
            accepted = verdict.lower() in ("accepted", "ok", "pass", "passed", "0", "")
            if total:
                axis.barh(index, total, height=0.62, edgecolor="white",
                          **(dict(color=BLUE) if accepted else dict(color=GREY_LIGHT, hatch="//")))
                axis.text(total, index, f" {total:,.1f}", va="center",
                          fontsize=small(), color=INK)
            if row and not accepted:
                refused.append(f"`{checker}` on `{target}`: {verdict}")
            rows.append([target, checker, verdict, total, extra])
        panel_title(axis, position, target)
        axis.margins(x=0.3)
        axis.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:,.0f}"))
        rows_axis(axis, checkers)                       # the panels share their rows
        axis.tick_params(labelleft=position % cols == 0)
    for axis in list(axes.flat)[len(targets):]:
        axis.axis("off")
    axis_labels(figure, "time per check (s)")
    handles = [Patch(facecolor=BLUE, label="accepted")]
    if refused:
        handles.append(Patch(facecolor=GREY_LIGHT, hatch="//", edgecolor="white", label="no verdict"))
    legend_below(figure, handles)
    save(ctx, figure, "kernel-checkers",
         f"{len(targets)} panels of horizontal bars, one panel per family of proofs and one bar per "
         "checker, each bar ending in its time in seconds; a hatched grey bar is a run that ended "
         "without a verdict.",
         "Time the independent checkers of Lean proofs take on the kernel proofs of FloatLib, by "
         "family of proofs. A bar is the time of one check of a family with everything it imports, and a "
         "hatched bar is a run that ended without a verdict, at the time it stopped. The checkers ran "
         "once, and the timing mode does not run them again.",
         f"The numbers are those of `{relative(files[0])}`; the README "
         "section next to that file says how each checker was run and what a rejection means. " + ("Runs without a verdict: " + "; ".join(refused) + ". " if refused else
                      "Every run ended with the family accepted. ")
         + "The CSV also has the time net of the same imports without the family's theorems, where the "
         "input has it. From Lean: nothing. From scripts: every time (each checker's own run).",
         [f"family: column `{what}` of the input", f"checker: column `{who}`",
          f"verdict: column `{status}`", f"seconds: column `{seconds_}`, imports included",
          f"net_seconds: column `{net}`, the same minus a run on the imports alone"],
         rows, files)


FIGURES = OrderedDict([
    ("kernel-binary", fig_kernel_binary),
    ("kernel-operands", fig_kernel_operands),
    ("kernel-ieee2019", fig_kernel_ieee2019),
    ("kernel-extras", fig_kernel_extras),
    ("kernel-vs-coq", fig_kernel_vs_coq),
    ("kernel-loops", fig_kernel_loops),
    ("kernel-families", fig_kernel_families),
    ("kernel-all-pairs", fig_kernel_all_pairs),
    ("kernel-exact-operations", fig_kernel_exact_operations),
    ("kernel-exact-library", fig_kernel_exact_library),
    ("kernel-exact-native", fig_kernel_exact_native),
    ("kernel-checkers", fig_kernel_checkers),
    ("interval-corpora", fig_interval_corpora),
    ("correctly-rounded", fig_correctly_rounded),
    ("compiled-precision", fig_compiled_precision),
    ("suites-fpbench", fig_suites_fpbench),
    ("suites-inequalities", fig_suites_inequalities),
    ("suites-hard-cases", fig_suites_hard_cases),
    ("suites-testfloat", fig_suites_testfloat),
])

# The result READMEs that show figures, each numbering its own from Figure 1.
README_FIGURES = OrderedDict([
    ("kernel/README.md", ["kernel-binary", "kernel-operands", "kernel-extras", "kernel-loops",
                          "kernel-checkers"]),
    ("backends/README.md", ["kernel-vs-coq", "kernel-families", "kernel-all-pairs", "compiled-precision"]),
    ("ieee2019/README.md", ["kernel-ieee2019", "correctly-rounded"]),
    ("suites/README.md", ["suites-fpbench", "suites-inequalities", "suites-hard-cases",
                          "suites-testfloat"]),
])
README_BEGIN = "<!-- figures: this section is written by benchmarks/plots/figures.py draw -->"
README_END = "<!-- end of figures -->"


# The guide's figure that a script of this directory draws (`flocq_matched.py`). It is not one of
# the numbered figures above: the chapter that shows it numbers and captions it. The entry here
# gives the chapter its alt text and caption, and says what the drawing no longer carries.
GUIDE_ASSETS = ROOT / "site" / "content" / "assets"
FLOCQ_MATCHED = dict(
    name="flocq-matched",
    alt="Six panels, one per arithmetic operation: time per operation against format width, both on "
        "logarithmic axes, with one line each for FloatLib, extracted Flocq and MPFR at eleven matching "
        "binary formats from 6 to 4,096 bits.",
    caption="Time of one arithmetic operation in FloatLib, in Flocq 4.2.2 extracted to OCaml and in MPFR, "
            "at eleven matching binary formats from 6 to 4,096 bits. A point is the median over nine "
            "trials of the time per operation in nanoseconds, with the precision and the exponent bounds "
            "matched across the three; square root at 1,024 bits and above is timed over complete blocks "
            "of sixteen inputs. Both axes are logarithmic, and lower is faster. Measured on 2026-10-31 "
            "on an Intel Xeon Platinum 8275CL with Lean 4.35.0.",
    notes="Drawn by `benchmarks/plots/flocq_matched.py` from "
          "`benchmarks/results/flocq-matched/matched-benchmark-summary.csv` after it verifies the retained "
          "archive; `figures.py draw` redraws it into `site/content/assets/` (the overview, one view per "
          "operation and the selector `flocq-matched-series.json`). The measured code is FloatLib at "
          "commit `8c88715`, with Flocq 4.2.2 extracted by Coq 8.20.1 and compiled by OCaml 4.13.1, and "
          "MPFR 4.1.0; `benchmarks/results/flocq-matched/README.md` has the method: medians of nine "
          "trials, matching precision and exponent bounds, a result-dependent chain of inputs, and "
          "complete blocks of sixteen inputs for square root at 1,024 bits and above. From Lean: the "
          "FloatLib times. From scripts: the Flocq and MPFR times and the medians.")


def draw_guide_figure() -> bool:
    """Redraw the guide's matched Flocq comparison with the current style. Returns whether it did."""
    import flocq_matched

    try:
        rows = flocq_matched.verify(flocq_matched.RESULTS)
    except (ValueError, OSError) as error:
        print(f"  {FLOCQ_MATCHED['name']}: not drawn, {error}")
        return False
    flocq_matched.plot(rows, GUIDE_ASSETS / f"{FLOCQ_MATCHED['name']}.png")
    print(f"  {FLOCQ_MATCHED['name']}: the guide's figure, in {relative(GUIDE_ASSETS)}")
    return True


def refresh_guide_copies(ctx: Context) -> list:
    """Copy each drawn figure over the copy of the same name that the guide shows, if it has one."""
    copied = []
    for name in ctx.index:
        target = GUIDE_ASSETS / f"{name}.png"
        if target.is_file():
            shutil.copyfile(ctx.out / f"{name}.png", target)
            copied.append(name)
    return copied


# ---- FIGURES.md --------------------------------------------------------------------------------

def figure_number(name: str) -> int:
    """The number of a figure in FIGURES.md: its place in `FIGURES`, drawn or not."""
    return list(FIGURES).index(name) + 1


def ref(*names) -> str:
    return ", ".join(f"Figure {figure_number(name)} (`{name}`)" for name in names)


def figure_block(entry: dict, number: int, directory: str) -> list:
    """A figure as Markdown: the image, whose title is the caption, and the numbered caption."""
    name = entry["name"]
    return [f"![{entry['alt']}]({directory}{name}.png \"{entry['caption']}\")", "",
            f"**Figure {number}.** {entry['caption']}", ""]


def write_index(ctx: Context, skipped: list, guide: bool = False) -> None:
    m = ctx.measured
    lines = [
        "# Figures", "",
        "Written by `benchmarks/plots/figures.py draw`; do not edit by hand. Every figure is in "
        "`figures/` as `NAME.png` (for the site, 9 inches wide at 200 dpi), `NAME.pdf` (vector) and "
        "`NAME.csv` (the numbers that are drawn, one row per mark).", "",
        "The figures follow the figure rules of the library: an image holds only the plot, its axes "
        "with units, a legend with short series names and panel letters. Everything else is in the "
        "entry of the figure below: its **caption** (what the figure shows, what was measured and in "
        "which unit, the scales, the machine and the toolchain), which is the title of the "
        "Markdown image and is what the guide prints under the figure; its **alt text**, which "
        "describes the image; and its **notes** (how it was measured, where a recorded number comes "
        "from, which numbers come from Lean and which from scripts).", "",
        "| figure | name | shows |", "| --- | --- | --- |"]
    missing = dict(skipped)
    for name in FIGURES:
        shows = (ctx.index[name]["caption"].split(". ")[0] + "." if name in ctx.index
                 else "not drawn: its input is missing")
        lines.append(f"| Figure {figure_number(name)} | `{name}` | {shows} |")
    lines += [
        "", "## How the numbers were made", "",
        "```bash",
        "python3 benchmarks/plots/figures.py time RAW     # measure this checkout, write the results, draw",
        "python3 benchmarks/plots/figures.py draw         # draw again from the result files",
        "```", "",
        "`RAW` is a directory outside the checkout for the logs. The library has to be built "
        "(`FLOATLIB_BUILD_DIR`, or `.lake/build`); the timing mode links the benchmark executables it "
        "starts and builds nothing else. It runs the runners under `benchmarks/kernel/`, "
        "`benchmarks/suite/`, `benchmarks/exact/` and `benchmarks/scripts/`: the kernel sections one "
        "at a time, because another job on the machine disturbs their cells, and then the others at "
        "most eight at a time. On Linux with core scheduling a measuring process has its cores to "
        "itself, the rows of 1,024 and 4,096 bits of the IEEE table excepted, which run eight at a "
        "time: a job on the second hardware thread of a core makes a measurement on the first 1.5 "
        "to 2 times slower. Those runners print every time (`Lean.Kernel.whnf`, Lean's profiler, "
        "`IO.monoNanosNow`, `/usr/bin/time`). Python starts them, copies their tables and draws.", "",
    ]
    if m:
        state = " with uncommitted changes to tracked files" if m.get("dirty") else ""
        sections = m.get("sections", {})
        # A record names its commit when the run that wrote it did; the column exists only then.
        named = any(entry.get("short") for entry in sections.values())
        subject = commit_of(dict(short=m.get("commit")), "measured commit ", f"{state} with") or "used"

        def at_a_time(count) -> str:
            return "one section at a time" if count == 1 else f"{count} sections at a time"

        # The runs that still have a section: a run with `--only` measures some sections again.
        runs = [entry for entry in m.get("runs", [])
                if any(s.get("started_utc") == entry["started_utc"] for s in sections.values())]
        if len(runs) > 1:
            parts = []
            for entry in runs:
                own = [name for name, s in sections.items() if s.get("started_utc") == entry["started_utc"]]
                parts.append(f"started {entry['started_utc']}, {at_a_time(entry['jobs'])}, "
                             f"{float(entry['seconds']) / 60:.0f} minutes of wall time: "
                             + ", ".join(f"`{name}`" for name in own))
            lines += [
                f"The timing mode {subject} Lean {m.get('lean', '')} on {m.get('machine', '')}, in "
                f"{len(runs)} runs with {m.get('threads', '')} threads in all. " + " ".join(
                    f"Run {index}, {part}." for index, part in enumerate(parts, 1))
                + " A section that is measured again replaces its earlier files.", ""]
        else:
            lines += [
                f"The last timing run {subject} Lean "
                f"{m.get('lean', '')} on {m.get('machine', '')}, started {m.get('started_utc', '')}, "
                f"{at_a_time(m.get('jobs', ''))} with {m.get('threads', '')} threads in all, "
                f"{float(m.get('seconds', 0)) / 60:.0f} minutes of wall time.", ""]
        lines += [
            "| section | exit | seconds | rows | Lean errors in its logs |" + (" commit |" if named else ""),
            "| --- | ---: | ---: | ---: | ---: |" + (" --- |" if named else "")]
        for name, entry in sections.items():
            lines.append(f"| `{name}` | {entry.get('exit', '')} | {float(entry.get('seconds', 0)):.0f} "
                         f"| {entry.get('rows', '')} | {entry.get('errors', 0)} |"
                         + (f" `{entry.get('short', '')}` |" if named else ""))
        lines.append("")
    lines += [
        "Not measured by the timing mode, and where it comes from:", "",
        f"- **Coq.** {COQ}. These times do not depend on FloatLib's commit.",
        "- **Counts.** Proofs accepted, bounds, vectors matched and goals closed are correctness "
        "results from the recorded suite runs.", "",
        "The recorded files are in `figures/recorded/`, and `figures/recorded/README.md` says where each "
        "came from.", "",
        "## Kernel features and where their numbers are", "",
        "| feature | figure, and the table behind it |", "| --- | --- |",
        "| `float_decide` and the binary kernel path (`KernelPath.Value.*`) | "
        + ref("kernel-binary", "kernel-operands", "kernel-extras", "kernel-loops", "kernel-vs-coq")
        + "; `kernel/README.md` |",
        "| the rules tagged `@[kernel_optimize]`, family by family | "
        + ref("kernel-ieee2019", "kernel-families", "kernel-extras")
        + "; `ieee2019/README.md`, `backends/README.md` |",
        "| `#kernel_cost` | the command that measures " + ref("kernel-families") + " and the Lean side of "
        + ref("kernel-vs-coq") + " |",
        "| `lane_decide`, lane tables and packed rows | " + ref("kernel-all-pairs") + " (its `add-table` "
        "row is the kernel check of one packed table), " + ref("kernel-exact-native")
        + " (a packed row product) |",
        "| `Z`, `Signed` | " + ref("kernel-exact-operations") + "; `exact/operations.md`, section `int` |",
        "| `Q`, `Frac` | " + ref("kernel-exact-operations") + "; section `rat` |",
        "| `Bits` (`size`, `testBit`, `popCount`), `Root` (`isqrt`, `isRoot`) | "
        + ref("kernel-exact-operations") + "; section `nat` |",
        "| `Dyad`, `Ball` | " + ref("kernel-exact-operations") + "; sections `dyad` and `ball` |",
        "| `CBall`, `CFix` | " + ref("kernel-exact-operations") + " (complex ball product); section "
        "`complex` |",
        "| `Seq`, and the cover check of `Multiplicative` | " + ref("kernel-exact-operations")
        + " (lists of 256); section `list` |",
        "| `Bisection`, `Strict` | `exact/operations.md`, section `search` |",
        "| `Mod` (`powMod`, `invMod`) | " + ref("kernel-exact-operations", "kernel-exact-native")
        + "; section `mod` |",
        "| FloatLib's own exact layer, and `interval` on it | " + ref("kernel-exact-library")
        + "; `exact/baseline.md`, `exact/tactic.md` |",
        "| independent checkers of the kernel proofs | " + ref("kernel-checkers") + " |",
        "| `kernel_twin`, `#kernel_eval`, `#kernel_rules`, `#compiler_backends`, `@[compiler_optimize]` | "
        "no runner times them: they declare or list rules and have no time of their own here |", ""]
    for name in FIGURES:
        number_ = figure_number(name)
        lines += [f"## Figure {number_}: {name}", ""]
        if name not in ctx.index:
            lines += [f"Not drawn: missing {missing.get(name, 'its input')}.", ""]
            continue
        entry = ctx.index[name]
        lines += figure_block(entry, number_, "figures/")
        lines += [f"Alt text: {entry['alt']}", "", f"Notes: {entry['notes']}", "",
                  f"Files: `figures/{name}.png`, `figures/{name}.pdf`, `figures/{name}.csv` "
                  f"({entry['rows']} rows).", "", "CSV columns:", ""]
        for column in entry["columns"]:
            head, _, meaning = column.partition(":")
            lines.append(f"- `{head.strip()}`" + (f": {meaning.strip()}" if meaning.strip() else ""))
        lines += ["", "Inputs: " + ", ".join(f"`{i}`" for i in entry["inputs"]) + "."]
        if entry["command"]:
            lines += ["", f"Measured again by: `{entry['command']}`."]
        lines.append("")
    if guide:
        entry = FLOCQ_MATCHED
        up = "../../site/content/assets/"
        lines += ["## The guide's figure drawn by a benchmark script", "",
                  f"`{entry['name']}` is a figure of the guide's performance chapter, which numbers it. The "
                  "script that draws it is in `benchmarks/plots/`, so its alt text and caption are kept "
                  "here.", "",
                  f"![{entry['alt']}]({up}{entry['name']}.png \"{entry['caption']}\")", "",
                  f"Caption: {entry['caption']}", "", f"Alt text: {entry['alt']}", "",
                  f"Notes: {entry['notes']}", ""]
    (RESULTS / "FIGURES.md").write_text("\n".join(lines), encoding="utf-8")


def write_readme_figures(ctx: Context) -> None:
    """The section `Figures` of each result README that has figures, numbered from Figure 1."""
    for readme, names in README_FIGURES.items():
        path = RESULTS / readme
        drawn = [ctx.index[name] for name in names if name in ctx.index]
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        if README_BEGIN in text:
            text = text[:text.index(README_BEGIN)]
        text = text.rstrip("\n") + "\n"      # the same file whether the tables were just written or not
        if drawn:
            lines = ["", README_BEGIN, "", "## Figures", "",
                     "The captions, alt texts, notes and CSV columns of these figures are in "
                     "[FIGURES.md](../FIGURES.md).", ""]
            for number_, entry in enumerate(drawn, start=1):
                lines += figure_block(entry, number_, "../figures/")
            text += "\n".join(lines + [README_END, ""])
        path.write_text(text, encoding="utf-8")


# ---- main --------------------------------------------------------------------------------------

def draw(only: list) -> int:
    setup()
    ctx = Context()
    unknown = set(only) - set(FIGURES)
    if unknown:
        raise SystemExit(f"no figure named {', '.join(sorted(unknown))}; see `figures.py list`")
    skipped = []
    for name in only or list(FIGURES):
        try:
            FIGURES[name](ctx)
        except Missing as missing:
            skipped.append((name, str(missing)))
            print(f"  {name}: not drawn, missing {missing}")
    if not only:
        # The guide's own copy is redrawn only when the results are those of this checkout.
        own = RESULTS == ROOT / "benchmarks" / "results" and GUIDE_ASSETS.is_dir()
        guide = own and draw_guide_figure()
        if own:
            copied = refresh_guide_copies(ctx)
            print(f"  the guide's copies: {len(copied)} refreshed in {relative(GUIDE_ASSETS)}")
        write_index(ctx, skipped, guide)
        write_readme_figures(ctx)
        print(f"{len(ctx.index)} figures drawn, {len(skipped)} not drawn; index: {relative(RESULTS / 'FIGURES.md')}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    modes = parser.add_subparsers(dest="mode", required=True)
    timing_ = modes.add_parser("time", help="measure this checkout, write the results, draw")
    timing_.add_argument("raw", help="directory for the logs, outside the checkout")
    timing_.add_argument("--jobs", type=int, default=8,
                         help="sections measured at a time, after the kernel sections")
    timing_.add_argument("--threads", type=int, default=24, help="threads in all")
    timing_.add_argument("--only", nargs="*", default=[], help="timing sections (default: all)")
    timing_.add_argument("--reuse", action="store_true",
                         help="reuse the executables and the Lake environment of an earlier run in RAW")
    install_ = modes.add_parser("install", help="result files from the logs of a timing run")
    install_.add_argument("raw")
    drawing = modes.add_parser("draw", help="draw every figure from the result files")
    drawing.add_argument("--only", nargs="*", default=[], help="figure names (default: all)")
    modes.add_parser("list", help="the figures and the timing sections")
    args = parser.parse_args()

    if args.mode == "list":
        print("figures:")
        for name, function in FIGURES.items():
            print(f"  {name:26s} {(function.__doc__ or '').strip().split(chr(10))[0]}")
        print("timing sections:")
        for name, seconds_, command in timing.sections(Path("RAW")):
            print(f"  {name:26s} {command}")
        return 0
    if args.mode == "draw":
        return draw(args.only)
    raw = Path(args.raw).resolve()
    if ROOT in raw.parents or raw == ROOT:
        raise SystemExit("RAW has to be outside the checkout")
    if args.mode == "time":
        raw.mkdir(parents=True, exist_ok=True)
        start = time.time()
        dirty = bool(subprocess.run(["git", "-C", str(ROOT), "diff", "--quiet", "HEAD"]).returncode)
        commit = git_head(short=False)
        # The record names a commit that others can look up: one that a remote branch has.
        named = commit if published(commit) and not dirty else ""
        print(f"measuring commit {commit}" + (" with uncommitted changes to tracked files" if dirty else "")
              + ("" if named else " (not on a remote branch: the record does not name it)"), flush=True)

        def log(text: str) -> None:
            print(f"[{time.time() - start:6.0f} s] {text}", flush=True)

        started = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
        done = timing.measure(raw, args.jobs, args.threads, args.only, log, args.reuse)
        record_run(raw, named, dirty, started, time.time() - start, args.jobs, args.threads, done,
                   timing.own_core(), timing.SHARED)
        log(f"measured commit {commit}: " + ", ".join(f"{n} exit {c}" for n, c, _ in done))
    install(raw)
    return draw([])


if __name__ == "__main__":
    sys.exit(main())
