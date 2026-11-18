"""Shared style for every figure the library ships.

The guide's figure scripts (this directory and ../data) and the benchmark figure scripts
(benchmarks/plots) import this module, so that all figures have one look. A script draws one
figure or a small family, names its data sources in its docstring, and writes into
content/assets. Chapters refer to the main image as
`![description](assets/<name>.png "Caption")`; the reader prints "Figure N.M." before the caption.

What may be drawn inside an image, and what `save` enforces:

* The plot or diagram itself: axes whose labels name the quantity and its unit, tick labels, a
  legend or direct labels with short series names, panel letters with a short panel title
  (`panel_title`), and in diagrams short labels on the parts.
* No title or headline, no subtitle, no note, footnote or sentence, no colour key written as a
  sentence, and nothing about where or how something was measured. All of that belongs in the
  caption. `check_rules` rejects a figure title, a drawn string that reads as a sentence or is
  longer than `MAX_LINE` characters, and a commit hash, file name, toolchain version, date or
  trial count outside the tick labels; `check_no_dashes` rejects em and en dashes (the site's
  text checks cannot see inside a PNG).

The look:

* One font family (DejaVu Sans, with DejaVu Sans Mono for machine words and Lean names) and one
  set of sizes: `SIZE_LABEL` for axis labels, panel titles and the main labels of a diagram,
  `SIZE_TICK` for tick labels, legends and secondary labels, `SIZE_SMALL` for dense marks such as
  bit indices. Regular weight throughout.
* One set of line widths and marker sizes (`LW_DATA`, `LW_REF`, `LW_AXIS`, `MARKER`), a white
  background, no top or right spine, a light grid on the value axis only, no frames around
  legends, no shadows, no filled cards.
* Okabe and Ito colours. A library has the same colour, marker and line style in
  every figure: `SERIES` is the one map, and `series(name)` returns the keyword arguments for
  `Axes.plot`. Explanatory diagrams use `ROLE` (normal and subnormal values, the marked
  exception, an exact result) and `FIELD` (the fields of an encoding) in the same way. Identity
  is never carried by colour alone.
* Every figure is drawn 9 inches wide at 200 dpi (`WIDTH`, `DPI`); a figure may add a
  `<stem>-mobile.png` arrangement at `MOBILE_WIDTH` and single-panel views at `VIEW_WIDTH`.
  `save` writes the PNG and, beside it, the same drawing as SVG.
* Every number drawn comes from a file in the repository or from arithmetic on a format's
  parameters; nothing is estimated or remembered.

Run any script from anywhere: python3 <script>.py [--out PATH]
"""

from __future__ import annotations

import json
import re
import textwrap
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import FancyBboxPatch, Rectangle  # noqa: E402
from matplotlib.transforms import Bbox  # noqa: E402

HERE = Path(__file__).resolve().parent
ASSETS = HERE.parent                 # site/content/assets
SITE = HERE.parents[2]               # site
REPO = HERE.parents[3]               # repository root

WIDTH = 9.0                          # inches; 1800 px at DPI
MOBILE_WIDTH = 3.8                   # inches; the stacked arrangement shown below 600 px
VIEW_WIDTH = 4.25                    # inches; one panel of a multi-panel plot, for phones
DPI = 200

# Okabe and Ito.
ORANGE = "#E69F00"
SKY = "#56B4E9"
GREEN = "#009E73"
YELLOW = "#F0E442"
BLUE = "#0072B2"
VERMILION = "#D55E00"
PURPLE = "#CC79A7"
BLACK = "#000000"
PALETTE = [BLUE, ORANGE, GREEN, VERMILION, PURPLE, SKY, YELLOW]
INK = "#1b1b1b"
MUTED = "#616161"
LINE = "#c9c9c6"
PAPER_2 = "#f6f6f4"
GRID = "#e3e3e0"
GREY_DARK = "#595959"                # tools outside the fixed map: always labelled
GREY_LIGHT = "#999999"

FONT = "DejaVu Sans"
MONO = "DejaVu Sans Mono"            # machine words and Lean names only
SIZE_LABEL = 11.0                    # axis labels, panel titles, main labels of a diagram
SIZE_PANEL = SIZE_LABEL
SIZE_TICK = 10.0                     # tick labels, legends, secondary labels
SIZE_LEGEND = SIZE_TICK
SIZE_SMALL = 9.0                     # dense marks: bit indices, numbers on bars

LW_DATA = 1.8                        # data lines
LW_REF = 1.0                         # reference lines, brackets, arrows
LW_AXIS = 0.8                        # spines, ticks, outlines of diagram parts
LW_GRID = 0.6
MARKER = 5.5

MAX_LINE = 60                        # longest line of text a figure may draw, in characters
DASHES = {"—": "em dash (U+2014)", "–": "en dash (U+2013)"}

# The one map from a library to its colour, line style and marker. The benchmark
# figures and the guide's figures both draw from it. Tools outside the map are grey and labelled.
SERIES = {
    "FloatLib": dict(color=BLUE, linestyle="-", marker="o"),
    "FloatLib posit": dict(color=BLUE, linestyle="--", marker="s", markerfacecolor="white"),
    "Flocq": dict(color=VERMILION, linestyle="-", marker="s"),
    "Flocq lazy": dict(color=ORANGE, linestyle="--", marker="^"),
    "MPFR": dict(color=GREEN, linestyle="-", marker="D"),
    "SoftFloat": dict(color=PURPLE, linestyle="-", marker="v"),
    "native C": dict(color=BLACK, linestyle="-", marker="x"),
    "Universal": dict(color=GREY_DARK, linestyle="--", marker="P"),
    "Universal host sqrt": dict(color=GREY_DARK, linestyle=":", marker="P",
                                markerfacecolor="white"),
    "CPython": dict(color=GREY_LIGHT, linestyle="none", marker="X"),
}
# Short names for legends. A script that knows the version of another tool it measured passes it
# as `label` ("MPFR 4.2.1", "Coq 8.20.1 + Flocq 4.2.2"). FloatLib's series carry no version, and a
# legend never carries a commit, a path or a script name.
SERIES_LABEL = {
    "FloatLib": "FloatLib",
    "FloatLib posit": "FloatLib posit",
    "Flocq": "Coq + Flocq",
    "Flocq lazy": "Coq + Flocq, lazy",
    "MPFR": "MPFR",
    "SoftFloat": "Berkeley SoftFloat",
    "native C": "native C",
    "Universal": "Universal posit",
    "Universal host sqrt": "Universal posit, host sqrt",
    "CPython": "CPython float",
}

# Roles in explanatory diagrams, the same in every chapter.
ROLE = {
    "main": BLUE,                    # normal values, the rounding or format under discussion
    "second": ORANGE,                # subnormal values, the comparison
    "mark": VERMILION,               # the exact input, a tie, a difference found
    "exact": GREEN,                  # an exact result, a selected candidate
}
# Fields of an encoding, the same in every layout.
FIELD = {
    "sign": PURPLE,
    "exponent": ORANGE,
    "fraction": SKY,
    "regime": GREEN,
    "terminator": GREY_LIGHT,
}

OPERATION_LABEL = {
    "add": "addition",
    "sub": "subtraction",
    "mul": "multiplication",
    "div": "division",
    "sqrt": "square root",
    "fma": "fused multiply-add",
}


def setup() -> None:
    """Apply the shared rcParams. Call once at the top of a script, before creating figures."""
    plt.rcParams.update({
        "figure.dpi": DPI,
        "savefig.dpi": DPI,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "font.family": FONT,
        "font.size": SIZE_LABEL,
        "axes.titlesize": SIZE_PANEL,
        "axes.titleweight": "normal",
        "axes.titlelocation": "left",
        "axes.labelsize": SIZE_LABEL,
        "xtick.labelsize": SIZE_TICK,
        "ytick.labelsize": SIZE_TICK,
        "legend.fontsize": SIZE_LEGEND,
        "axes.edgecolor": INK,
        "axes.labelcolor": INK,
        "axes.linewidth": LW_AXIS,
        "xtick.color": INK,
        "ytick.color": INK,
        "xtick.major.width": LW_AXIS,
        "ytick.major.width": LW_AXIS,
        "xtick.minor.width": LW_GRID,
        "ytick.minor.width": LW_GRID,
        "text.color": INK,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "axes.grid.axis": "y",
        "grid.color": GRID,
        "grid.linewidth": LW_GRID,
        "axes.axisbelow": True,
        "legend.frameon": False,
        "lines.linewidth": LW_DATA,
        "lines.markersize": MARKER,
        "hatch.linewidth": LW_GRID,
        "mathtext.fontset": "dejavusans",
        "svg.fonttype": "none",
    })


def figure(height: float, **kwargs):
    """A figure of the shared width and the given height in inches."""
    return plt.subplots(figsize=(WIDTH, height), **kwargs)


def series(name: str, **overrides) -> dict:
    """Keyword arguments for `Axes.plot` that draw the library `name` the way every figure does."""
    style = dict(SERIES[name], label=SERIES_LABEL[name], linewidth=LW_DATA, markersize=MARKER)
    style.update(overrides)
    return style


def series_handle(name: str, **overrides) -> Line2D:
    """A legend handle for the library `name`."""
    return Line2D([], [], **series(name, **overrides))


def panel_title(ax, index: int, title: str = "") -> None:
    """Letter a panel, (a), (b), ..., followed by a short title that names only what differs."""
    letter = f"({chr(ord('a') + index)})"
    ax.set_title(f"{letter} {title}".rstrip(), loc="left", fontsize=SIZE_PANEL, color=INK, pad=6)


def value_grid(ax, axis: str = "y") -> None:
    """A light grid on the value axis only (`axis` is "y", "x", or "both" for a scatter plot)."""
    ax.grid(False)
    ax.grid(True, axis=axis, color=GRID, linewidth=LW_GRID)
    ax.set_axisbelow(True)


def legend(target, handles=None, labels=None, **kwargs):
    """A legend without a frame at the shared size. `target` is an Axes or a Figure."""
    options = dict(frameon=False, fontsize=SIZE_LEGEND, handlelength=2.2, handletextpad=0.6,
                   columnspacing=1.6, borderaxespad=0.0)
    options.update(kwargs)
    if handles is None:
        return target.legend(**options)
    if labels is None:
        return target.legend(handles=handles, **options)
    return target.legend(handles, labels, **options)


def all_text(fig) -> list[str]:
    """Every visible, non-empty string the figure draws, tick labels included."""
    strings = []
    for text in fig.findobj(matplotlib.text.Text):
        if text.get_text() and text.get_visible():
            strings.append(text.get_text())
    return strings


def check_no_dashes(fig) -> None:
    """Stop if a drawn string holds an em or en dash."""
    for string in all_text(fig):
        for dash, name in DASHES.items():
            if dash in string:
                raise SystemExit(f"figure text contains an {name}: {string!r}")


_SENTENCE = re.compile(r"[A-Za-z)\]]\.(\s|$)")
_MATH = re.compile(r"\$[^$]*\$")
# A commit hash, a file name or path, a toolchain version, a date, or the words of a
# measurement protocol. Tick labels are data and are not searched.
_PROVENANCE = re.compile(
    r"(?<![0-9A-Za-z])(?=[0-9a-f]*[a-f])(?=[0-9a-f]*[0-9])[0-9a-f]{7,40}(?![0-9A-Za-z])"
    r"|\.(py|csv|json|lean|md|sh)\b|/[a-z]+/"
    r"|\b(commit|recorded|measured|trials?)\b|\b(Lean|Mathlib) v?\d|\b20\d\d-\d\d-\d\d\b",
    re.I)


def check_rules(fig) -> None:
    """Stop if the figure draws text that belongs in its caption.

    That is a figure title, a sentence, a line longer than `MAX_LINE` characters, and anything
    that says where or how something was measured.
    """
    title = getattr(fig, "_suptitle", None)
    if title is not None and title.get_text().strip():
        raise SystemExit(f"a figure has no title; say it in the caption: {title.get_text()!r}")
    ticks = {id(label) for ax in fig.axes for axis in (ax.xaxis, ax.yaxis)
             for label in axis.get_ticklabels(which="both")}
    for text in fig.findobj(matplotlib.text.Text):
        string = text.get_text()
        if not string or not text.get_visible():
            continue
        plain = _MATH.sub("x", string)
        if _SENTENCE.search(plain):
            raise SystemExit(f"figure text is a sentence; move it to the caption: {string!r}")
        if any(len(line) > MAX_LINE for line in plain.splitlines()):
            raise SystemExit(f"figure text is longer than {MAX_LINE} characters; "
                             f"shorten it or move it to the caption: {string!r}")
        if id(text) not in ticks and _PROVENANCE.search(plain):
            raise SystemExit("figure text says where or how something was measured; "
                             f"move it to the caption: {string!r}")


# An SVG keeps its text as text, and a page shows it with the fonts of the reader's system. These
# stacks follow the family in every text style, so that a phone without DejaVu Sans shows a
# sans-serif face of similar width and not the browser's default serif.
SVG_FONT_STACK = {
    f"font-family: '{FONT}'": f"font-family: '{FONT}', 'Bitstream Vera Sans', Verdana, sans-serif",
    f"font-family: '{MONO}'":
        f"font-family: '{MONO}', 'Bitstream Vera Sans Mono', Menlo, Consolas, monospace",
}


def save_svg(fig, target: Path, **kwargs) -> Path:
    """Write `fig` as an SVG whose bytes depend only on the drawing (fixed ids, no date)."""
    target = Path(target)
    with matplotlib.rc_context({"svg.hashsalt": "floatlib-figures-v2", "svg.fonttype": "none"}):
        fig.savefig(target, format="svg", metadata={"Date": None}, facecolor="white", **kwargs)
    text = target.read_text(encoding="utf-8")
    for family, stack in SVG_FONT_STACK.items():
        text = text.replace(family, stack)
    target.write_text("\n".join(line.rstrip() for line in text.splitlines()) + "\n",
                      encoding="utf-8")
    return target


def content_bbox(fig, pad: float = 0.1):
    """The box, in inches, that `save` writes: the full canvas width, cropped in height.

    Every figure keeps the width of its canvas, so that all figures are shown at one scale and
    their text has one size on the page; the box grows sideways only where something is drawn
    outside the canvas. In height it is cropped to what is drawn, with a margin of `pad`.
    Matplotlib's own tight box always contains each Axes rectangle, so a diagram drawn on an
    Axes without axis lines would keep the empty parts of its canvas. Here such an Axes
    contributes only what is drawn on it.
    """
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    boxes = []

    def add(artist) -> None:
        if not artist.get_visible():
            return
        box = artist.get_tightbbox(renderer)
        if box is not None and all(map(_finite, box.extents)) and (box.width or box.height):
            boxes.append(box)

    for ax in fig.axes:
        if ax.axison:
            add(ax)
            continue
        skip = {id(ax.patch), id(ax.xaxis), id(ax.yaxis), *(id(s) for s in ax.spines.values())}
        for artist in ax.get_children():
            if id(artist) in skip:
                continue
            if isinstance(artist, matplotlib.text.Text) and not artist.get_text():
                continue
            add(artist)
    for artist in (*fig.texts, *fig.legends, *fig.artists, *fig.patches, *fig.lines):
        add(artist)
    for name in ("_suptitle", "_supxlabel", "_supylabel"):
        if getattr(fig, name, None) is not None:
            add(getattr(fig, name))
    if not boxes:
        return "tight"
    union = Bbox.union(boxes)
    left, right = union.x0 / fig.dpi, union.x1 / fig.dpi
    width = fig.get_figwidth()
    return Bbox.from_extents(left - pad if left < 0 else 0.0, union.y0 / fig.dpi - pad,
                             right + pad if right > width else width, union.y1 / fig.dpi + pad)


def _finite(value: float) -> bool:
    return value == value and abs(value) != float("inf")


def save(fig, name: str, out: Path | None = None, *, vector: bool = True,
         rules: bool = True) -> Path:
    """Write the figure as content/assets/<name> (or to `out`) after the text checks.

    A PNG is written at `DPI` with the box of `content_bbox`. Unless `vector` is false or the
    file is a `-mobile` arrangement, the same drawing is written beside it as `<stem>.svg`.
    Returns the PNG path.
    """
    check_no_dashes(fig)
    if rules:
        check_rules(fig)
    target = Path(out) if out else ASSETS / name
    target.parent.mkdir(parents=True, exist_ok=True)
    box = content_bbox(fig)
    fig.savefig(target, dpi=DPI, facecolor="white", bbox_inches=box)
    if vector and target.suffix == ".png" and not target.stem.endswith("-mobile"):
        save_svg(fig, target.with_suffix(".svg"), bbox_inches=box)
    plt.close(fig)
    return target


def mobile_path(target: Path) -> Path:
    """The path of the `-mobile` arrangement that belongs to `target`."""
    target = Path(target)
    return target.with_name(f"{target.stem}-mobile{target.suffix}")


def stagger_labels(axis) -> None:
    """Keep every tick label of the x axis and put every second one on a lower line."""
    labels = [label.get_text().strip() for label in axis.get_xticklabels()]
    axis.set_xticks(
        axis.get_xticks(),
        labels=[label if i % 2 == 0 else "\n" + label for i, label in enumerate(labels)],
    )


def compact_view(fig, ax, *, title: str, handles, labels) -> None:
    """Lay out one panel at `VIEW_WIDTH` for a phone: its title above, its legend below."""
    fig.set_size_inches(VIEW_WIDTH, 5.0)
    for location in ("left", "center", "right"):
        ax.set_title("", loc=location)
    ax.tick_params(axis="both", labelsize=SIZE_TICK)
    ax.xaxis.label.set_size(SIZE_LABEL)
    ax.yaxis.label.set_size(SIZE_LABEL)
    wrapped = [textwrap.fill(label, 22, break_long_words=False) for label in labels]
    key = fig.legend(
        handles, wrapped, loc="upper center", bbox_to_anchor=(0.5, 0.3),
        ncols=min(2, len(labels)), frameon=False, fontsize=SIZE_LEGEND,
        handlelength=2.2, handletextpad=0.5, columnspacing=0.9, labelspacing=0.6,
        borderaxespad=0,
    )
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    key_height = key.get_window_extent(renderer).height / fig.dpi
    left = max(0.72, (ax.get_window_extent(renderer).x0
                      - ax.yaxis.get_tightbbox(renderer).x0) / fig.dpi + 0.12)
    x_gap = (ax.get_window_extent(renderer).y0
             - ax.xaxis.get_tightbbox(renderer).y0) / fig.dpi + 0.20
    header, plot_height, footer = 0.40, 2.9, 0.10
    height = header + plot_height + x_gap + key_height + footer
    fig.set_size_inches(VIEW_WIDTH, height)
    ax.set_position([left / VIEW_WIDTH, (footer + key_height + x_gap) / height,
                     (VIEW_WIDTH - left - 0.18) / VIEW_WIDTH, plot_height / height])
    key.set_bbox_to_anchor((0.5, (footer + key_height) / height))
    fig.text(left / VIEW_WIDTH, 1 - 0.12 / height, title, fontsize=SIZE_PANEL, ha="left",
             va="top", color=INK)


def save_view(fig, overview: Path, view: str) -> Path:
    """Save one single-panel view of `overview` as `<stem>-<view>.svg` after the text checks."""
    check_no_dashes(fig)
    check_rules(fig)
    target = save_svg(fig, Path(overview).with_name(f"{Path(overview).stem}-{view}.svg"))
    plt.close(fig)
    return target


def write_views(overview: Path, descriptions: dict[str, str], *, overview_alt: str,
                view_label: dict[str, str] | None = None, label: str = "Operation") -> Path:
    """Write `<stem>-series.json`, the reader's selector between the overview and its views.

    `descriptions` maps each view id to its alt text; the view files must already exist.
    """
    overview = Path(overview)
    if not descriptions:
        raise ValueError("a view selector needs at least one view")
    names = view_label or OPERATION_LABEL
    views = [{"id": "all", "label": f"All {label.lower()}s", "src": overview.name,
              "alt": overview_alt}]
    for view, alt in descriptions.items():
        asset = overview.with_name(f"{overview.stem}-{view}.svg")
        if not asset.is_file():
            raise ValueError(f"missing view: {asset}")
        name = names[view]
        views.append({"id": view, "label": name[0].upper() + name[1:], "src": asset.name,
                      "alt": alt})
    target = overview.with_name(f"{overview.stem}-series.json")
    target.write_text(json.dumps({
        "label": label, "compactDefault": next(iter(descriptions)), "views": views,
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return target


def bit_layout(ax, fields, *, y: float = 0.0, height: float = 0.8, total: int | None = None,
               label_bits: bool = True, name_size: float = SIZE_TICK,
               index_size: float = SIZE_SMALL, x0: float = 0.0, scale: float = 1.0) -> float:
    """Draw one row of bit fields on `ax`.

    `fields` is a list of (name, width_in_bits, colour); fields are drawn most significant first,
    from `x0` rightwards, each `scale` axis units per bit. Bit indices run from the total width
    minus one down to zero, printed at the two ends of each field. Returns the x coordinate at
    the right end, so a caller can align several rows or place a label after the row.
    The caller sets the axis limits and turns the axes off.
    """
    total_bits = total if total is not None else sum(width for _, width, _ in fields)
    x = x0
    hi = total_bits - 1
    for name, width, colour in fields:
        rect = Rectangle((x, y), width * scale, height, facecolor=colour, edgecolor=INK,
                         linewidth=LW_AXIS, alpha=0.9)
        ax.add_patch(rect)
        if name and width * scale >= 3:
            ax.text(x + width * scale / 2, y + height / 2, name, ha="center", va="center",
                    fontsize=name_size, color=INK)
        elif name:
            # A field too narrow for its name (a sign bit) is named below the row instead.
            ax.text(x + width * scale / 2, y - 0.08, name, ha="center", va="top",
                    fontsize=name_size, color=INK)
        if label_bits:
            ax.text(x + 0.08 * scale, y + height + 0.05, str(hi), ha="left", va="bottom",
                    fontsize=index_size, color=MUTED)
            if width > 1:
                ax.text(x + width * scale - 0.08 * scale, y + height + 0.05, str(hi - width + 1),
                        ha="right", va="bottom", fontsize=index_size, color=MUTED)
        x += width * scale
        hi -= width
    return x


def box(ax, x, y, w, h, text="", *, facecolor="white", edgecolor=INK, fontsize=SIZE_LABEL,
        rounding=0.0, linewidth=LW_AXIS, weight="normal", color=INK):
    """A plain outlined node for flow diagrams (data coordinates), with its label centred."""
    style = f"round,pad=0,rounding_size={rounding}" if rounding else "square,pad=0"
    patch = FancyBboxPatch((x, y), w, h, boxstyle=style, facecolor=facecolor,
                           edgecolor=edgecolor, linewidth=linewidth)
    ax.add_patch(patch)
    if text:
        ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=fontsize,
                color=color, fontweight=weight, linespacing=1.3)
    return patch


def arrow(ax, start, end, *, color=INK, linewidth=LW_REF, style="-|>", shrink=2.0,
          connection=None):
    """An arrow between two points in data coordinates."""
    kwargs = dict(arrowstyle=style, color=color, lw=linewidth, shrinkA=shrink, shrinkB=shrink)
    if connection:
        kwargs["connectionstyle"] = connection
    ax.annotate("", xy=end, xytext=start, arrowprops=kwargs)


def diagram_axes(fig, xlim, ylim):
    """A single axes with no frame, grid or ticks, for diagrams drawn in data coordinates."""
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.grid(False)
    return ax
