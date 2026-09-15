"""Shared style for the guide's figures.

Every figure script in this directory imports this module, so the chapters' figures share one
palette, one type size, one width and one saving routine. A script draws one figure (or a small
family), names its data sources in its docstring, and writes a PNG into content/assets, where the
chapter refers to it as `![caption](assets/<name>.png)`.

Conventions the helpers enforce or make easy:

* Okabe and Ito colours only, assigned in a fixed order, never cycled or generated; identity is
  also carried by a label, a marker or a line style, never by colour alone.
* 9 inches wide at 200 dpi (1800 px), so a figure that spans the guide's wide column is sharp on
  a high-density screen; heights vary with content. Text is 10 pt or larger at that width.
* White background and no transparency: the reader shows each PNG on a white plate with a thin
  border, in dark mode too, so a figure must not rely on the page colour.
* No em or en dashes in any drawn string (the site's text checks cannot see inside a PNG), which
  `save` verifies before writing.
* Every number drawn comes from a file in the repository or from arithmetic on a format's
  parameters; nothing is estimated or remembered.

Run any script from anywhere: python3 <script>.py [--out PATH]
"""

from __future__ import annotations

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import FancyBboxPatch, Rectangle  # noqa: E402

HERE = Path(__file__).resolve().parent
ASSETS = HERE.parent                 # site/content/assets
SITE = HERE.parents[2]               # site
REPO = HERE.parents[3]               # repository root

WIDTH = 9.0                          # inches; 1800 px at DPI
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

DASHES = {"\u2014": "em dash (U+2014)", "\u2013": "en dash (U+2013)"}


def setup() -> None:
    """Apply the shared rcParams. Call once at the top of a script, before creating figures."""
    plt.rcParams.update({
        "figure.dpi": DPI,
        "savefig.dpi": DPI,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "font.family": "DejaVu Sans",
        "font.size": 10,
        "axes.titlesize": 11,
        "axes.labelsize": 10,
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "legend.fontsize": 9,
        "axes.edgecolor": INK,
        "axes.labelcolor": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "text.color": INK,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "grid.color": "#e3e3e0",
        "grid.linewidth": 0.6,
        "axes.axisbelow": True,
        "legend.frameon": False,
        "lines.linewidth": 1.8,
        "lines.markersize": 5.5,
        "mathtext.fontset": "dejavusans",
    })


def figure(height: float, **kwargs):
    """A figure of the shared width and the given height in inches."""
    return plt.subplots(figsize=(WIDTH, height), **kwargs)


def all_text(fig) -> list[str]:
    strings = []
    for text in fig.findobj(matplotlib.text.Text):
        if text.get_text():
            strings.append(text.get_text())
    return strings


def check_no_dashes(fig) -> None:
    for string in all_text(fig):
        for dash, name in DASHES.items():
            if dash in string:
                raise SystemExit(f"figure text contains an {name}: {string!r}")


def save(fig, name: str, out: Path | None = None) -> Path:
    """Write the figure as content/assets/<name> (or to `out`) after the dash check."""
    check_no_dashes(fig)
    target = Path(out) if out else ASSETS / name
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, dpi=DPI, facecolor="white", bbox_inches="tight", pad_inches=0.15)
    plt.close(fig)
    return target


def bit_layout(ax, fields, *, y: float = 0.0, height: float = 0.8, total: int | None = None,
               label_bits: bool = True, name_size: float = 9.5, index_size: float = 7.5,
               x0: float = 0.0, scale: float = 1.0) -> float:
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
                         linewidth=0.9, alpha=0.9)
        ax.add_patch(rect)
        if name and width * scale >= 3:
            ax.text(x + width * scale / 2, y + height / 2, name, ha="center", va="center",
                    fontsize=name_size, color=INK)
        elif name:
            # A field too narrow for its name (a sign bit) is named below the row instead.
            ax.text(x + width * scale / 2, y - 0.08, name, ha="center", va="top",
                    fontsize=name_size - 1, color=INK)
        if label_bits:
            ax.text(x + 0.08 * scale, y + height + 0.05, str(hi), ha="left", va="bottom",
                    fontsize=index_size, color=MUTED)
            if width > 1:
                ax.text(x + width * scale - 0.08 * scale, y + height + 0.05, str(hi - width + 1),
                        ha="right", va="bottom", fontsize=index_size, color=MUTED)
        x += width * scale
        hi -= width
    return x


def box(ax, x, y, w, h, text, *, facecolor=PAPER_2, edgecolor=INK, fontsize=9.5, rounding=0.08,
        linewidth=1.0, weight="normal", color=INK):
    """A rounded, labelled box for architecture and flow diagrams (data coordinates)."""
    patch = FancyBboxPatch((x, y), w, h, boxstyle=f"round,pad=0,rounding_size={rounding}",
                           facecolor=facecolor, edgecolor=edgecolor, linewidth=linewidth)
    ax.add_patch(patch)
    ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=fontsize,
            color=color, fontweight=weight, linespacing=1.3)
    return patch


def arrow(ax, start, end, *, color=INK, linewidth=1.0, style="-|>", shrink=2.0, connection=None):
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
