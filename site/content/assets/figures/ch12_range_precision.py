#!/usr/bin/env python3
"""Draw content/assets/ch12-range-precision.png: range and precision of the five named formats.

Left panel: for binary16, bfloat16, binary32, binary64 and binary128, the least positive
subnormal, the least positive normal and the largest finite value on one logarithmic axis, one
row per format. Right panel: the number of significant decimal digits each format's precision
carries. The two 16-bit formats show the trade the chapter describes: bfloat16 reaches binary32's
range with fewer digits than binary16.

Sources. The exponent and fraction widths are the `expWidth` and `fracWidth` of the descriptors
in FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean. Everything else is arithmetic
on those two integers, with the formulas the chapter states for an IEEE descriptor (they are the
definitions in FloatLib/Floats/Formats/BinaryInterchange/Format/Definition.lean and
Format/Properties.lean: `ieeeBias`, `minNormalExponent`, `minSubnormalExponent`,
`maxNormalExponent`):

    b        = 2^(expWidth - 1) - 1           (the conventional bias)
    p        = fracWidth + 1                  (precision in bits, implicit leading one included)
    e_min    = 1 - b,   e_max = b
    x_min^norm = 2^e_min
    x_min^subn = 2^(e_min - fracWidth)
    x_max    = (2 - 2^-fracWidth) * 2^e_max
    digits   = p * log10(2)                    (significant decimal digits of a p-bit significand)

The decimal exponents are computed exactly as log10 of integers or of powers of two, never
through a binary64 float (binary128's values do not fit in one); the labels are rounded to three
significant figures.

Axis note. The value axis is the decimal exponent log10(x) on a symmetric-log scale: linear for
exponents between -10 and 10, logarithmic beyond, so that binary16 (12 decades of range) and
binary128 (nearly ten thousand) fit on one line. Where a format's least subnormal and least normal
are closer than the marker size, the open circle sits around the square; that is the true picture
of a subnormal extension of fracWidth binades against a normal range of 2^expWidth binades.

Run from anywhere: python3 ch12_range_precision.py [--out PNG]
"""

from __future__ import annotations

import argparse
import math
import sys
from decimal import Decimal, getcontext
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.lines import Line2D  # noqa: E402

# (name, expWidth, fracWidth) as in Format/Catalog.lean, in the order of the chapter's table.
FORMATS = (
    ("binary16", 5, 10),
    ("bfloat16", 8, 7),
    ("binary32", 8, 23),
    ("binary64", 11, 52),
    ("binary128", 15, 112),
)

LOG10_2 = math.log10(2)

SUBN_STYLE = dict(marker="o", markersize=10, markerfacecolor="white", markeredgecolor=fs.VERMILION,
                  markeredgewidth=1.6, linestyle="None")
NORM_STYLE = dict(marker="s", markersize=6, color=fs.BLUE, linestyle="None")
MAX_STYLE = dict(marker=">", markersize=8, color=fs.GREEN, linestyle="None")

XLABEL = "value on a logarithmic axis, compressed beyond $10^{\\pm 10}$ so that binary128 fits"
DIGITS_LABEL = "decimal digits, $p \\log_{10} 2$"


def constants(exp_width: int, frac_width: int) -> dict:
    """The chapter's formulas, evaluated exactly on integers."""
    bias = 2 ** (exp_width - 1) - 1
    p = frac_width + 1
    e_min = 1 - bias
    e_max = bias
    # x_max = (2 - 2^-w_f) * 2^e_max = (2^(w_f+1) - 1) * 2^(e_max - w_f), an integer here because
    # e_max >= w_f for every format in the table.
    assert e_max >= frac_width
    x_max_int = (2 ** (frac_width + 1) - 1) * 2 ** (e_max - frac_width)
    return {
        "bias": bias, "p": p, "e_min": e_min, "e_max": e_max,
        "log_max": math.log10(x_max_int),                # exact log10 of a big integer
        "log_norm": e_min * LOG10_2,                      # log10(2^e_min)
        "log_subn": (e_min - frac_width) * LOG10_2,       # log10(2^(e_min - w_f))
        "digits": p * LOG10_2,
        "x_max_int": x_max_int,
    }


def sci(log10_value: float, exact_int: int | None = None) -> str:
    """Three significant figures as m x 10^e, or the integer itself when it is short."""
    if exact_int is not None and exact_int < 10 ** 6:
        return str(exact_int)
    getcontext().prec = 30
    exponent = math.floor(log10_value)
    mantissa = Decimal(10) ** Decimal(log10_value - exponent)
    mantissa = mantissa.quantize(Decimal("0.01"))
    if mantissa >= 10:
        mantissa = (mantissa / 10).quantize(Decimal("0.01"))
        exponent += 1
    return f"${mantissa} \\times 10^{{{exponent}}}$"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    fig, (ax, axd) = fs.figure(4.6, ncols=2, sharey=True, gridspec_kw={"width_ratios": [4.4, 1]})
    fig.subplots_adjust(left=0.09, right=0.97, top=0.84, bottom=0.17, wspace=0.08)

    rows = list(range(len(FORMATS)))[::-1]  # first format at the top
    for y, (name, exp_width, frac_width) in zip(rows, FORMATS):
        c = constants(exp_width, frac_width)
        # The range: dashed through the subnormals, solid through the normals.
        ax.plot([c["log_subn"], c["log_norm"]], [y, y], color=fs.VERMILION, linewidth=1.4,
                linestyle=(0, (3, 2)), zorder=1)
        ax.plot([c["log_norm"], c["log_max"]], [y, y], color=fs.BLUE, linewidth=1.8, zorder=1)
        ax.plot([c["log_subn"]], [y], zorder=3, **SUBN_STYLE)
        ax.plot([c["log_norm"]], [y], zorder=4, **NORM_STYLE)
        ax.plot([c["log_max"]], [y], zorder=4, **MAX_STYLE)
        # Value labels sit above their markers so that no label runs into the axis frame or the
        # row name, whichever end of the axis the marker is near.
        ax.annotate(sci(c["log_subn"]), (c["log_subn"], y), textcoords="offset points",
                    xytext=(0, 9), ha="center", va="bottom", fontsize=9)
        ax.annotate(sci(c["log_max"], c["x_max_int"]), (c["log_max"], y),
                    textcoords="offset points", xytext=(0, 9), ha="center", va="bottom",
                    fontsize=9)

        axd.barh(y, c["digits"], height=0.5, color=fs.PURPLE, edgecolor=fs.INK, linewidth=0.6)
        axd.annotate(f"{c['digits']:.1f}", (c["digits"], y), textcoords="offset points",
                     xytext=(4, 0), ha="left", va="center", fontsize=9)

    ax.set_xscale("symlog", base=10, linthresh=10, linscale=1.5)
    ax.set_xlim(-40000, 40000)
    ticks = [-1000, -100, -10, 0, 10, 100, 1000]
    ax.set_xticks(ticks)
    ax.set_xticklabels(["$10^{-1000}$", "$10^{-100}$", "$10^{-10}$", "$1$", "$10^{10}$",
                        "$10^{100}$", "$10^{1000}$"])
    ax.minorticks_off()
    ax.set_yticks(rows)
    ax.set_yticklabels([name for name, _, _ in FORMATS], fontsize=10)
    ax.set_ylim(-0.6, len(FORMATS) - 0.25)
    ax.set_xlabel(XLABEL, fontsize=9.5)
    ax.grid(axis="y", visible=False)
    ax.tick_params(axis="y", length=0)

    axd.set_xlim(0, 44)
    axd.set_xticks([0, 10, 20, 30, 40])
    axd.set_xlabel(DIGITS_LABEL, fontsize=9.5)
    axd.grid(axis="y", visible=False)
    axd.tick_params(axis="y", length=0)

    handles = [
        Line2D([], [], label="least positive subnormal, $2^{e_{\\min} - w_f}$", **SUBN_STYLE),
        Line2D([], [], label="least positive normal, $2^{e_{\\min}}$", **NORM_STYLE),
        Line2D([], [], label="largest finite, $(2 - 2^{-w_f}) \\cdot 2^{e_{\\max}}$", **MAX_STYLE),
    ]
    fig.legend(handles=handles, loc="upper center", ncol=3, bbox_to_anchor=(0.5, 0.97),
               fontsize=9.5, handletextpad=0.5, columnspacing=1.8)

    out = fs.save(fig, "ch12-range-precision.png", out=args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
