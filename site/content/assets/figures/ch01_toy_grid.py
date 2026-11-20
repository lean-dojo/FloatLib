#!/usr/bin/env python3
"""Draw content/assets/ch01-toy-grid.png: the nonnegative values of a six-bit toy format.

Chapter 02 explains that a binary floating-point grid is evenly spaced within each binade, that
the spacing doubles at each power of two, and that the all-zeros exponent field continues the
grid below the smallest normal with the spacing it had just above (gradual underflow). Binary32
has far too many points to draw, so this figure uses a toy format with 3 exponent bits and
2 fraction bits, the descriptor `FloatFormat.ieee 3 2` of
FloatLib/Floats/Formats/BinaryInterchange/Format/Definition.lean: its bias is
`ieeeBias 3 = 2^(3-1) - 1 = 3` and its width is `bitWidth = 1 + 3 + 2 = 6`. The chapter itself
uses no toy format, and the caption says this one is ours.

Every value is computed here from the decoding rule of `toDyadic?` in
FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean, with the exponents of
FloatLib/Floats/Formats/BinaryInterchange/Format/Properties.lean
(`minNormalExponent = 1 - exponentBias`, `minSubnormalExponent = minNormalExponent - fracWidth`):

* exponent field E = 0 with fraction F denotes F * 2^minSubnormalExponent (no hidden bit);
* 0 < E < 2^3 - 1 with fraction F denotes (2^fracWidth + F) * 2^(E - exponentBias - fracWidth);
* E = 2^3 - 1, the all-ones field, is infinity or NaN and contributes no point.

Nothing is taken from memory; the assertions below pin the smallest subnormal, the smallest
normal and the largest finite value to those formulas.

Run from anywhere: python3 ch01_toy_grid.py [--out PNG]
Also writes a -mobile.png sibling, with one independently scaled row per exponent field.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import ConnectionPatch  # noqa: E402

# FloatFormat.ieee 3 2 (Format/Definition.lean).
EXP_WIDTH = 3
FRAC_WIDTH = 2
BIAS = 2 ** (EXP_WIDTH - 1) - 1                 # FloatFormat.ieeeBias
ALL_ONES = 2 ** EXP_WIDTH - 1                   # reserved for infinity and NaN
MIN_NORMAL_EXP = 1 - BIAS                       # FloatFormat.minNormalExponent
MIN_SUBNORMAL_EXP = MIN_NORMAL_EXP - FRAC_WIDTH  # FloatFormat.minSubnormalExponent


def decode(exp_field: int, frac_field: int) -> Fraction:
    """The rule of Model.toDyadic? (Dyadic/Decode.lean) for a positive finite word."""
    if exp_field == 0:
        return Fraction(frac_field) * Fraction(2) ** MIN_SUBNORMAL_EXP
    significand = 2 ** FRAC_WIDTH + frac_field
    return significand * Fraction(2) ** (exp_field - BIAS - FRAC_WIDTH)


def positive_words() -> list[tuple[int, int, Fraction]]:
    words = []
    for exp_field in range(ALL_ONES):
        for frac_field in range(2 ** FRAC_WIDTH):
            words.append((exp_field, frac_field, decode(exp_field, frac_field)))
    return words


def frac_label(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


SUBNORMAL = dict(marker="s", markersize=6.5, markerfacecolor="white",
                 markeredgecolor=fs.ROLE["second"], markeredgewidth=1.6, linestyle="none")
NORMAL = dict(marker="o", markersize=6, color=fs.ROLE["main"], linestyle="none")


def key(target, **kwargs) -> None:
    """The legend of the two marks, the same in both arrangements."""
    handles = [Line2D([], [], label="zero and subnormal", **SUBNORMAL),
               Line2D([], [], label="normal", **NORMAL)]
    fs.legend(target, handles=handles, **kwargs)


def number_line(ax, words, xlim, *, tick_height: float, label_words: bool) -> None:
    ax.set_xlim(*xlim)
    ax.axis("off")
    ax.grid(False)
    ax.plot(xlim, [0, 0], color=fs.INK, linewidth=1.0, zorder=1)
    for exp_field, frac_field, value in words:
        x = float(value)
        zero_or_subnormal = exp_field == 0
        ax.plot([x, x], [-tick_height, tick_height], color=fs.INK, linewidth=0.8, zorder=2)
        ax.plot([x], [0], zorder=3, **(SUBNORMAL if zero_or_subnormal else NORMAL))
        if label_words:
            ax.text(x, -tick_height - 0.10, f"{exp_field:0{EXP_WIDTH}b} {frac_field:0{FRAC_WIDTH}b}",
                    ha="center", va="top", rotation=90, fontsize=fs.SIZE_SMALL, family=fs.MONO,
                    color=fs.INK)


def bracket(ax, lo: float, hi: float, y: float, text: str, *, color=fs.INK, fontsize=fs.SIZE_TICK,
            text_dy: float = 0.08) -> None:
    ax.plot([lo, lo, hi, hi], [y - 0.07, y, y, y - 0.07], color=color, linewidth=0.9)
    ax.text((lo + hi) / 2, y + text_dy, text, ha="center", va="bottom", fontsize=fontsize,
            color=color, linespacing=1.25)


def build_mobile(words):
    """Keep all 28 values and their fields legible by separating the seven exponent rows."""
    height = 9.0
    fig = fs.plt.figure(figsize=(fs.MOBILE_WIDTH, height))
    ax = fs.diagram_axes(fig, (0, fs.MOBILE_WIDTH), (0, height))
    ax.text(0.18, 7.73, "fraction field F", fontsize=fs.SIZE_TICK, va="center", color=fs.MUTED)
    columns = (0.40, 1.40, 2.40, 3.40)
    for frac_field, x in enumerate(columns):
        ax.text(x, 7.43, f"{frac_field:02b}", fontsize=fs.SIZE_LABEL, ha="center",
                va="center", family=fs.MONO)

    steps = []
    for exp_field in range(ALL_ONES):
        row = [w for w in words if w[0] == exp_field]
        assert [f for _, f, _ in row] == list(range(2 ** FRAC_WIDTH))
        step = row[1][2] - row[0][2]
        assert all(b[2] - a[2] == step for a, b in zip(row, row[1:]))
        steps.append(step)
        y = 7.08 - 0.88 * exp_field
        ax.text(0.18, y, f"E = {exp_field:03b}", fontsize=fs.SIZE_LABEL,
                family=fs.MONO, va="center")
        ax.text(3.62, y, f"spacing {frac_label(step)}", fontsize=fs.SIZE_TICK, ha="right",
                va="center")
        line_y = y - 0.29
        ax.plot([columns[0], columns[-1]], [line_y, line_y], color=fs.LINE, linewidth=1)
        for (_, _, value), x in zip(row, columns):
            ax.plot([x], [line_y], **(SUBNORMAL if exp_field == 0 else NORMAL))
            ax.text(x, line_y - 0.16, frac_label(value), fontsize=fs.SIZE_TICK, ha="center", va="top")
    assert steps == [Fraction(1, 16), Fraction(1, 16), Fraction(1, 8),
                     Fraction(1, 4), Fraction(1, 2), Fraction(1), Fraction(2)]
    assert len({v for _, _, v in words}) == 28
    key(ax, loc="center", bbox_to_anchor=(1.9, 1.02), bbox_transform=ax.transData, ncols=2,
        columnspacing=1.0)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    words = positive_words()
    values = [v for _, _, v in words]
    assert decode(0, 1) == Fraction(1, 16) and MIN_SUBNORMAL_EXP == -4
    assert decode(1, 0) == Fraction(1, 4) and MIN_NORMAL_EXP == -2
    assert max(values) == 14 and len(words) == 28
    subnormal_step = decode(0, 1)
    assert decode(1, 1) - decode(1, 0) == subnormal_step   # same spacing on both sides of 1/4

    fig, (top, bottom) = fs.figure(4.9, nrows=2, gridspec_kw={"height_ratios": [1.0, 1.35]})
    fig.subplots_adjust(left=0.02, right=0.98, top=0.98, bottom=0.02, hspace=0.55)

    # Upper panel: the whole nonnegative range 0 to 14.
    top.set_ylim(-0.85, 1.95)
    number_line(top, words, (-0.4, 17.4), tick_height=0.14, label_words=False)
    for value in (0, 1, 2, 4, 8, 14):
        top.text(value, -0.24, str(value), ha="center", va="top", fontsize=fs.SIZE_TICK, color=fs.INK)
    # Narrow binades get the upper row of brackets so that no two labels touch.
    for lo, hi, exp_field, y in ((1, 2, 3, 0.95), (2, 4, 4, 0.42), (4, 8, 5, 0.95)):
        step = decode(exp_field, 1) - decode(exp_field, 0)
        bracket(top, lo, hi, y, f"spacing {frac_label(step)}\nE = {exp_field}")
    step_top = decode(6, 1) - decode(6, 0)
    bracket(top, 8, 14, 0.42, f"spacing {frac_label(step_top)}\nE = 6")
    key(top, loc="upper right", bbox_to_anchor=(17.4, 1.95), bbox_transform=top.transData)
    top.axvspan(-0.15, 1.0, ymin=0.22, ymax=0.62, color=fs.PAPER_2, zorder=0)
    top.text(-0.4, 1.9, "(a)", ha="left", va="top", fontsize=fs.SIZE_PANEL, color=fs.INK)

    # Lower panel: zoom on [0, 1], words labelled by their exponent and fraction fields.
    bottom.set_ylim(-1.35, 1.35)
    small = [w for w in words if w[2] <= 1]
    number_line(bottom, small, (-0.05, 1.05), tick_height=0.10, label_words=True)
    for value, text in ((Fraction(0), "0"), (Fraction(1, 4), "1/4"),
                        (Fraction(1, 2), "1/2"), (Fraction(1), "1")):
        bottom.text(float(value), 0.17, text, ha="center", va="bottom", fontsize=fs.SIZE_SMALL,
                    color=fs.INK, linespacing=1.2)
    bottom.axvspan(-0.02, float(decode(1, 0)), ymin=0.44, ymax=0.56, color=fs.ROLE["second"], alpha=0.12,
                   zorder=0)
    bracket(bottom, 0.0, float(decode(1, 0)) - 0.01, 0.98,
            f"E = 0\nspacing {frac_label(subnormal_step)}")
    for exp_field, lo, hi in ((1, Fraction(1, 4), Fraction(1, 2)), (2, Fraction(1, 2), Fraction(1))):
        step = decode(exp_field, 1) - decode(exp_field, 0)
        bracket(bottom, float(lo) + 0.005, float(hi) - 0.005, 0.98,
                f"E = {exp_field}\nspacing {frac_label(step)}")
    bottom.text(-0.05, 1.33, "(b)", ha="left", va="top", fontsize=fs.SIZE_PANEL, color=fs.INK)

    # Two thin lines tie the shaded band of the upper panel to the lower panel's full width. They
    # start under the tick labels 0 and 1, clear of the digits.
    for x_top, x_bottom in ((0.0, -0.05), (1.0, 1.05)):
        fig.add_artist(ConnectionPatch(xyA=(x_top, -0.55), coordsA=top.transData,
                                       xyB=(x_bottom, 1.35), coordsB=bottom.transData,
                                       color=fs.LINE, linewidth=0.8))

    out = fs.save(fig, "ch01-toy-grid.png", args.out)
    print(f"wrote {out}")
    mobile = fs.mobile_path(out)
    print(f"wrote {fs.save(build_mobile(words), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
