#!/usr/bin/env python3
"""Draw content/assets/ch13-element-values.png: the seven small formats, layout and value set.

One row per format: E5M2, E4M3FN, E4M3FNUZ, E5M2FNUZ, E2M3, E3M2 and E2M1, in the order chapter 09
introduces them. At the left, the stored word drawn to scale as sign, exponent and fraction fields
(with fs.bit_layout, one width per bit in every row). At the right, every positive finite value
the format can hold, as a tick on one shared logarithmic axis, tall for a normal value and short
for a subnormal one. Zero is not drawn (it has no place on a logarithmic axis) and neither are the
infinities and NaNs, so a row shows exactly the positive numbers a byte of that format can mean.

Sources. The descriptors are those of
FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean: `e5m2 = ieee 5 2`,
`e4m3fn = finiteMaxNaN 4 3`, `e4m3fnuz = finiteUnsignedZero 4 3`,
`e5m2fnuz = finiteUnsignedZero 5 2`, `e2m3 = finite 2 3`, `e3m2 = finite 3 2`, `e2m1 = finite 2 1`,
with the biases the constructors in Format/Definition.lean assign: `ieeeBias w = 2^(w-1) - 1`
for `ieee`, `finiteMaxNaN` and `finite`, and `ieeeBias w + 1` for `finiteUnsignedZero`. Which
words are numbers follows the classifiers of
FloatLib/Floats/Formats/BinaryInterchange/Model/Carrier.lean: under `ieee` an all-ones exponent
is an infinity (zero fraction) or a NaN; under `finiteMaxNaN` only the word with all exponent and
all fraction bits set is NaN, for either sign; under `finiteUnsignedZero` only the word equal to
the sign mask (negative zero) is NaN and only the all-zero word is zero; under `finite` every word
is a number. The value of a finite word follows `toDyadic?` in
FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean and `ieeeToDyadic?` in
Dyadic/Core.lean: a zero exponent field denotes fraction * 2^(1 - bias - fracWidth), any other
exponent field E denotes (2^fracWidth + fraction) * 2^(E - bias - fracWidth).

Before drawing, the script checks its own arithmetic against two `-- ` results printed in the
chapter: the sixteen E2M1 codes decode to 0, 1/2, 1, 3/2, 2, 3, 4, 6 and their negatives, and the
largest finite values of e2m1, e2m3, e3m2, e4m3fn, e4m3fnuz, e5m2, e5m2fnuz are
6, 15/2, 28, 448, 240, 57344, 57344.

Run from anywhere: python3 ch13_element_values.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.lines import Line2D  # noqa: E402

IEEE, FINITE_MAX_NAN, FINITE_UNSIGNED_ZERO, FINITE = "ieee", "finiteMaxNaN", "finiteUnsignedZero", "finite"


def ieee_bias(exp_width: int) -> int:
    """`FloatFormat.ieeeBias`."""
    return 2 ** (exp_width - 1) - 1


def descriptor(name: str, encoding: str, exp_width: int, frac_width: int) -> dict:
    """The four data fields of a `FloatFormat` built by the named constructor."""
    bias = ieee_bias(exp_width) + (1 if encoding == FINITE_UNSIGNED_ZERO else 0)
    return {"name": name, "encoding": encoding, "expWidth": exp_width, "fracWidth": frac_width,
            "bias": bias}


# In the order the chapter introduces them.
FORMATS = (
    descriptor("E5M2", IEEE, 5, 2),
    descriptor("E4M3FN", FINITE_MAX_NAN, 4, 3),
    descriptor("E4M3FNUZ", FINITE_UNSIGNED_ZERO, 4, 3),
    descriptor("E5M2FNUZ", FINITE_UNSIGNED_ZERO, 5, 2),
    descriptor("E2M3", FINITE, 2, 3),
    descriptor("E3M2", FINITE, 3, 2),
    descriptor("E2M1", FINITE, 2, 1),
)


def fields(fmt: dict, word: int) -> tuple[int, int, int]:
    """Sign, exponent field, fraction field of a stored word."""
    frac = word & ((1 << fmt["fracWidth"]) - 1)
    exp = (word >> fmt["fracWidth"]) & ((1 << fmt["expWidth"]) - 1)
    sign = word >> (fmt["expWidth"] + fmt["fracWidth"])
    return sign, exp, frac


def is_nan(fmt: dict, word: int) -> bool:
    sign, exp, frac = fields(fmt, word)
    all_ones_exp = (1 << fmt["expWidth"]) - 1
    all_ones_frac = (1 << fmt["fracWidth"]) - 1
    if fmt["encoding"] == IEEE:
        return exp == all_ones_exp and frac != 0
    if fmt["encoding"] == FINITE_MAX_NAN:
        return exp == all_ones_exp and frac == all_ones_frac
    if fmt["encoding"] == FINITE_UNSIGNED_ZERO:
        return word == 1 << (fmt["expWidth"] + fmt["fracWidth"])  # the sign mask
    return False


def is_inf(fmt: dict, word: int) -> bool:
    _sign, exp, frac = fields(fmt, word)
    return fmt["encoding"] == IEEE and exp == (1 << fmt["expWidth"]) - 1 and frac == 0


def to_rational(fmt: dict, word: int) -> Fraction | None:
    """`Model.toDyadic?` as an exact rational; None for infinities and NaNs."""
    if is_nan(fmt, word) or is_inf(fmt, word):
        return None
    sign, exp, frac = fields(fmt, word)
    if fmt["encoding"] == FINITE_UNSIGNED_ZERO and word == 0:
        return Fraction(0)
    if exp == 0:
        value = Fraction(frac) * Fraction(2) ** (1 - fmt["bias"] - fmt["fracWidth"])
    else:
        value = Fraction((1 << fmt["fracWidth"]) + frac) * Fraction(2) ** (exp - fmt["bias"] - fmt["fracWidth"])
    return -value if sign else value


def positive_values(fmt: dict) -> tuple[list[Fraction], list[Fraction]]:
    """Positive finite nonzero values, split into (normals, subnormals)."""
    normals, subnormals = [], []
    for exp in range(1 << fmt["expWidth"]):
        for frac in range(1 << fmt["fracWidth"]):
            word = (exp << fmt["fracWidth"]) | frac
            value = to_rational(fmt, word)
            if value is None or value == 0:
                continue
            (subnormals if exp == 0 else normals).append(value)
    return normals, subnormals


def check_against_chapter() -> None:
    by_name = {f["name"]: f for f in FORMATS}
    e2m1 = by_name["E2M1"]
    codes = [to_rational(e2m1, code) for code in range(16)]
    expected = [Fraction(v) for v in (0, "1/2", 1, "3/2", 2, 3, 4, 6, 0, "-1/2", -1, "-3/2", -2, -3, -4, -6)]
    assert codes == expected, codes
    maxima = [max(positive_values(by_name[n])[0]) for n in
              ("E2M1", "E2M3", "E3M2", "E4M3FN", "E4M3FNUZ", "E5M2", "E5M2FNUZ")]
    assert maxima == [Fraction(v) for v in (6, "15/2", 28, 448, 240, 57344, 57344)], maxima


def rational_label(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def power_of_two_label(value: Fraction) -> str:
    """`2^k` for a value of the form 1/2^k (every least subnormal here is one), else the fraction."""
    if value.numerator == 1 and value.denominator & (value.denominator - 1) == 0:
        return f"$2^{{{-(value.denominator.bit_length() - 1)}}}$"
    return rational_label(value)


SIGN_COLOUR = fs.MUTED
EXP_COLOUR = fs.ORANGE
FRAC_COLOUR = fs.SKY
NORMAL_COLOUR = fs.BLUE
SUBNORMAL_COLOUR = fs.VERMILION

LAYOUT_SCALE = 3          # axis units per bit in the layout panel, so one-bit fields get a label
ROW_HEIGHT = 0.5


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    check_against_chapter()
    fs.setup()

    n = len(FORMATS)
    fig = fs.figure(5.4)[0]
    fig.clf()
    # Two panels sharing the rows: layouts at the left, values at the right.
    ax_layout = fig.add_axes([0.135, 0.13, 0.16, 0.76])
    ax_values = fig.add_axes([0.325, 0.13, 0.66, 0.76])

    rows = list(range(n))[::-1]
    ylabels = []
    for y, fmt in zip(rows, FORMATS):
        normals, subnormals = positive_values(fmt)
        ylabels.append(f"{fmt['name']}\n{len(normals) + len(subnormals)} positive values")

        # Layout, most significant bit at the left, drawn to one scale in every row.
        layout_fields = [
            ("S", 1, SIGN_COLOUR),
            (f"E{fmt['expWidth']}", fmt["expWidth"], EXP_COLOUR),
            (f"M{fmt['fracWidth']}", fmt["fracWidth"], FRAC_COLOUR),
        ]
        fs.bit_layout(ax_layout, layout_fields, y=y - ROW_HEIGHT / 2, height=ROW_HEIGHT,
                      label_bits=False, scale=LAYOUT_SCALE, name_size=9)

        # Values.
        xs_n = [float(v) for v in normals]
        xs_s = [float(v) for v in subnormals]
        ax_values.vlines(xs_n, y - 0.3, y + 0.3, color=NORMAL_COLOUR, linewidth=0.8)
        ax_values.vlines(xs_s, y - 0.17, y + 0.17, color=SUBNORMAL_COLOUR, linewidth=0.8)
        largest = max(normals)
        ax_values.annotate(f"max {rational_label(largest)}", (float(largest), y),
                           textcoords="offset points", xytext=(7, 0), ha="left", va="center",
                           fontsize=9, color=fs.INK)
        smallest = min(subnormals)
        ax_values.annotate(power_of_two_label(smallest), (float(smallest), y),
                           textcoords="offset points", xytext=(-7, 0), ha="right", va="center",
                           fontsize=9, color=fs.INK)

    ax_layout.set_xlim(-0.5, 8 * LAYOUT_SCALE + 0.5)
    ax_layout.set_ylim(-0.6, n - 0.4)
    ax_layout.set_yticks(rows)
    ax_layout.set_yticklabels(ylabels, fontsize=9.5, linespacing=1.4)
    ax_layout.tick_params(axis="y", length=0)
    ax_layout.set_xticks([])
    ax_layout.grid(False)
    for side in ("left", "bottom"):
        ax_layout.spines[side].set_visible(False)
    ax_layout.set_title("stored word, to scale", loc="left", fontsize=10)

    ax_values.set_xscale("log", base=2)
    ax_values.set_xlim(2.0 ** -21, 2.0 ** 19.5)
    ticks = [2.0 ** k for k in range(-16, 17, 4)]
    ax_values.set_xticks(ticks)
    ax_values.set_xticklabels([f"$2^{{{k}}}$" if k else "$1$" for k in range(-16, 17, 4)])
    ax_values.minorticks_off()
    ax_values.set_ylim(-0.6, n - 0.4)
    ax_values.set_yticks(rows)
    ax_values.set_yticklabels([])
    ax_values.tick_params(axis="y", length=0)
    ax_values.grid(axis="y", visible=False)
    ax_values.set_xlabel("value (each positive finite value is one tick)")
    ax_values.set_title("every positive finite value", loc="left", fontsize=10)

    handles = [
        Line2D([], [], marker="|", markersize=12, markeredgewidth=1.2, color=NORMAL_COLOUR,
               linestyle="None", label="normal value (tall tick)"),
        Line2D([], [], marker="|", markersize=7, markeredgewidth=1.2, color=SUBNORMAL_COLOUR,
               linestyle="None", label="subnormal value (short tick)"),
    ]
    # The lower left of the value panel is empty (the small formats sit near one), so the legend
    # lives there rather than crowding the panel title.
    ax_values.legend(handles=handles, loc="lower left", ncol=1, fontsize=9.5, handletextpad=0.4,
                     labelspacing=0.9)

    out = fs.save(fig, "ch13-element-values.png", out=args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
