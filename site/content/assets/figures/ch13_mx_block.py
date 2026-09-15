#!/usr/bin/env python3
"""Draw content/assets/ch13-mx-block.png: the chapter's block scaled product, bit by bit.

Chapter 09 works one OCP MX example in Lean: a `BlockCode FloatFormat.e2m1` of four E2M1 weights
sharing the E8M0 scale code 125 and a block of four E2M1 activations sharing the scale code 128,
decoded jointly, multiplied lane by lane in exact dyadic arithmetic, summed, and rounded once
into bfloat16 and once into E4M3FN. This figure lays the two blocks out as boxes drawn to scale
(one width per bit: an eight-bit scale beside four four-bit elements), shows what each element
word means on its own and after the block's scale is applied, and follows the numbers down to the
two rounded results.

Sources. Every code is the chapter's own Lean text (`weights` and `activations` in section "E8M0
and microscaling blocks"): scale codes 125 and 128, element words 0x2, 0x5, 0xb, 0x7 and 0x4,
0x1, 0x6, 0xa. Every value is the chapter's own `-- ` result: the decoded blocks
#[1/4, 3/4, -3/8, 3/2] and #[4, 1, 8, -2], the exact dot product -17/4, the bfloat16 word 49288
(0xc088, exactly -4.25) and the E4M3FN word 200 (0xc8, which is -4). The unscaled element values
are read off the E2M1 code table the chapter prints (codes 0 to 15). The script recomputes each
of these from the format parameters (E2M1 = `finite 2 1`, bias 1, in
FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean; E8M0 code c denotes 2^(c - 127),
`E8M0.exponent?` in FloatLib/Floats/Formats/OCP/MX/E8M0/Core.lean) and stops with an error if
any of them disagrees with the chapter, so the drawing and the prose cannot drift apart.

The block has four elements because that is the block the chapter builds; the chapter does not
state the block length the MX specification requires, and neither does this figure.

Run from anywhere: python3 ch13_mx_block.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.patches import Patch, Rectangle  # noqa: E402

# The chapter's two blocks: E8M0 scale code, then the four E2M1 element words.
WEIGHTS = ("weights", 125, (0x2, 0x5, 0xb, 0x7))
ACTIVATIONS = ("activations", 128, (0x4, 0x1, 0x6, 0xa))

# The chapter's `-- ` results, which the arithmetic below must reproduce.
CHAPTER_WEIGHTS = [Fraction(1, 4), Fraction(3, 4), Fraction(-3, 8), Fraction(3, 2)]
CHAPTER_ACTIVATIONS = [Fraction(4), Fraction(1), Fraction(8), Fraction(-2)]
CHAPTER_DOT = Fraction(-17, 4)
CHAPTER_BF16_WORD, CHAPTER_BF16_VALUE = 49288, Fraction(-17, 4)
CHAPTER_E4M3FN_WORD, CHAPTER_E4M3FN_VALUE = 200, Fraction(-4)

E2M1_EXP_WIDTH, E2M1_FRAC_WIDTH, E2M1_BIAS = 2, 1, 1   # `finite 2 1`, bias ieeeBias 2 = 1
E8M0_BIAS = 127

SIGN_COLOUR = fs.MUTED
EXP_COLOUR = fs.ORANGE
FRAC_COLOUR = fs.SKY


def e2m1_value(word: int) -> Fraction:
    """`Model.toDyadic?` at e2m1 (every word is finite): fields, then the two-case rule."""
    frac = word & ((1 << E2M1_FRAC_WIDTH) - 1)
    exp = (word >> E2M1_FRAC_WIDTH) & ((1 << E2M1_EXP_WIDTH) - 1)
    sign = word >> (E2M1_EXP_WIDTH + E2M1_FRAC_WIDTH)
    if exp == 0:
        value = Fraction(frac) * Fraction(2) ** (1 - E2M1_BIAS - E2M1_FRAC_WIDTH)
    else:
        value = Fraction((1 << E2M1_FRAC_WIDTH) + frac) * Fraction(2) ** (exp - E2M1_BIAS - E2M1_FRAC_WIDTH)
    return -value if sign else value


def e8m0_exponent(code: int) -> int:
    """`E8M0.exponent?` for a non-NaN code."""
    assert code != 255
    return code - E8M0_BIAS


def bfloat16_value(word: int) -> Fraction:
    """Decode a bfloat16 word (ieee 8 7, bias 127) that is finite and normal."""
    frac = word & 0x7f
    exp = (word >> 7) & 0xff
    sign = word >> 15
    assert 0 < exp < 255
    value = Fraction(128 + frac) * Fraction(2) ** (exp - 127 - 7)
    return -value if sign else value


def e4m3fn_value(word: int) -> Fraction:
    """Decode an E4M3FN word (finiteMaxNaN 4 3, bias 7) that is finite and normal."""
    frac = word & 0x7
    exp = (word >> 3) & 0xf
    sign = word >> 7
    assert exp > 0 and not (exp == 15 and frac == 7)
    value = Fraction(8 + frac) * Fraction(2) ** (exp - 7 - 3)
    return -value if sign else value


def decode_block(block) -> tuple[list[Fraction], list[Fraction], int]:
    _name, scale_code, words = block
    shift = e8m0_exponent(scale_code)
    unscaled = [e2m1_value(w) for w in words]
    scaled = [v * Fraction(2) ** shift for v in unscaled]
    return unscaled, scaled, shift


def check_against_chapter() -> None:
    _u, w, _s = decode_block(WEIGHTS)
    _u, a, _s = decode_block(ACTIVATIONS)
    assert w == CHAPTER_WEIGHTS, w
    assert a == CHAPTER_ACTIVATIONS, a
    dot = sum((x * y for x, y in zip(w, a)), Fraction(0))
    assert dot == CHAPTER_DOT, dot
    assert bfloat16_value(CHAPTER_BF16_WORD) == CHAPTER_BF16_VALUE
    assert e4m3fn_value(CHAPTER_E4M3FN_WORD) == CHAPTER_E4M3FN_VALUE


def frac_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def field_boxes(ax, x: float, y: float, height: float, parts, fontsize: float = 9.5) -> float:
    """Adjacent one-unit-per-bit boxes; `parts` is a list of (bit string, colour). Returns the
    right edge. Unlike fs.bit_layout this prints the bits themselves inside every field, however
    narrow, which is what a worked example needs."""
    for bits, colour in parts:
        width = len(bits)
        ax.add_patch(Rectangle((x, y), width, height, facecolor=colour, edgecolor=fs.INK,
                               linewidth=0.9, alpha=0.9))
        ax.text(x + width / 2, y + height / 2, " ".join(bits), ha="center", va="center",
                fontsize=fontsize, color=fs.INK, family="DejaVu Sans Mono")
        x += width
    return x


def e2m1_parts(word: int):
    bits = format(word, "04b")
    return [(bits[0], SIGN_COLOUR), (bits[1:3], EXP_COLOUR), (bits[3], FRAC_COLOUR)]


# Geometry in bit units: the scale box is 8 wide, each element 4 wide, with gaps of 0.6.
SCALE_X = 0.0
SCALE_W = 8
ELEMENT_W = 4
GAP = 0.6
FIRST_ELEMENT_X = SCALE_X + SCALE_W + 1.4
BOX_H = 1.3
LABEL_X = -0.8            # right edge of the row labels


def element_x(i: int) -> float:
    return FIRST_ELEMENT_X + i * (ELEMENT_W + GAP)


def element_centre(i: int) -> float:
    return element_x(i) + ELEMENT_W / 2


def draw_block(ax, block, y_top: float) -> None:
    """One block: the boxes, the value of each element word, and the value after scaling."""
    name, scale_code, words = block
    unscaled, scaled, shift = decode_block(block)
    y_box = y_top - BOX_H
    ax.text(LABEL_X, y_box + BOX_H / 2, name, ha="right", va="center", fontsize=10.5,
            fontweight="bold", color=fs.INK)
    field_boxes(ax, SCALE_X, y_box, BOX_H, [(format(scale_code, "08b"), EXP_COLOUR)])
    for i, word in enumerate(words):
        field_boxes(ax, element_x(i), y_box, BOX_H, e2m1_parts(word))

    # Row 1: what each word means on its own.
    y1 = y_box - 1.0
    ax.text(LABEL_X, y1, "code alone", ha="right", va="center", fontsize=9.5, color=fs.MUTED)
    ax.text(SCALE_X + SCALE_W / 2, y1, f"$2^{{{scale_code} - 127}} = 2^{{{shift}}}$",
            ha="center", va="center", fontsize=9.5)
    for i, value in enumerate(unscaled):
        ax.text(element_centre(i), y1, frac_text(value), ha="center", va="center", fontsize=10)

    # Row 2: after the block's scale, with a bus from the scale box to every element.
    y2 = y1 - 1.15
    ax.text(LABEL_X, y2, f"times $2^{{{shift}}}$", ha="right", va="center", fontsize=9.5,
            color=fs.MUTED)
    y_bus = (y1 + y2) / 2 + 0.05
    ax.plot([SCALE_X + SCALE_W / 2, SCALE_X + SCALE_W / 2, element_centre(len(words) - 1)],
            [y1 - 0.3, y_bus, y_bus], color=fs.INK, linewidth=0.8)
    for i, value in enumerate(scaled):
        fs.arrow(ax, (element_centre(i), y_bus), (element_centre(i), y2 + 0.3), linewidth=0.8,
                 shrink=0.0)
        ax.text(element_centre(i), y2, frac_text(value), ha="center", va="center", fontsize=10,
                fontweight="bold")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    check_against_chapter()
    fs.setup()

    _u, w, _s = decode_block(WEIGHTS)
    _u, a, _s = decode_block(ACTIVATIONS)
    products = [x * y for x, y in zip(w, a)]
    dot = sum(products, Fraction(0))

    right_edge = element_x(3) + ELEMENT_W
    xlim = (LABEL_X - 5.4, right_edge + 0.8)
    ylim = (-17.4, 1.9)
    # Equal aspect: the height follows from the extent of the drawing, so nothing is letterboxed.
    fig = fs.figure(fs.WIDTH * (ylim[1] - ylim[0]) / (xlim[1] - xlim[0]))[0]
    fig.clf()
    ax = fs.diagram_axes(fig, xlim, ylim)

    # Column headers over the first block.
    ax.text(SCALE_X + SCALE_W / 2, 1.0, "E8M0 scale, 8 bits", ha="center", va="center",
            fontsize=9.5, color=fs.MUTED)
    ax.text((element_x(0) + element_x(3) + ELEMENT_W) / 2, 1.0, "four E2M1 elements, 4 bits each",
            ha="center", va="center", fontsize=9.5, color=fs.MUTED)

    draw_block(ax, WEIGHTS, 0.0)
    draw_block(ax, ACTIVATIONS, -5.4)

    # Lane products, exact sum, and the two roundings.
    y_prod = -11.4
    ax.text(LABEL_X, y_prod, "lane products", ha="right", va="center", fontsize=9.5, color=fs.MUTED)
    for i, (x, y, p) in enumerate(zip(w, a, products)):
        y_text = f"({frac_text(y)})" if y < 0 else frac_text(y)
        ax.text(element_centre(i), y_prod, f"{frac_text(x)} $\\times$ {y_text} = {frac_text(p)}",
                ha="center", va="center", fontsize=10)

    y_sum = y_prod - 1.4
    centre = (element_x(0) + element_x(3) + ELEMENT_W) / 2
    ax.text(LABEL_X, y_sum, "exact sum", ha="right", va="center", fontsize=9.5, color=fs.MUTED)
    ax.plot([element_x(0), element_x(3) + ELEMENT_W], [y_prod - 0.6, y_prod - 0.6],
            color=fs.INK, linewidth=0.8)
    ax.text(centre, y_sum, " + ".join(f"({frac_text(p)})" if p < 0 else frac_text(p) for p in products)
            + f" = {frac_text(dot)}", ha="center", va="center", fontsize=10, fontweight="bold")

    box_w = element_x(3) + ELEMENT_W - element_x(0)
    box_h = 1.2
    y_box1 = y_sum - 1.2 - box_h          # bottom of the first result box
    y_box2 = y_box1 - 0.4 - box_h         # bottom of the second
    ax.text(LABEL_X, (y_box1 + y_box2 + box_h) / 2, "rounded once", ha="right", va="center",
            fontsize=9.5, color=fs.MUTED)
    fs.arrow(ax, (centre, y_sum - 0.45), (centre, y_box1 + box_h), linewidth=0.8, shrink=0.0)
    bf = bfloat16_value(CHAPTER_BF16_WORD)
    e4 = e4m3fn_value(CHAPTER_E4M3FN_WORD)
    fs.box(ax, element_x(0), y_box1, box_w, box_h,
           f"into bfloat16: word 0x{CHAPTER_BF16_WORD:04x}, exactly {float(bf):g}", fontsize=9.5)
    fs.box(ax, element_x(0), y_box2, box_w, box_h,
           f"into E4M3FN: word 0x{CHAPTER_E4M3FN_WORD:02x}, which is {frac_text(e4)} "
           "(a tie, rounded to even)", fontsize=9.5)

    handles = [
        Patch(facecolor=SIGN_COLOUR, edgecolor=fs.INK, linewidth=0.9, label="sign bit"),
        Patch(facecolor=EXP_COLOUR, edgecolor=fs.INK, linewidth=0.9, label="exponent bits"),
        Patch(facecolor=FRAC_COLOUR, edgecolor=fs.INK, linewidth=0.9, label="fraction bit"),
    ]
    # The scale column is empty below the two blocks, so the legend goes there.
    ax.legend(handles=handles, loc="upper left", bbox_to_anchor=(SCALE_X, y_prod + 0.7),
              bbox_transform=ax.transData, ncol=1, fontsize=9.5, handlelength=1.4,
              borderaxespad=0.0, labelspacing=0.7)

    out = fs.save(fig, "ch13-mx-block.png", out=args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
