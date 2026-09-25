#!/usr/bin/env python3
"""Draw content/assets/ch13-mx-block.png: shared scales and one exact dot product.

Chapter 09 works one OCP MX example in Lean: a `BlockCode FloatFormat.e2m1` of four E2M1 weights
sharing the E8M0 scale code 125 and a block of four E2M1 activations sharing the scale code 128,
decoded jointly, multiplied lane by lane in exact dyadic arithmetic, summed, and rounded once
into bfloat16 and once into E4M3FN. This figure shows the four element values before and after
their shared scale is applied, then follows the lane products to an exact sum. Both rounded
outputs branch from that sum. The phone version stacks the blocks and the output choices.

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

import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

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


def vector(values) -> str:
    return "[" + ",  ".join(frac_text(v) for v in values) + "]"


def draw(mobile: bool):
    fig = plt.figure(figsize=(3.8, 9.0) if mobile else (9, 5.5))
    fig.text(0.035, 0.98, "Shared scales, one exact dot product", fontsize=13.5,
             weight="bold", va="top")
    fig.text(0.035, 0.925 if mobile else 0.90,
             "Worked example with four E2M1 lanes", fontsize=11.5, color=fs.MUTED)
    canvas = fig.add_axes([0, 0, 1, 1], zorder=0)
    canvas.set(xlim=(0, 1), ylim=(0, 1))
    canvas.axis("off")
    block_rects = ([(0.035, 0.69, 0.93, 0.18), (0.035, 0.46, 0.93, 0.18)] if mobile else
                   [(0.035, 0.57, 0.44, 0.25), (0.525, 0.57, 0.44, 0.25)])
    for block, rect in zip((WEIGHTS, ACTIVATIONS), block_rects):
        unscaled, scaled, shift = decode_block(block)
        ax = fig.add_axes(rect)
        ax.set(xlim=(0, 1), ylim=(0, 1))
        ax.axis("off")
        ax.add_patch(Rectangle((0, 0), 1, 1, fc=fs.PAPER_2, ec=fs.LINE, lw=0.8))
        ax.text(0.05, 0.83, block[0].capitalize(), fontsize=12, weight="bold")
        ax.text(0.05, 0.62, f"E8M0 code {block[1]}: multiply by $2^{{{shift}}}$", fontsize=11.5)
        ax.text(0.05, 0.39, vector(unscaled), fontsize=12)
        ax.text(0.05, 0.15, "→  " + vector(scaled), fontsize=12, color=fs.BLUE)
    products = [x * y for x, y in zip(CHAPTER_WEIGHTS, CHAPTER_ACTIVATIONS)]
    assert products == [Fraction(1), Fraction(3, 4), Fraction(-3), Fraction(-3)]
    product_y, sum_y = (0.385, 0.29) if mobile else (0.43, 0.31)
    for x, y, w, h in block_rects:
        # Both decoded blocks feed the same componentwise multiplication.
        if mobile and y > 0.6:
            canvas.plot([x + w, 0.985, 0.985],
                        [y + h / 2, y + h / 2, product_y + 0.035],
                        color=fs.MUTED, lw=1.1)
            canvas.annotate("", (0.70, product_y + 0.035), (0.985, product_y + 0.035),
                            arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.1))
        else:
            canvas.annotate("", (0.50, product_y + 0.035), (x + w / 2, y - 0.005),
                            arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.1))
    fig.text(0.5, product_y, "Lane products: " + vector(products), ha="center", fontsize=12)
    canvas.annotate("", (0.5, sum_y + 0.04), (0.5, product_y - 0.01),
                    arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.1))
    fig.text(0.5, sum_y, "Exact sum: −17/4 = −4.25", ha="center", fontsize=14, weight="bold")
    # Each output is rounded independently from the exact sum; there is no output-to-output arrow.
    outputs = ([(0.06, 0.145, 0.88, 0.082), (0.06, 0.035, 0.88, 0.082)] if mobile else
               [(0.08, 0.06, 0.38, 0.11), (0.54, 0.06, 0.38, 0.11)])
    for i, rect in enumerate(outputs):
        x, y, w, h = rect
        canvas.add_patch(Rectangle((x, y), w, h, facecolor=fs.PAPER_2, edgecolor=fs.LINE, lw=0.8))
        text = ("bfloat16: −4.25 (exact)" if i == 0 else "E4M3FN: −4 (tie to even)")
        canvas.text(x + 0.04, y + h * 0.56, text, fontsize=12, va="center")
    if mobile:
        # A vertical bracket makes the common exact source explicit, even with stacked outputs.
        canvas.plot([0.5, 0.025, 0.025], [sum_y - 0.012, sum_y - 0.012, 0.071],
                    color=fs.MUTED, lw=1.1)
        for x, y, w, h in outputs:
            canvas.annotate("", (x, y + h / 2), (0.025, y + h / 2),
                            arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.1))
        fig.text(0.10, 0.247, "Round this sum once to either format:", fontsize=11.5)
    else:
        for x, y, w, h in outputs:
            canvas.annotate("", (x + w / 2, y + h), (0.5, 0.205),
                            arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.1))
        canvas.annotate("", (0.5, 0.26), (0.5, sum_y - 0.01),
                        arrowprops=dict(arrowstyle="->", color=fs.MUTED, lw=1.1))
        fig.text(0.5, 0.225, "Round the exact sum once to either format", ha="center", fontsize=11.5)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    check_against_chapter()
    assert e4m3fn_value(CHAPTER_E4M3FN_WORD + 1) == Fraction(-9, 2)
    assert (CHAPTER_E4M3FN_VALUE + Fraction(-9, 2)) / 2 == CHAPTER_DOT
    assert CHAPTER_E4M3FN_WORD % 2 == 0
    fs.setup()
    out = args.out or fs.ASSETS / "ch13-mx-block.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
