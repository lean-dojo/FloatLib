#!/usr/bin/env python3
"""Draw content/assets/ch13-mx-block.png: shared scales and one exact dot product.

The chapter on machine-learning formats works one OCP MX example in Lean: a `Block.Tensor` of four E2M1 weights
sharing the E8M0 scale code 125 and a block of four E2M1 activations sharing the scale code 128,
decoded jointly, multiplied lane by lane in exact dyadic arithmetic, summed, and rounded once
into bfloat16 and once into E4M3. This figure shows the four element values before and after
their shared scale is applied, then follows the lane products to an exact sum. Both rounded
outputs branch from that sum. The phone version stacks the blocks and the output choices.

Sources. Every code is the chapter's own Lean text (`weights` and `activations` in section "E8M0
and microscaling blocks"): scale codes 125 and 128, element words 0x2, 0x5, 0xb, 0x7 and 0x4,
0x1, 0x6, 0xa. Every value is the chapter's own `-- ` result: the decoded blocks
#[1/4, 3/4, -3/8, 3/2] and #[4, 1, 8, -2], the exact dot product -17/4, the bfloat16 word 49288
(0xc088, exactly -4.25) and the E4M3 word 200 (0xc8, which is -4). The unscaled element values
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
    """Decode an E4M3 word (finiteMaxNaN 4 3, bias 7) that is finite and normal."""
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
    sign = "−" if value < 0 else ""
    if value.denominator == 1:
        return f"{sign}{abs(value.numerator)}"
    return f"{sign}{abs(value.numerator)}/{value.denominator}"


def vector(values) -> str:
    return "[" + ",  ".join(frac_text(v) for v in values) + "]"


def node(ax, x, y, w, h, label, lines):
    """An outlined node: its name in the corner, its values centred."""
    fs.box(ax, x, y, w, h)
    ax.text(x + 0.12, y + h - 0.2, label, fontsize=fs.SIZE_TICK, color=fs.MUTED, va="center")
    body = y + (h - 0.36) / 2
    step = 0.32
    start = body + step * (len(lines) - 1) / 2
    for index, line in enumerate(lines):
        ax.text(x + w / 2, start - index * step, line, fontsize=fs.SIZE_LABEL, ha="center",
                va="center")


def draw(mobile: bool):
    """Two scaled blocks, their lane products, the exact sum, and one rounding per output."""
    width, height = (fs.MOBILE_WIDTH, 8.0) if mobile else (fs.WIDTH, 4.9)
    fig = plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    blocks = []
    for block in (WEIGHTS, ACTIVATIONS):
        unscaled, scaled, shift = decode_block(block)
        blocks.append((block[0], [f"{vector(unscaled)}  ×  $2^{{{shift}}}$",
                                  f"=  {vector(scaled)}"], f"scale code {block[1]}"))
    products = [x * y for x, y in zip(CHAPTER_WEIGHTS, CHAPTER_ACTIVATIONS)]
    assert products == [Fraction(1), Fraction(3, 4), Fraction(-3), Fraction(-3)]
    assert sum(products) == CHAPTER_DOT == Fraction(-17, 4)
    outputs = [("bfloat16", frac_text(CHAPTER_BF16_VALUE)), ("E4M3", frac_text(CHAPTER_E4M3FN_VALUE))]
    if mobile:
        w = width - 0.4
        ys = [6.55, 4.95, 3.75, 2.65, 1.3, 0.15]
        for (name, lines, code), y in zip(blocks, ys[:2]):
            node(ax, 0.2, y, w, 1.3, f"{name}, {code}", lines)
        node(ax, 0.2, ys[2], w, 0.85, "lane products", [vector(products)])
        node(ax, 0.2, ys[3], w, 0.85, "exact sum", [frac_text(CHAPTER_DOT)])
        for (name, value), y in zip(outputs, ys[4:]):
            node(ax, 0.2, y, w, 0.85, name, [value])
        centre = width / 2
        fs.arrow(ax, (centre, ys[0]), (centre, ys[1] + 1.3))
        fs.arrow(ax, (centre, ys[1]), (centre, ys[2] + 0.85))
        fs.arrow(ax, (centre, ys[2]), (centre, ys[3] + 0.85))
        fs.arrow(ax, (centre - 0.6, ys[3]), (centre - 0.6, ys[4] + 0.85))
        ax.text(centre - 0.45, (ys[3] + ys[4] + 0.85) / 2, "round", fontsize=fs.SIZE_TICK,
                va="center")
        # The second output is rounded from the exact sum too, not from the first output.
        ax.plot([width - 0.2, width - 0.07, width - 0.07], [ys[3] + 0.42, ys[3] + 0.42,
                                                           ys[5] + 0.42], color=fs.INK,
                lw=fs.LW_REF)
        fs.arrow(ax, (width - 0.07, ys[5] + 0.42), (width - 0.2, ys[5] + 0.42))
    else:
        for (name, lines, code), x in zip(blocks, (0.3, 4.7)):
            node(ax, x, 3.45, 4.0, 1.3, f"{name}, {code}", lines)
        node(ax, 2.5, 2.25, 4.0, 0.85, "lane products", [vector(products)])
        node(ax, 3.25, 1.2, 2.5, 0.85, "exact sum", [frac_text(CHAPTER_DOT)])
        for (name, value), x in zip(outputs, (1.0, 5.5)):
            node(ax, x, 0.15, 2.5, 0.75, name, [value])
        fs.arrow(ax, (2.3, 3.45), (3.5, 3.1))
        fs.arrow(ax, (6.7, 3.45), (5.5, 3.1))
        fs.arrow(ax, (4.5, 2.25), (4.5, 2.05))
        # Each output is rounded independently from the exact sum.
        fs.arrow(ax, (3.25, 1.45), (2.25, 0.9))
        fs.arrow(ax, (5.75, 1.45), (6.75, 0.9))
        ax.text(2.45, 1.25, "round", fontsize=fs.SIZE_TICK, ha="right", va="center")
        ax.text(6.55, 1.25, "round", fontsize=fs.SIZE_TICK, ha="left", va="center")
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
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
