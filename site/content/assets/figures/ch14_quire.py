#!/usr/bin/env python3
"""Draw content/assets/ch14-quire.png: the 512-bit quire of a 32-bit posit as a fixed-point word.

Chapter 11 gives the quire of an n-bit posit as a signed two's-complement word of 16n bits whose
least significant bit is worth 2^(16 - 8n), and works out the capacity argument in words: the
square of the largest posit is 2^240, and 2^31 such products come to exactly 2^511 coefficient
units, one past the largest ordinary quire coefficient. This figure draws the word to scale,
bit 511 on the left, with three value landmarks and the thirty carry bits above the largest
product. Its capacity strip states the strict bound from a zero accumulator for finite
products; the longer derivation stays in the chapter.

Everything drawn is arithmetic on the parameters of FloatLib/Floats/Formats/Posit/Quire/Model/
Core.lean (width = 16 * bits, scaleExponent = 16 - 8 * bits) and of
FloatLib/Floats/Formats/Posit/Descriptor.lean for the posit range, which the chapter states as
[2^-120, 2^120] for 32 bits: bit i of the quire has weight 2^(i + scaleExponent), so the least
significant bit is 2^-240 (the square of the smallest posit), bit 240 is one, bit 120 is the
smallest posit, bit 360 is the largest posit, bit 480 is the square of the largest posit, bits 481
to 510 are the thirty bits above it, and bit 511 is the sign.

Run from anywhere: python3 ch14_quire.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

POSIT_BITS = 32
WIDTH = 16 * POSIT_BITS                 # Quire.width = 512
SCALE_EXPONENT = 16 - 8 * POSIT_BITS    # Quire.scaleExponent = -240
MAX_POSIT_EXPONENT = 4 * (POSIT_BITS - 2)   # regime of payloadBits ones: 4 * (n - 2) = 120

BIT_ONE = -SCALE_EXPONENT                          # weight 2^0
BIT_MIN_POSIT = BIT_ONE - MAX_POSIT_EXPONENT       # weight 2^-120
BIT_MAX_PRODUCT = BIT_ONE + 2 * MAX_POSIT_EXPONENT  # weight 2^240
BIT_SIGN = WIDTH - 1
HEADROOM = BIT_SIGN - BIT_MAX_PRODUCT - 1          # 30 bits strictly between them

assert BIT_MIN_POSIT * 2 == BIT_ONE == 240, (BIT_MIN_POSIT, BIT_ONE)
assert BIT_MAX_PRODUCT == 480 and HEADROOM == 30


def x_of(bit: int) -> float:
    """Left edge of a bit; bit 511 is drawn at the left and bit 0 at the right."""
    return BIT_SIGN - bit


def draw(mobile: bool):
    fig = plt.figure(figsize=(3.8, 5.8) if mobile else (9, 3.85))
    fig.text(0.035, 0.97, "Room for exact products", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.87 if mobile else 0.83,
             r"Posit32 quire: 512 bits, scale $2^{-240}$", fontsize=12, color=fs.MUTED)
    ax = fig.add_axes([0.05, 0.43, 0.90, 0.35] if mobile else [0.04, 0.34, 0.92, 0.37])
    ax.set(xlim=(-6, WIDTH + 6), ylim=(-1.15, 2.7))
    ax.axis("off")
    segments = [(BIT_SIGN, BIT_SIGN, fs.VERMILION),
                (BIT_MAX_PRODUCT + 1, BIT_SIGN - 1, fs.GREEN),
                (BIT_ONE, BIT_MAX_PRODUCT, fs.BLUE), (0, BIT_ONE - 1, fs.SKY)]
    for lo, hi, colour in segments:
        ax.add_patch(Rectangle((x_of(hi), 0), hi - lo + 1, 0.7,
                               facecolor=colour, edgecolor=fs.INK, lw=0.6))
    for bit, y, label in [(BIT_SIGN, 2.25, "sign: bit 511"),
                           (496, 1.35, "30 carry bits: 481 to 510")]:
        x = x_of(bit) + 0.5
        ax.plot([x, x], [0.72, y - 0.08], color=fs.MUTED, lw=0.9)
        ax.text(x + 4, y, label, fontsize=11.5, va="center")
    point = x_of(BIT_ONE - 1)
    ax.plot([point, point], [-0.04, 0.82], color=fs.INK, lw=1.5)
    for bit, value, ha in [(BIT_MAX_PRODUCT, r"$2^{240}$", "left" if mobile else "center"),
                            (BIT_ONE, "$1$", "center"),
                            (0, r"$2^{-240}$", "right" if mobile else "center")]:
        x = x_of(bit) + 0.5
        ax.plot([x, x], [0, -0.18], color=fs.MUTED, lw=0.8)
        ax.text(x, -0.3, f"bit {bit}\n{value}", fontsize=11.5, ha=ha, va="top", linespacing=1.4)
    fig.text(0.035, 0.32 if mobile else 0.24,
             "Largest product reaches bit 480.\nBits above it absorb carries." if mobile else
             "Largest product: $2^{240}$, at bit 480.  The 30 bits above it absorb carries.",
             fontsize=12, linespacing=1.5)
    fig.text(0.035, 0.21 if mobile else 0.15,
             "Blue: 241 integer positions\nLight blue: 240 fractional positions" if mobile else
             "Blue: 241 integer positions.  Light blue: 240 fractional positions.",
             fontsize=11.5, linespacing=1.5, color=fs.MUTED)
    fig.text(0.035, 0.025,
             "From zero, strictly fewer than $2^{31}$\nfinite products accumulate exactly."
             if mobile else "From zero, strictly fewer than $2^{31}$ finite products accumulate exactly.",
             fontsize=12, linespacing=1.5,
             bbox=dict(facecolor=fs.PAPER_2, edgecolor=fs.LINE, boxstyle="square,pad=0.45"))
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    fs.setup()
    out = args.out or fs.ASSETS / "ch14-quire.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
