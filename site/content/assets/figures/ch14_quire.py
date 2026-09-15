#!/usr/bin/env python3
"""Draw content/assets/ch14-quire.png: the 512-bit quire of a 32-bit posit as a fixed-point word.

Chapter 11 gives the quire of an n-bit posit as a signed two's-complement word of 16n bits whose
least significant bit is worth 2^(16 - 8n), and works out the capacity argument in words: the
square of the largest posit is 2^240, and 2^31 such products come to exactly 2^511 coefficient
units, one past the largest ordinary quire coefficient. This figure draws the word to scale, bit
511 on the left, with the weight of each landmark bit written under it and the spans that one
posit, one product of two posits, and the headroom for a long sum occupy.

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
from matplotlib.patches import Rectangle  # noqa: E402

POSIT_BITS = 32
WIDTH = 16 * POSIT_BITS                 # Quire.width = 512
SCALE_EXPONENT = 16 - 8 * POSIT_BITS    # Quire.scaleExponent = -240
MAX_POSIT_EXPONENT = 4 * (POSIT_BITS - 2)   # regime of payloadBits ones: 4 * (n - 2) = 120

BIT_ONE = -SCALE_EXPONENT                          # weight 2^0
BIT_MIN_POSIT = BIT_ONE - MAX_POSIT_EXPONENT       # weight 2^-120
BIT_MAX_POSIT = BIT_ONE + MAX_POSIT_EXPONENT       # weight 2^120
BIT_MAX_PRODUCT = BIT_ONE + 2 * MAX_POSIT_EXPONENT  # weight 2^240
BIT_SIGN = WIDTH - 1
HEADROOM = BIT_SIGN - BIT_MAX_PRODUCT - 1          # 30 bits strictly between them

assert BIT_MIN_POSIT * 2 == BIT_ONE == 240, (BIT_MIN_POSIT, BIT_ONE)
assert BIT_MAX_PRODUCT == 480 and HEADROOM == 30


def x_of(bit: int) -> float:
    """Left edge of a bit; bit 511 is drawn at the left and bit 0 at the right."""
    return BIT_SIGN - bit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    fig, ax = fs.figure(3.7)
    ax.set_xlim(-6, WIDTH + 6)
    ax.set_ylim(-3.4, 4.1)
    ax.axis("off")
    ax.grid(False)

    y0, h = 0.0, 1.0
    segments = [
        (BIT_SIGN, BIT_SIGN, fs.VERMILION, ""),
        (BIT_MAX_PRODUCT + 1, BIT_SIGN - 1, fs.GREEN, f"{HEADROOM} bits"),
        (BIT_ONE, BIT_MAX_PRODUCT, fs.BLUE, f"{BIT_MAX_PRODUCT - BIT_ONE + 1} integer bits, weights 1 to $2^{{240}}$"),
        (0, BIT_ONE - 1, fs.SKY, f"{BIT_ONE} fraction bits, weights $2^{{-240}}$ to $2^{{-1}}$"),
    ]
    for lo, hi, colour, label in segments:
        ax.add_patch(Rectangle((x_of(hi), y0), hi - lo + 1, h, facecolor=colour,
                               edgecolor=fs.INK, linewidth=0.9))
        if label and hi - lo > 60:
            ax.text((x_of(hi) + x_of(lo) + 1) / 2, y0 + h / 2, label, ha="center", va="center",
                    fontsize=9.5, color="white" if colour == fs.BLUE else fs.INK)
    # The two narrow segments are named by leaders that rise vertically from them, the sign
    # label on the upper line and the headroom label on the lower one, so neither crosses the
    # other or the spans drawn higher up.
    sign_x = x_of(BIT_SIGN) + 0.5
    ax.plot([sign_x, sign_x], [y0 + h, 1.95], color=fs.INK, linewidth=0.8)
    ax.text(sign_x + 3, 1.95, f"sign, bit {BIT_SIGN}", ha="left", va="center", fontsize=9.5,
            color=fs.INK)
    head_x = (x_of(BIT_SIGN - 1) + x_of(BIT_MAX_PRODUCT + 1) + 1) / 2
    ax.plot([head_x, head_x], [y0 + h, 1.38], color=fs.INK, linewidth=0.8)
    ax.text(head_x + 3, 1.38,
            f"{HEADROOM} bits of headroom, bits {BIT_MAX_PRODUCT + 1} to {BIT_SIGN - 1}",
            ha="left", va="center", fontsize=9.5, color=fs.INK)

    # Binary point between bit 240 and bit 239.
    ax.plot([x_of(BIT_ONE - 1), x_of(BIT_ONE - 1)], [y0 - 0.15, y0 + h + 0.15], color=fs.INK,
            linewidth=1.6)
    ax.text(x_of(BIT_ONE - 1), y0 + h + 0.22, "binary point", ha="center", va="bottom",
            fontsize=9.5, color=fs.INK)

    # Landmark bits and their weights.
    landmarks = [
        (0, r"bit 0" "\n" r"$2^{-240}$" "\n" "smallest posit squared"),
        (BIT_MIN_POSIT, r"bit 120" "\n" r"$2^{-120}$" "\n" "smallest posit"),
        (BIT_ONE, r"bit 240" "\n" r"$2^{0} = 1$"),
        (BIT_MAX_POSIT, r"bit 360" "\n" r"$2^{120}$" "\n" "largest posit"),
        (BIT_MAX_PRODUCT, r"bit 480" "\n" r"$2^{240}$" "\n" "largest posit squared"),
    ]
    for bit, label in landmarks:
        xc = x_of(bit) + 0.5
        ax.plot([xc, xc], [y0 - 0.05, y0 - 0.35], color=fs.INK, linewidth=0.9)
        ax.text(xc, y0 - 0.45, label, ha="center", va="top", fontsize=9, color=fs.INK,
                linespacing=1.25)

    # Spans above the word.
    def span(lo_bit: int, hi_bit: int, y: float, text: str) -> None:
        left, right = x_of(hi_bit), x_of(lo_bit) + 1
        ax.plot([left, left, right, right], [y - 0.12, y, y, y - 0.12], color=fs.INK,
                linewidth=0.9)
        ax.text((left + right) / 2, y + 0.08, text, ha="center", va="bottom", fontsize=9.5,
                color=fs.INK)

    span(BIT_MIN_POSIT, BIT_MAX_POSIT, 3.4, r"one posit: $2^{-120}$ to $2^{120}$")
    span(0, BIT_MAX_PRODUCT, 2.5, r"one product of two posits: $2^{-240}$ to $2^{240}$")

    ax.text(WIDTH / 2, -3.3,
            r"$2^{31}$ products of the largest posit sum to $2^{31} \cdot 2^{480} = 2^{511}$ units and reach the sign bit, "
            "so the term limit is fewer than $2^{31}$",
            ha="center", va="bottom", fontsize=9.5, color=fs.INK)

    out = fs.save(fig, "ch14-quire.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
