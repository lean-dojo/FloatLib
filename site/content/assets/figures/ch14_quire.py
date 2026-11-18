#!/usr/bin/env python3
"""Draw content/assets/ch14-quire.png: the 512-bit quire of a 32-bit posit as a fixed-point word.

The chapter on posits gives the quire of an n-bit posit as a signed two's-complement word of 16n bits whose
least significant bit is worth 2^(16 - 8n), and works out the capacity argument in words: the
square of the largest posit is 2^240, and 2^31 such products come to exactly 2^511 coefficient
units, one past the largest ordinary quire coefficient. This figure draws the word to scale,
bit 511 on the left, with three value landmarks and the fields of the Posit Standard (2022),
Section 3.4: the sign bit, 31 carry-guard bits, 8n - 16 integer bits and 8n - 16 fraction bits.
The capacity bound for finite products is stated in the caption and derived in the chapter.

Everything drawn is arithmetic on the parameters of FloatLib/Floats/Formats/Posit/Quire/Model/
Core.lean (width = 16 * bits, scaleExponent = 16 - 8 * bits) and of
FloatLib/Floats/Formats/Posit/Descriptor.lean for the posit range, which the chapter states as
[2^-120, 2^120] for 32 bits: bit i of the quire has weight 2^(i + scaleExponent), so the least
significant bit is 2^-240 (the square of the smallest posit), bit 240 is one, bit 120 is the
smallest posit, bit 360 is the largest posit, bit 480 is the square of the largest posit and the
lowest carry-guard bit, bits 480 to 510 are the carry guard, and bit 511 is the sign.

Run from anywhere: python3 ch14_quire.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch, Rectangle  # noqa: E402

POSIT_BITS = 32
WIDTH = 16 * POSIT_BITS                 # Quire.width = 512
SCALE_EXPONENT = 16 - 8 * POSIT_BITS    # Quire.scaleExponent = -240
MAX_POSIT_EXPONENT = 4 * (POSIT_BITS - 2)   # regime of payloadBits ones: 4 * (n - 2) = 120

BIT_ONE = -SCALE_EXPONENT                          # weight 2^0
BIT_MIN_POSIT = BIT_ONE - MAX_POSIT_EXPONENT       # weight 2^-120
BIT_MAX_PRODUCT = BIT_ONE + 2 * MAX_POSIT_EXPONENT  # weight 2^240
BIT_SIGN = WIDTH - 1
BIT_CARRY = 2 * (8 * POSIT_BITS - 16)              # the carry guard starts above 8n - 16 + 8n - 16 bits
CARRY_BITS = BIT_SIGN - BIT_CARRY                  # 31 carry-guard bits, the standard's C30 to C0

assert BIT_MIN_POSIT * 2 == BIT_ONE == 240, (BIT_MIN_POSIT, BIT_ONE)
assert BIT_MAX_PRODUCT == BIT_CARRY == 480 and CARRY_BITS == 31


def x_of(bit: int) -> float:
    """Left edge of a bit; bit 511 is drawn at the left and bit 0 at the right."""
    return BIT_SIGN - bit


def draw(mobile: bool):
    """The 512-bit word as one bar: sign, carry guard, integer part, fraction part."""
    fig = plt.figure(figsize=(fs.MOBILE_WIDTH, 2.45) if mobile else (fs.WIDTH, 1.9))
    ax = fig.add_axes([0.05, 0.53, 0.90, 0.45] if mobile else [0.04, 0.40, 0.92, 0.57])
    ax.set(xlim=(-6, WIDTH + 6), ylim=(-1.15, 0.9))
    ax.axis("off")
    segments = [
        (BIT_SIGN, BIT_SIGN, fs.FIELD["sign"], f"sign (bit {BIT_SIGN})"),
        (BIT_CARRY, BIT_SIGN - 1, fs.ROLE["second"],
         f"carry guard (bits {BIT_CARRY} to {BIT_SIGN - 1})"),
        (BIT_ONE, BIT_CARRY - 1, fs.ROLE["main"],
         f"integer part (bits {BIT_ONE} to {BIT_CARRY - 1})"),
        (0, BIT_ONE - 1, fs.SKY, f"fraction part (bits 0 to {BIT_ONE - 1})"),
    ]
    handles = []
    for lo, hi, colour, label in segments:
        ax.add_patch(Rectangle((x_of(hi), 0), hi - lo + 1, 0.7,
                               facecolor=colour, edgecolor=fs.INK, lw=fs.LW_GRID))
        handles.append(Patch(facecolor=colour, edgecolor=fs.INK, linewidth=fs.LW_GRID,
                             label=label))
    for bit, value, ha in [(BIT_MAX_PRODUCT, r"$2^{240}$", "left" if mobile else "center"),
                            (BIT_ONE, "$1$", "center"),
                            (0, r"$2^{-240}$", "right" if mobile else "center")]:
        x = x_of(bit) + 0.5
        ax.plot([x, x], [0, -0.18], color=fs.INK, lw=fs.LW_AXIS)
        ax.text(x, -0.3, f"bit {bit}\n{value}", fontsize=fs.SIZE_TICK, ha=ha, va="top",
                linespacing=1.4)
    fs.legend(fig, handles=handles, loc="lower center", bbox_to_anchor=(0.5, 0.0),
              ncols=1 if mobile else 2, handlelength=1.4)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    fs.setup()
    out = args.out or fs.ASSETS / "ch14-quire.png"
    for mobile in (False, True):
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
