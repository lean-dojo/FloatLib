#!/usr/bin/env python3
"""Draw content/assets/ch16-spacing.png: the representable values of five systems on one line.

Chapter 12 covers fixed point, logarithmic numbers, codebooks and shared-scale blocks, and
contrasts them with floating point. This figure marks every representable value between -8 and 8
under each system, one strip per system, so the spacing rules are visible side by side: uniform
for fixed point, proportional to magnitude for a float, geometric for a logarithmic code, uniform
within a block and different from block to block for shared scales, and an arbitrary finite set
for a codebook.

Every value set is computed from the decoders in the Lean source, at small parameters:

* fixed point: FloatLib/Floats/Formats/FixedPoint/Exact/Runtime.lean, Code.toRat =
  coefficient / radix^fractionalDigits, at binaryRadix with 2 fractional digits, so m / 4;
* floating point: FloatFormat.e2m3 of FloatLib/Floats/Formats/BinaryInterchange/Format/
  Catalog.lean (`.finite 2 3`: 2 exponent bits, 3 fraction bits, bias 2^(2-1) - 1 = 1, every
  exponent code finite), decoded as t * 2^(1 - bias - 3) for a zero exponent field and
  (8 + t) * 2^(e - bias - 3) otherwise;
* logarithmic: FloatLib/Floats/Formats/Logarithmic/Exact/Runtime.lean, Code.toRat gives zero
  or +-radix^exponent, at binaryRadix; the exponent is an unbounded Int, so only exponents -4
  to 3 are drawn and the powers continue toward zero;
* shared-scale blocks: FloatLib/Floats/Formats/Block/SharedScale/Core.lean, lane i decodes to
  significands[i] * 2^exponent with an unbounded integer significand; one strip per shared
  exponent, -2, 0 and 2;
* codebooks: FloatLib/Floats/Formats/Codebook/Catalog/Runtime.lean, ternary2 (00 -> 0,
  01 -> +1, 10 -> -1, 11 reserved) and bipolar1 (0 -> -1, 1 -> +1).

Run from anywhere: python3 ch16_spacing.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

LIMIT = 8

# Fixed point: binaryRadix, 2 fractional digits.
FIXED_RADIX, FIXED_DIGITS = 2, 2

# FloatFormat.e2m3 = .finite 2 3.
E2M3_EXP_WIDTH, E2M3_FRAC_WIDTH = 2, 3
E2M3_BIAS = 2 ** (E2M3_EXP_WIDTH - 1) - 1

LOG_RADIX = 2
LOG_EXPONENTS = range(-4, 4)

BLOCK_EXPONENTS = (-2, 0, 2)

TERNARY2 = {0: 0, 1: 1, 2: -1}          # 3 is reserved
BIPOLAR1 = {0: -1, 1: 1}


def within(values):
    return sorted(v for v in values if -LIMIT <= v <= LIMIT)


def fixed_point():
    scale = FIXED_RADIX ** FIXED_DIGITS
    return within(Fraction(m, scale) for m in range(-LIMIT * scale, LIMIT * scale + 1))


def e2m3():
    values = {Fraction(0)}
    unit = 2 ** E2M3_FRAC_WIDTH
    for e in range(2 ** E2M3_EXP_WIDTH):
        for t in range(unit):
            if e == 0:
                v = t * Fraction(2) ** (1 - E2M3_BIAS - E2M3_FRAC_WIDTH)
            else:
                v = (unit + t) * Fraction(2) ** (e - E2M3_BIAS - E2M3_FRAC_WIDTH)
            values.add(v)
            values.add(-v)
    return within(values)


def logarithmic():
    values = {Fraction(0)}
    for e in LOG_EXPONENTS:
        v = Fraction(LOG_RADIX) ** e
        values.update((v, -v))
    return within(values)


def block(exponent: int):
    step = Fraction(2) ** exponent
    n = int(LIMIT / step)
    return within(s * step for s in range(-n, n + 1))


STRIPS = [
    ("fixed point, FixedPoint.Code binaryRadix 2: every m / 4", fs.BLUE, fixed_point()),
    ("floating point, FloatFormat.e2m3: 2 exponent bits, 3 fraction bits, bias 1", fs.ORANGE, e2m3()),
    (r"logarithmic, Logarithmic.Code binaryRadix: zero and $\pm 2^{e}$, exponents -4 to 3 drawn",
     fs.GREEN, logarithmic()),
    ("block scaled, Block.SharedScaleCode, shared exponent -2: every s / 4", fs.PURPLE, block(-2)),
    ("shared exponent 0: every integer s", fs.PURPLE, block(0)),
    ("shared exponent 2: every 4 s", fs.PURPLE, block(2)),
    ("codebook, Codebook.Catalog.ternary2: -1, 0, +1 (fourth word reserved)", fs.VERMILION,
     within(Fraction(v) for v in TERNARY2.values())),
    ("codebook, Codebook.Catalog.bipolar1: -1, +1", fs.VERMILION,
     within(Fraction(v) for v in BIPOLAR1.values())),
]
# Vertical position of each strip; the three block strips and the two codebook strips are
# grouped, with enough room between strips for a label that does not touch the ticks above it.
Y = [8.7, 7.5, 6.3, 5.05, 4.15, 3.25, 2.0, 1.1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    fig, ax = fs.figure(5.4)
    for (label, colour, values), y in zip(STRIPS, Y):
        ax.hlines(y, -LIMIT, LIMIT, color=fs.LINE, linewidth=0.8, zorder=1)
        ax.vlines([float(v) for v in values], y - 0.2, y + 0.2, color=colour, linewidth=1.1,
                  zorder=2)
        ax.text(-LIMIT, y + 0.27, label, ha="left", va="bottom", fontsize=9.5, color=fs.INK)
    ax.set_xlim(-LIMIT - 0.2, LIMIT + 0.2)
    ax.set_ylim(0.6, 9.4)
    ax.set_xticks(range(-LIMIT, LIMIT + 1))
    ax.set_yticks([])
    ax.spines["left"].set_visible(False)
    ax.grid(False)
    ax.set_xlabel("value")

    out = fs.save(fig, "ch16-spacing.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
