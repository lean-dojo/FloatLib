#!/usr/bin/env python3
"""Draw content/assets/ch16-spacing.png: the representable values of five systems on one line.

Chapter 12 covers fixed point, logarithmic numbers, codebooks and shared-scale blocks, and
contrasts them with floating point. This figure marks the representable values between -8 and 8,
truncating the logarithmic exponents to -4 through 3 as labelled. One strip per system makes
the spacing rules visible side by side: uniform
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
import matplotlib.pyplot as plt  # noqa: E402

LIMIT = 8

# Fixed point: binaryRadix, 2 fractional digits.
FIXED_RADIX, FIXED_DIGITS = 2, 2

# FloatFormat.e2m3 = .finite 2 3.
E2M3_EXP_WIDTH, E2M3_FRAC_WIDTH = 2, 3
E2M3_BIAS = 2 ** (E2M3_EXP_WIDTH - 1) - 1

LOG_RADIX = 2
LOG_EXPONENTS = range(-4, 4)

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
    ("Fixed point: step 1/4", fs.BLUE, fixed_point()),
    ("Floating point: E2M3", fs.ORANGE, e2m3()),
    ("Logarithmic: zero and ±2ᵉ", fs.GREEN, logarithmic()),
    ("Shared scale: step 1/4", fs.PURPLE, block(-2)),
    ("Shared scale: step 1", fs.PURPLE, block(0)),
    ("Shared scale: step 4", fs.PURPLE, block(2)),
    ("Ternary: −1, 0, 1", fs.VERMILION, within(Fraction(v) for v in TERNARY2.values())),
    ("Bipolar: −1, 1", fs.VERMILION, within(Fraction(v) for v in BIPOLAR1.values())),
]


def draw(mobile: bool):
    fig = plt.figure(figsize=(3.8, 8.6) if mobile else (9, 5.9))
    fig.text(0.035, 0.98, "Different rules for spacing", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.915 if mobile else 0.89, "Representable values from −8 to 8",
             fontsize=12, color=fs.MUTED)
    ax = fig.add_axes([0.07, 0.09, 0.88, 0.77] if mobile else [0.04, 0.10, 0.92, 0.72])
    for i, (label, colour, values) in enumerate(STRIPS):
        y = 7 - i
        ax.hlines(y, -LIMIT, LIMIT, color=fs.LINE, lw=0.8)
        ax.vlines([float(v) for v in values], y - 0.15, y + 0.15, color=colour, lw=1.1)
        if not mobile:
            if i == 2:
                label += " (e = −4 to 3 shown; continues toward 0)"
            elif i == 6:
                label += " (fourth code reserved)"
        ax.text(-LIMIT, y + 0.40, label, fontsize=12, va="bottom")
        if mobile and i == 2:
            ax.text(-LIMIT, y + 0.17, "e = −4 to 3 shown; continues toward 0", fontsize=11, va="bottom")
        elif mobile and i == 6:
            ax.text(-LIMIT, y + 0.17, "fourth code reserved", fontsize=11, va="bottom", color=fs.MUTED)
    ax.set(xlim=(-LIMIT - 0.2, LIMIT + 0.2), ylim=(-0.5, 7.95))
    ax.set_xticks([-8, -4, 0, 4, 8])
    ax.tick_params(axis="x", labelsize=11.5)
    ax.set_yticks([])
    ax.spines["left"].set_visible(False)
    ax.grid(False)
    ax.set_xlabel("value (same linear axis)", fontsize=11.5)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    assert max(e2m3()) == Fraction(15, 2)
    assert fixed_point() == block(-2)
    fs.setup()
    out = args.out or fs.ASSETS / "ch16-spacing.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
