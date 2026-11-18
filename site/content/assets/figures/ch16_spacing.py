#!/usr/bin/env python3
"""Draw content/assets/ch16-spacing.png: the representable values of five systems on one line.

The chapter on fixed point and other formats covers fixed point, logarithmic numbers, codebooks and shared-scale blocks, and
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
* shared-scale blocks: FloatLib/Floats/Formats/Block/Configured.lean (`sharedScale`), lane i
  decodes to element[i] * 2^exponent with an unbounded integer element; one strip per shared
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


# (family, parameter, values): the label of a row is "family, parameter".
STRIPS = [
    ("fixed point", "step 1/4", fixed_point()),
    ("floating point", "E2M3", e2m3()),
    ("logarithmic", "exponents −4 to 3", logarithmic()),
    ("shared scale", "step 1/4", block(-2)),
    ("shared scale", "step 1", block(0)),
    ("shared scale", "step 4", block(2)),
    ("ternary", "", within(Fraction(v) for v in TERNARY2.values())),
    ("bipolar", "", within(Fraction(v) for v in BIPOLAR1.values())),
]


def draw(mobile: bool):
    """One row of marks per format on a shared linear value axis."""
    fig, ax = plt.subplots(figsize=(fs.MOBILE_WIDTH, 5.4) if mobile else (fs.WIDTH, 4.0))
    fig.subplots_adjust(left=0.42 if mobile else 0.27, right=0.96, top=0.98,
                        bottom=0.13 if mobile else 0.15)
    rows = len(STRIPS)
    labels = []
    for i, (family, parameter, values) in enumerate(STRIPS):
        y = rows - 1 - i
        ax.hlines(y, -LIMIT, LIMIT, color=fs.LINE, lw=fs.LW_AXIS)
        ax.vlines([float(v) for v in values], y - 0.22, y + 0.22, color=fs.ROLE["main"],
                  lw=fs.LW_REF)
        joiner = "\n" if mobile else ", "
        labels.append(family + (joiner + parameter if parameter else ""))
    ax.set(xlim=(-LIMIT - 0.2, LIMIT + 0.2), ylim=(-0.6, rows - 0.4))
    ax.set_xticks([-8, -4, 0, 4, 8], labels=["−8", "−4", "0", "4", "8"])
    ax.set_yticks(range(rows - 1, -1, -1), labels=labels)
    ax.tick_params(axis="y", length=0)
    ax.spines["left"].set_visible(False)
    ax.grid(False)
    ax.set_xlabel("value")
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
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
