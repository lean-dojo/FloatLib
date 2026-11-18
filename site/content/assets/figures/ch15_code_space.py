#!/usr/bin/env python3
"""Draw content/assets/ch15-code-space.png: the code space of four P3109 descriptors.

The chapter on machine-learning formats explains where a P3109 format keeps its zero, its subnormals, its one NaN and its
infinities: in a signed format the top bit splits the codes at 2^(K-1), codes below are positive,
codes above are the same magnitudes negated, the boundary itself is the NaN, positive infinity
(extended domain only) takes the code just below the NaN and negative infinity the top code; in
an unsigned format the NaN is the last code. This figure draws one complete strip per
descriptor, code 0 at the left, each scaled to its own number of codes, with ticks at code 0,
at the NaN and at the last code. One legend names the classes of all four strips, so the finite,
unsigned and precision-one descriptors can be compared with b8p4se class by class.

The four descriptors are the ones the chapter defines: b8p4se, b8p4sf, b8p8uf and b6p1sf. Every
number is arithmetic on their parameters following FloatLib/Floats/Formats/P3109/Runtime.lean:
exponentBits, exponentBias = 2^(exponentBits - 1), signBoundary = 2^(K-1), nanBits,
positiveInfinityBits, negativeInfinityBits, and decodePositiveFinite (t * 2^(2 - P - B) for a
zero exponent field, (2^(P-1) + t) * 2^(e - B + 1 - P) otherwise). The values printed agree with
the chapter's `#eval` results (code 1 of b8p4se is 2^-10, code 8 is 2^-7, code 126 is 224, code
127 of b8p4sf is 240, b8p8uf is the grid c/128 up to 127/64).

Run from anywhere: python3 ch15_code_space.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch, Rectangle  # noqa: E402


@dataclass(frozen=True)
class Format:
    name: str
    k: int
    p: int
    signed: bool
    extended: bool

    @property
    def exponent_bits(self) -> int:
        return self.k - self.p if self.signed else self.k - self.p + 1

    @property
    def bias(self) -> int:
        return 2 ** (self.exponent_bits - 1)

    @property
    def trailing_bits(self) -> int:
        return self.p - 1

    @property
    def modulus(self) -> int:
        return 2 ** self.k

    @property
    def sign_boundary(self) -> int:
        return 2 ** (self.k - 1)

    @property
    def nan(self) -> int:
        return self.sign_boundary if self.signed else self.modulus - 1

    @property
    def positive_infinity(self) -> int | None:
        if not self.extended:
            return None
        return self.sign_boundary - 1 if self.signed else self.modulus - 2

    @property
    def negative_infinity(self) -> int | None:
        return self.modulus - 1 if (self.signed and self.extended) else None

    def positive_finite(self, bits: int) -> Fraction:
        """decodePositiveFinite on an in-range magnitude code."""
        if bits == 0:
            return Fraction(0)
        unit = 2 ** self.trailing_bits
        t, e = bits % unit, bits // unit
        if e == 0:
            return t * Fraction(2) ** (2 - self.p - self.bias)
        return (unit + t) * Fraction(2) ** (e - self.bias + 1 - self.p)

    def classify(self, code: int) -> str:
        if code == self.nan:
            return "nan"
        if code == self.positive_infinity:
            return "+inf"
        if code == self.negative_infinity:
            return "-inf"
        negative = self.signed and code > self.sign_boundary
        magnitude = code - self.sign_boundary if negative else code
        if magnitude == 0:
            return "zero"
        kind = "subnormal" if magnitude // 2 ** self.trailing_bits == 0 else "normal"
        return ("-" if negative else "+") + kind

FORMATS = (
    Format("b8p4se", 8, 4, True, True),
    Format("b8p4sf", 8, 4, True, False),
    Format("b8p8uf", 8, 8, False, False),
    Format("b6p1sf", 6, 1, True, False),
)

CLASS_COLOUR = {
    "zero": "white", "+subnormal": fs.SKY, "+normal": fs.BLUE, "+inf": fs.GREEN,
    "nan": fs.VERMILION, "-subnormal": fs.YELLOW, "-normal": fs.ORANGE, "-inf": fs.GREEN,
}
CLASS_LABEL = {
    "zero": "zero", "+subnormal": "positive subnormal", "+normal": "positive normal",
    "+inf": "+∞ and −∞", "nan": "NaN", "-subnormal": "negative subnormal",
    "-normal": "negative normal",
}


def runs(fmt: Format) -> list[tuple[int, int, str]]:
    out: list[tuple[int, int, str]] = []
    for code in range(fmt.modulus):
        cls = fmt.classify(code)
        if out and out[-1][2] == cls:
            out[-1] = (out[-1][0], code, cls)
        else:
            out.append((code, code, cls))
    return out


def draw(mobile: bool):
    """One strip per format: every code, in code order, coloured by the class it decodes to."""
    width = fs.MOBILE_WIDTH if mobile else fs.WIDTH
    pitch = 0.95
    legend_height = 1.5 if mobile else 0.75
    height = pitch * len(FORMATS) + legend_height + 0.1
    fig = plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    left = 0.2 if mobile else 1.15
    span = width - left - 0.25
    for row, fmt in enumerate(FORMATS):
        y = height - 0.5 - row * pitch - (0.3 if mobile else 0.0)
        if mobile:
            ax.text(left, y + 0.42, fmt.name, fontsize=fs.SIZE_LABEL, va="bottom")
        else:
            ax.text(left - 0.15, y + 0.16, fmt.name, fontsize=fs.SIZE_LABEL, ha="right",
                    va="center")
        unit = span / fmt.modulus
        for lo, hi, cls in runs(fmt):
            ax.add_patch(Rectangle((left + lo * unit, y), (hi - lo + 1) * unit, 0.32,
                                   facecolor=CLASS_COLOUR[cls], edgecolor="none"))
        ax.add_patch(Rectangle((left, y), span, 0.32, facecolor="none", edgecolor=fs.INK,
                               lw=fs.LW_AXIS))
        # Ticks name encoded integers; code order is not the numerical order of the values.
        ticks = sorted({0, fmt.nan, fmt.modulus - 1})
        for code in ticks:
            x = left + (code + 0.5) * unit
            ax.plot([x, x], [y - 0.07, y], color=fs.INK, lw=fs.LW_AXIS)
            ax.text(x, y - 0.11, str(code), ha="center", va="top", fontsize=fs.SIZE_SMALL)
    handles = [Patch(facecolor=CLASS_COLOUR[cls], edgecolor=fs.INK, linewidth=fs.LW_GRID,
                     label=label) for cls, label in CLASS_LABEL.items()]
    fs.legend(ax, handles=handles, loc="lower center", bbox_to_anchor=(width / 2, 0.05),
              bbox_transform=ax.transData, ncols=2 if mobile else 4, handlelength=1.4,
              columnspacing=1.2)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    se, sf, uf, p1 = FORMATS
    assert se.positive_finite(1) == Fraction(1, 1024)
    assert se.positive_finite(8) == Fraction(1, 128)
    assert se.positive_finite(126) == 224 and sf.positive_finite(127) == 240
    assert all(uf.positive_finite(c) == Fraction(c, 128) for c in range(255))
    assert not any("subnormal" in p1.classify(c) for c in range(p1.modulus))
    assert p1.positive_finite(1) == Fraction(2) ** -15 and p1.positive_finite(31) == 2 ** 15
    fs.setup()
    out = args.out or fs.ASSETS / "ch15-code-space.png"
    for mobile in (False, True):
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
