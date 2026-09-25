#!/usr/bin/env python3
"""Draw content/assets/ch15-code-space.png: the code space of four P3109 descriptors.

Chapter 10 explains where a P3109 format keeps its zero, its subnormals, its one NaN and its
infinities: in a signed format the top bit splits the codes at 2^(K-1), codes below are positive,
codes above are the same magnitudes negated, the boundary itself is the NaN, positive infinity
(extended domain only) takes the code just below the NaN and negative infinity the top code; in
an unsigned format the NaN is the last code. This figure draws one complete strip for b8p4se,
with code 0 at the left and code 255 at the right. A key names every contiguous code class.
Three compact comparisons then show what changes in the finite, unsigned and precision-one
descriptors. The phone version stacks the key and comparisons without shrinking a wide strip.

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
from matplotlib.patches import Rectangle  # noqa: E402


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
    "+subnormal": fs.SKY, "+normal": fs.BLUE,
    "-subnormal": fs.YELLOW, "-normal": fs.ORANGE,
    "+inf": fs.GREEN, "-inf": fs.GREEN, "nan": fs.VERMILION, "zero": fs.PAPER_2,
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
    fig = plt.figure(figsize=(3.8, 8.9) if mobile else (9, 5.5))
    fig.text(0.035, 0.98, "Where P3109 keeps special values", fontsize=13.5, weight="bold", va="top")
    fig.text(0.035, 0.925 if mobile else 0.90,
             "b8p4se: 8 bits, precision 4\nSigned, with infinities" if mobile else
             "b8p4se: 8 bits, precision 4; signed, with infinities",
             fontsize=11.5, linespacing=1.4, va="top" if mobile else "baseline")
    ax = fig.add_axes([0.065, 0.78, 0.87, 0.075] if mobile else [0.06, 0.72, 0.88, 0.11])
    ax.set(xlim=(0, 256), ylim=(-0.25, 1.4))
    ax.axis("off")
    for lo, hi, cls in runs(FORMATS[0]):
        ax.add_patch(Rectangle((lo, 0.1), hi - lo + 1, 0.65,
                               facecolor=CLASS_COLOUR[cls], edgecolor="none"))
    # Boundaries denote encoded integers, not numerical order of the decoded values.
    for x, label in [(0.5, "0"), (128.5, "128"), (255.5, "255")]:
        ax.plot([x, x], [0, 0.1], color=fs.INK, lw=0.8)
        ax.text(x, -0.18, label, ha="center", va="top", fontsize=11.5)
    ax.text(64, 0.93, "positive", ha="center", fontsize=11.5, color=fs.BLUE)
    ax.text(195, 0.93, "negative", ha="center", fontsize=11.5, color=fs.INK)
    cells = [
        ("0", "zero", "zero"),
        ("1 to 7", "+subnormal", "positive subnormal"),
        ("8 to 126", "+normal", "positive normal"),
        ("127", "+inf", "+infinity"),
        ("128", "nan", "NaN"),
        ("129 to 135", "-subnormal", "negative subnormal"),
        ("136 to 254", "-normal", "negative normal"),
        ("255", "-inf", "−infinity"),
    ]
    legend = fig.add_axes([0.04, 0.425, 0.92, 0.30] if mobile else [0.06, 0.38, 0.88, 0.25])
    legend.axis("off")
    legend.set(xlim=(0, 1), ylim=(0, 1))
    for i, (codes, cls, label) in enumerate(cells):
        col, row = (0, i) if mobile else divmod(i, 4)
        x = col * 0.51
        y = 0.93 - row * (0.126 if mobile else 0.27)
        legend.add_patch(Rectangle((x, y - 0.025), 0.025, 0.045 if mobile else 0.07,
                                   facecolor=CLASS_COLOUR[cls], edgecolor=fs.LINE, lw=0.6))
        legend.text(x + 0.055, y, codes, fontsize=11.5, va="center")
        legend.text(x + (0.43 if mobile else 0.20), y, label, fontsize=11.5, va="center")
    fig.text(0.035, 0.377 if mobile else 0.295,
             "Change the descriptor, change the limits", fontsize=12, weight="bold")
    comparisons = [
        ("b8p4sf", "Signed, finite", "NaN: 128; no infinities", "Largest finite magnitude: 240"),
        ("b8p8uf", "Unsigned, finite", "NaN: 255; no infinities", "Grid c/128, from 0 to 127/64"),
        ("b6p1sf", "Signed, precision 1", "NaN: 32; no subnormals", "±2ᵉ, for e = −15 to 15"),
    ]
    for i, (name, kind, special, value) in enumerate(comparisons):
        x, y = (0.035, 0.325 - i * 0.12) if mobile else (0.035 + i * 0.325, 0.23)
        fig.text(x, y, name, fontsize=12, weight="bold")
        dy = 0.026 if mobile else 0.049
        fig.text(x, y - dy, kind, fontsize=11.5)
        fig.text(x, y - 2 * dy, special, fontsize=11)
        fig.text(x, y - 3 * dy, value, fontsize=11)
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
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
