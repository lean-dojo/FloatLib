#!/usr/bin/env python3
"""Draw content/assets/ch15-code-space.png: the code space of four P3109 descriptors.

Chapter 10 explains where a P3109 format keeps its zero, its subnormals, its one NaN and its
infinities: in a signed format the top bit splits the codes at 2^(K-1), codes below are positive,
codes above are the same magnitudes negated, the boundary itself is the NaN, positive infinity
(extended domain only) takes the code just below the NaN and negative infinity the top code; in
an unsigned format the NaN is the last code. This figure draws one strip per descriptor, code 0
at the left and the last code at the right, with every class coloured and named and the landmark
codes and their values written in. To the left of each strip is the descriptor's bit layout to
scale: a sign bit (signed formats only), K - P exponent bits (K - P + 1 when unsigned) and P - 1
trailing bits.

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

    def describe(self) -> str:
        sign = "signed" if self.signed else "unsigned"
        domain = "extended" if self.extended else "finite"
        return f"{self.name}: {sign}, {domain}"


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
CLASS_NAME = {
    "+subnormal": "subnormal", "+normal": "positive normal",
    "-subnormal": "negative subnormal", "-normal": "negative normal",
    "+inf": "+inf", "-inf": "-inf", "nan": "NaN", "zero": "zero",
}
FIELD_COLOUR = {"s": fs.PAPER_2, "e": fs.PURPLE, "t": fs.SKY}

STRIP_X0, STRIP_X1 = 4.0, 13.5
BIT = 0.3
PITCH = 2.1
STRIP_H = 0.72


def power(value: Fraction) -> str:
    """Write a value as an integer, a fraction, or a power of two in mathtext."""
    num, den = value.numerator, value.denominator
    if den == 1:
        if num >= 256 and num & (num - 1) == 0:
            return rf"$2^{{{num.bit_length() - 1}}}$"
        return f"${num}$"
    if num == 1 and den & (den - 1) == 0:
        return rf"$2^{{-{den.bit_length() - 1}}}$"
    return rf"${num}/{den}$"


def runs(fmt: Format) -> list[tuple[int, int, str]]:
    out: list[tuple[int, int, str]] = []
    for code in range(fmt.modulus):
        cls = fmt.classify(code)
        if out and out[-1][2] == cls:
            out[-1] = (out[-1][0], code, cls)
        else:
            out.append((code, code, cls))
    return out


def draw_format(ax, fmt: Format, y: float, placements) -> None:
    ax.text(0, y + STRIP_H + 0.42, fmt.describe(), ha="left", va="bottom", fontsize=10,
            color=fs.INK)
    # Bit layout to scale.
    layout = ([("s", 1)] if fmt.signed else []) + [("e", fmt.exponent_bits), ("t", fmt.trailing_bits)]
    x = 0.0
    for letter, width in layout:
        for _ in range(width):
            ax.add_patch(Rectangle((x, y), BIT, STRIP_H, facecolor=FIELD_COLOUR[letter],
                                   edgecolor=fs.INK, linewidth=0.8))
            ax.text(x + BIT / 2, y + STRIP_H / 2, letter, ha="center", va="center", fontsize=9,
                    color=fs.INK)
            x += BIT
    split = ", ".join(f"{w} {name}" for (letter, w), name in zip(
        layout, (["sign"] if fmt.signed else []) + ["exponent", "trailing"]) if w)
    ax.text(0, y - 0.12, f"K = {fmt.k}, P = {fmt.p}: {split} bits", ha="left", va="top",
            fontsize=9, color=fs.MUTED)

    # Code strip to scale.
    def xc(code: float) -> float:
        return STRIP_X0 + (STRIP_X1 - STRIP_X0) * code / fmt.modulus

    for lo, hi, cls in runs(fmt):
        ax.add_patch(Rectangle((xc(lo), y), xc(hi + 1) - xc(lo), STRIP_H,
                               facecolor=CLASS_COLOUR[cls], edgecolor="none"))
        if cls in ("+normal", "-normal") or (cls == "+subnormal" and hi - lo > 40):
            # Wide classes are named inside the strip on two lines: the codes, then the values.
            offset = fmt.sign_boundary if cls == "-normal" else 0
            sign = "-" if cls == "-normal" else ""
            first = power(fmt.positive_finite(lo - offset))
            last = power(fmt.positive_finite(hi - offset))
            text = f"codes {lo} to {hi}: {CLASS_NAME[cls]}\n{sign}{first} to {sign}{last}"
            ax.text((xc(lo) + xc(hi + 1)) / 2, y + STRIP_H / 2, text, ha="center", va="center",
                    fontsize=9, linespacing=1.25, color="white" if cls == "+normal" else fs.INK)
    ax.add_patch(Rectangle((STRIP_X0, y), STRIP_X1 - STRIP_X0, STRIP_H, facecolor="none",
                           edgecolor=fs.INK, linewidth=0.8))

    # Narrow classes are named by leaders, above the strip for the positive half and zero,
    # below it for NaN and the negative half. The negative subnormals are the positive ones
    # negated, which the normal-row labels already show, so their label carries no values.
    for lo, hi, cls in runs(fmt):
        if cls in ("+normal", "-normal") or (cls == "+subnormal" and hi - lo > 40):
            continue
        dx, above, ha = placements[(fmt.name, cls)]
        if lo == hi:
            label = f"{lo}: {CLASS_NAME[cls]}"
        else:
            label = f"{lo} to {hi}: {CLASS_NAME[cls]}"
        if cls == "+subnormal":
            label += f", {power(fmt.positive_finite(lo))} to {power(fmt.positive_finite(hi))}"
        anchor_x = (xc(lo) + xc(hi + 1)) / 2
        anchor_y = y + STRIP_H if above else y
        text_y = y + STRIP_H + 0.4 if above else y - 0.42
        ax.annotate(label, (anchor_x, anchor_y), xytext=(anchor_x + dx, text_y),
                    textcoords="data", ha=ha, va="bottom" if above else "top", fontsize=9,
                    color=fs.INK,
                    arrowprops=dict(arrowstyle="-", color=fs.INK, lw=0.7, shrinkA=0, shrinkB=0))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    # For each leader label of a narrow class: horizontal offset of the text anchor from the
    # class (axis units), whether the label sits above the strip, and the text alignment at the
    # anchor, chosen so that no two labels overlap.
    placements = {
        ("b8p4se", "zero"): (0.0, True, "left"),
        ("b8p4se", "+subnormal"): (1.0, True, "left"),
        ("b8p4se", "+inf"): (0.1, True, "left"),
        ("b8p4se", "nan"): (-0.15, False, "right"),
        ("b8p4se", "-subnormal"): (0.3, False, "left"),
        ("b8p4se", "-inf"): (-0.05, False, "right"),
        ("b8p4sf", "zero"): (0.0, True, "left"),
        ("b8p4sf", "+subnormal"): (1.0, True, "left"),
        ("b8p4sf", "nan"): (-0.15, False, "right"),
        ("b8p4sf", "-subnormal"): (0.3, False, "left"),
        ("b8p8uf", "zero"): (0.0, True, "left"),
        ("b8p8uf", "nan"): (-0.05, False, "right"),
        ("b6p1sf", "zero"): (0.0, True, "left"),
        ("b6p1sf", "nan"): (-0.15, False, "right"),
    }
    height_units = PITCH * len(FORMATS) + 0.75
    xlim = (-0.1, 13.7)
    fig = fs.plt.figure(figsize=(fs.WIDTH, fs.WIDTH * height_units / (xlim[1] - xlim[0])))
    ax = fs.diagram_axes(fig, xlim, (-0.85, height_units - 0.85))
    ax.text(STRIP_X0, height_units - 1.0,
            "each strip is one descriptor's whole code space, code 0 at the left and the last code at the right",
            ha="left", va="bottom", fontsize=9.5, color=fs.MUTED)
    for row, fmt in enumerate(FORMATS):
        y = (len(FORMATS) - 1 - row) * PITCH
        draw_format(ax, fmt, y, placements)

    out = fs.save(fig, "ch15-code-space.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
