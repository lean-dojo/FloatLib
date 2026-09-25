#!/usr/bin/env python3
"""Draw content/assets/ch14-posit-layout.png: four 8-bit posit words with their fields marked.

Chapter 11 decodes the 8-bit words 0x6C, 0x01 and 0x7F by hand and with `decodeExact`. This
figure draws those three words and the encoding of one, 0x40, most significant bit on the left,
with the sign, the regime run, the terminating bit, the exponent bits and the fraction bits
coloured and named. The rows are ordered by value, so reading downwards the regime run lengthens
and the fraction shrinks toward both ends of the range, which is the taper the chapter describes.

Every number drawn is arithmetic on the format's parameters. The parameters come from
FloatLib/Floats/Formats/Posit/Descriptor.lean (payloadBits = bits - 1, exponentBits = 2,
regimeExponentStep = 4) and the decoder below follows the field definitions of
FloatLib/Floats/Formats/Posit/Model/Fields.lean (regimeRunLength, regimeValue,
usedExponentBits, fractionBits, scale, significand = 2^fractionBits + fractionField), which is
also how the chapter describes them. The values printed at the right of each row are computed by
that decoder, so they agree with the chapter's `#eval` results (0x6C = 128, 0x01 = 2^-24,
0x7F = 2^24).

Run from anywhere: python3 ch14_posit_layout.py [--out PNG]
Also writes a -mobile.png sibling with a shared field key and a full-width row for each word.
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

BITS = 8                       # the width the chapter decodes by hand
PAYLOAD_BITS = BITS - 1        # Format.payloadBits
EXPONENT_BITS = 2              # Format.exponentBits
REGIME_STEP = 4                # Format.regimeExponentStep = 2 ^ exponentBits
WORDS = (0x01, 0x40, 0x6C, 0x7F)

FIELD_COLOURS = {
    "sign": fs.PAPER_2,
    "regime": fs.BLUE,
    "terminator": fs.SKY,
    "exponent": fs.GREEN,
    "fraction": fs.ORANGE,
}
DIGIT_ON_DARK = {"regime", "exponent"}


@dataclass
class Decoded:
    word: int
    negative: bool
    regime_bit: int
    run: int
    regime_value: int
    has_terminator: bool
    used_exponent_bits: int
    exponent: int
    fraction_bits: int
    fraction: int
    significand: int
    scale: int

    @property
    def value(self) -> Fraction:
        return Fraction(self.significand) * (Fraction(2) ** self.scale)


def decode(word: int) -> Decoded:
    """The chapter's decoding of a finite posit word (zero and NaR are not drawn)."""
    negative = (word >> (BITS - 1)) & 1 == 1
    magnitude = (1 << BITS) - word if negative else word
    payload = magnitude & ((1 << PAYLOAD_BITS) - 1)
    regime_bit = (payload >> (PAYLOAD_BITS - 1)) & 1
    run = 0
    for index in range(PAYLOAD_BITS - 1, -1, -1):
        if (payload >> index) & 1 != regime_bit:
            break
        run += 1
    regime_value = run - 1 if regime_bit == 1 else -run
    has_terminator = run < PAYLOAD_BITS
    trailing = PAYLOAD_BITS - run - 1 if has_terminator else 0
    used = min(EXPONENT_BITS, trailing)
    fraction_bits = trailing - used
    fraction = payload & ((1 << fraction_bits) - 1)
    stored = (payload >> fraction_bits) & ((1 << used) - 1)
    exponent = stored << (EXPONENT_BITS - used)        # missing exponent bits count as zero
    scale = regime_value * REGIME_STEP + exponent - fraction_bits
    significand = (1 << fraction_bits) + fraction
    return Decoded(word, negative, regime_bit, run, regime_value, has_terminator, used,
                   exponent, fraction_bits, fraction, significand, scale)


def fields(d: Decoded) -> list[tuple[str, int]]:
    """(field name, width in bits), most significant first; widths sum to BITS."""
    out = [("sign", 1), ("regime", d.run)]
    if d.has_terminator:
        out.append(("terminator", 1))
    if d.used_exponent_bits:
        out.append(("exponent", d.used_exponent_bits))
    if d.fraction_bits:
        out.append(("fraction", d.fraction_bits))
    assert sum(w for _, w in out) == BITS, out
    return out


def value_label(d: Decoded) -> str:
    if d.significand == 1:
        return rf"$= 2^{{{d.scale}}}$"
    value = d.value
    shown = str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"
    return rf"$= {d.significand} \cdot 2^{{{d.scale}}} = {shown}$"


def field_note(name: str, d: Decoded) -> str:
    if name == "regime":
        kind = ("one" if d.run == 1 else "ones") if d.regime_bit else "zeros"
        return f"regime: {d.run} {kind}, k = {d.regime_value}"
    if name == "exponent":
        return f"exponent, e = {d.exponent}"
    if name == "fraction":
        return f"fraction, F = {d.fraction}"
    return name


def draw_row(ax, d: Decoded, y: float) -> None:
    bit_index = BITS - 1
    x = 0.0
    for name, width in fields(d):
        colour = FIELD_COLOURS[name]
        for _ in range(width):
            ax.add_patch(Rectangle((x, y), 1, 1, facecolor=colour, edgecolor=fs.INK, linewidth=0.9))
            digit = (d.word >> bit_index) & 1
            ax.text(x + 0.5, y + 0.5, str(digit), ha="center", va="center", fontsize=12,
                    color="white" if name in DIGIT_ON_DARK else fs.INK)
            x += 1
            bit_index -= 1
        start, end = x - width, x
        if name in ("sign", "terminator"):
            # The two one-bit fields are named above the row so that they never collide with
            # the field notes below it.
            ax.text((start + end) / 2, y + 1.1, name, ha="center", va="bottom", fontsize=9,
                    color=fs.INK)
        else:
            ax.plot([start + 0.08, start + 0.08, end - 0.08, end - 0.08],
                    [y - 0.1, y - 0.22, y - 0.22, y - 0.1], color=fs.INK, linewidth=0.8)
            ax.text((start + end) / 2, y - 0.3, field_note(name, d), ha="center", va="top",
                    fontsize=9, color=fs.INK)
    hexword = f"0x{d.word:02X}"
    ax.text(BITS + 0.8, y + 0.5, hexword, ha="left", va="center", fontsize=11,
            family="DejaVu Sans Mono", color=fs.INK)
    ax.text(BITS + 2.6, y + 0.5, value_label(d), ha="left", va="center", fontsize=11, color=fs.INK)


def build_mobile(rows):
    """Keep the original words, field colours and exact values on a narrow canvas."""
    assert [d.word for d in rows] == list(WORDS)
    assert [d.value for d in rows] == [Fraction(1, 2 ** 24), Fraction(1),
                                      Fraction(128), Fraction(2 ** 24)]
    assert [(d.run, d.regime_value, d.used_exponent_bits, d.exponent, d.fraction_bits,
             d.significand, d.scale) for d in rows] == [
        (6, -6, 0, 0, 0, 1, -24), (1, 0, 2, 0, 3, 8, -3),
        (2, 1, 2, 3, 2, 4, 5), (7, 6, 0, 0, 0, 1, 24)]
    assert all(not d.negative and d.fraction == 0 for d in rows)
    assert [d.has_terminator for d in rows] == [True, True, True, False]

    height = 8.6
    fig = fs.plt.figure(figsize=(3.8, height))
    ax = fs.diagram_axes(fig, (0, 3.8), (0, height))
    ax.text(0.18, 8.37, "Reading four posit8 words", fontsize=15, weight="bold", va="top")
    ax.text(0.18, 7.96, "Most significant bit at left", fontsize=12, va="center")
    key = (("sign", 0.18, 7.56), ("regime", 0.18, 7.24), ("terminator", 0.18, 6.92),
           ("exponent", 2.04, 7.56), ("fraction", 2.04, 7.24))
    for name, x, y in key:
        ax.add_patch(Rectangle((x, y - 0.08), 0.17, 0.17, facecolor=FIELD_COLOURS[name],
                               edgecolor=fs.INK, linewidth=0.6))
        ax.text(x + 0.25, y, name.capitalize(), fontsize=12, va="center")

    for row, d in enumerate(rows):
        y = 6.37 - row * 1.61
        ax.text(0.18, y, f"0x{d.word:02X}", fontsize=13, family="DejaVu Sans Mono",
                va="center", weight="bold")
        ax.text(3.62, y, value_label(d), fontsize=15, ha="right", va="center")
        bit_y = y - 0.64
        bit_index = BITS - 1
        x = 0.18
        cell = 3.44 / BITS
        for name, width in fields(d):
            for _ in range(width):
                ax.add_patch(Rectangle((x, bit_y), cell, 0.42, facecolor=FIELD_COLOURS[name],
                                       edgecolor=fs.INK, linewidth=0.8))
                ax.text(x + cell / 2, bit_y + 0.21, str((d.word >> bit_index) & 1),
                        fontsize=13, ha="center", va="center",
                        color="white" if name in DIGIT_ON_DARK else fs.INK)
                x += cell
                bit_index -= 1
        assert bit_index == -1
        ax.text(0.18, y - 0.89, field_note("regime", d).capitalize().replace(", ", " · "),
                fontsize=12, va="center")
        if d.fraction_bits:
            note = f"e = {d.exponent} · F = {d.fraction} · {d.fraction_bits} fraction bits"
        elif d.has_terminator:
            note = "No exponent or fraction bits"
        else:
            note = "No terminator or trailing fields"
        ax.text(0.18, y - 1.18, note, fontsize=12, va="center")
        if row < len(rows) - 1:
            ax.plot([0.18, 3.62], [y - 1.41, y - 1.41], color=fs.LINE, linewidth=0.8)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    pitch = 2.05
    rows = [decode(w) for w in WORDS]
    rows.sort(key=lambda d: d.value)
    height_units = pitch * len(rows) + 0.9
    xlim = (-0.3, 13.4)
    fig = fs.plt.figure(figsize=(fs.WIDTH, fs.WIDTH * height_units / (xlim[1] - xlim[0])))
    ax = fs.diagram_axes(fig, xlim, (-0.75, height_units - 0.75))

    ax.text(0, height_units - 0.6,
            r"8-bit posit words, most significant bit on the left; value $= (2^{f} + F) \cdot 2^{4k + e - f}$",
            ha="left", va="center", fontsize=10.5, color=fs.INK)
    for row, d in enumerate(reversed(rows)):
        draw_row(ax, d, row * pitch)

    out = fs.save(fig, "ch14-posit-layout.png", args.out)
    print(f"wrote {out}")
    mobile = out.with_name(f"{out.stem}-mobile{out.suffix}")
    print(f"wrote {fs.save(build_mobile(rows), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
