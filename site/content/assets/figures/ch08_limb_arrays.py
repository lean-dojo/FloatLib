#!/usr/bin/env python3
"""Draw content/assets/ch08-limb-arrays.png: a number split into 32-bit limbs, and a carry.

Chapter 13 introduces `FloatLib.Numerics.LimbArray` (FloatLib/Kernels/LimbArray/Core/Runtime.lean):
a natural number stored as a little-endian `Array UInt32`, limb i carrying weight 2^(32 i), with
limbs beyond the stored ones read as zero. Its Lean block prints two results this figure draws:

    #eval LimbArray.ofNat (2 ^ 70 + 5) 3
    -- { limbs := #[5, 0, 64] }
    #eval LimbArray.add (LimbArray.ofNat (2 ^ 96 - 1) 3) (LimbArray.ofNat 1 1)
    -- { limbs := #[0, 0, 0, 1] }

The upper panel is the first result: 2^70 + 5 in three limbs, drawn most significant first, with
each limb's bit positions, value and weight, and the array as Lean prints it. The lower panel is
the second: `add` from FloatLib/Kernels/LimbArray/Arithmetic/Runtime.lean runs `addLoop`, which
at each limb forms `a_i + b_i + carry` in a UInt64, stores the low 32 bits, and passes the high
bits on as the next carry; the sum is placed in one limb more than the wider operand and the final
carry is stored there. Here every limb of 2^96 - 1 is 0xFFFFFFFF, so adding 1 carries through all
three limbs into the reserved fourth.

This script transcribes `ofNat` and `addLoop` into Python over integers, replays both examples,
and stops with an error if either result differs from the array the chapter prints. Every drawn
number (limb values, per-limb UInt64 sums, carries, bit indices) comes from that replay.

Run from anywhere: python3 ch08_limb_arrays.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

RADIX = 2 ** 32
MASK = RADIX - 1


def of_nat(n: int, count: int) -> list[int]:
    """`LimbArray.ofNat n count`: the count low base-2^32 digits of n, little-endian."""
    limbs = []
    for _ in range(count):
        limbs.append(n & MASK)
        n >>= 32
    return limbs


def limb(v: list[int], i: int) -> int:
    """`LimbArray.limb`: zero beyond the stored limbs."""
    return v[i] if i < len(v) else 0


def add_loop(a: list[int], b: list[int]) -> tuple[list[int], list[dict]]:
    """`LimbArray.add a b` with its per-limb UInt64 sums and carries recorded."""
    count = max(len(a), len(b))
    out = [0] * (count + 1)
    carry = 0
    steps = []
    for index in range(count):
        total = limb(a, index) + limb(b, index) + carry  # fits a UInt64
        assert total < 2 ** 64
        out[index] = total & MASK
        steps.append(dict(index=index, a=limb(a, index), b=limb(b, index), carry_in=carry,
                          total=total, stored=total & MASK, carry_out=total >> 32))
        carry = total >> 32
    out[count] = carry  # the base case of addLoop stores the final carry
    return out, steps


def to_nat(v: list[int]) -> int:
    return sum(x * RADIX ** i for i, x in enumerate(v))


# The chapter's two examples and the arrays its `#eval`s print.
SPLIT_VALUE, SPLIT_COUNT, SPLIT_EXPECTED = 2 ** 70 + 5, 3, [5, 0, 64]
ADD_LEFT, ADD_RIGHT, ADD_EXPECTED = (2 ** 96 - 1, 3), (1, 1), [0, 0, 0, 1]

SUPERSCRIPTS = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")


def pow2(n: int) -> str:
    return "2" + str(n).translate(SUPERSCRIPTS)


def lean_array(v: list[int]) -> str:
    return "#[" + ", ".join(str(x) for x in v) + "]"


def hex32(x: int) -> str:
    return f"{x:08X}"


# Layout in axis units; the figure is 9 inches wide.
LIMB_W = 3.55
LIMB_H = 0.95
X_LABEL = 0.2
X_LIMBS = 3.35
WIDTH_UNITS = X_LIMBS + 4 * LIMB_W + 0.3
MONO = "DejaVu Sans Mono"


def limb_x(position: int, total: int) -> float:
    """Left edge of limb `position` when `total` limbs are drawn, most significant leftmost."""
    return X_LIMBS + (total - 1 - position) * LIMB_W


def limb_box(ax, x: float, y: float, value: int, *, facecolor=fs.PAPER_2, stored: bool = True):
    if stored:
        ax.add_patch(Rectangle((x, y), LIMB_W, LIMB_H, facecolor=facecolor, edgecolor=fs.INK,
                               lw=0.9, alpha=0.9))
        ax.text(x + LIMB_W / 2, y + LIMB_H * 0.62, str(value), ha="center", va="center",
                fontsize=9.5, color=fs.INK, family=MONO)
        ax.text(x + LIMB_W / 2, y + LIMB_H * 0.26, "0x" + hex32(value), ha="center", va="center",
                fontsize=8.5, color=fs.MUTED, family=MONO)
    else:
        ax.add_patch(Rectangle((x, y), LIMB_W, LIMB_H, facecolor="white", edgecolor=fs.MUTED,
                               lw=0.9, ls=(0, (3, 3))))
        ax.text(x + LIMB_W / 2, y + LIMB_H * 0.62, "0", ha="center", va="center", fontsize=9.5,
                color=fs.MUTED, family=MONO)
        ax.text(x + LIMB_W / 2, y + LIMB_H * 0.26, "not stored, reads as 0", ha="center",
                va="center", fontsize=8.5, color=fs.MUTED)


def row_label(ax, y: float, text: str) -> None:
    ax.text(X_LABEL, y + LIMB_H / 2, text, ha="left", va="center", fontsize=9.5, color=fs.INK,
            linespacing=1.3)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    split = of_nat(SPLIT_VALUE, SPLIT_COUNT)
    if split != SPLIT_EXPECTED:
        raise SystemExit(f"ofNat gave {split}, chapter prints {SPLIT_EXPECTED}")
    assert to_nat(split) == SPLIT_VALUE
    a = of_nat(*ADD_LEFT)
    b = of_nat(*ADD_RIGHT)
    total, steps = add_loop(a, b)
    if total != ADD_EXPECTED:
        raise SystemExit(f"add gave {total}, chapter prints {ADD_EXPECTED}")
    assert to_nat(total) == ADD_LEFT[0] + ADD_RIGHT[0]
    n_out = len(total)

    # Vertical plan, measured downwards from the top edge at 0; the height follows from it.
    y_title = -0.15
    y_split = y_title - 1.25 - LIMB_H          # bit positions above, so leave room
    y_tonat = y_split - 0.75
    y_rule = y_tonat - 0.75
    y_title2 = y_rule - 0.35
    y_a = y_title2 - 0.95 - LIMB_H
    y_b = y_a - 0.25 - LIMB_H
    y_sum = y_b - 0.2 - 1.1
    y_arrow = y_sum - 0.25
    y_out = y_arrow - 0.45 - LIMB_H
    y_bottom = y_out - 0.85
    height_units = -y_bottom

    fs.setup()
    fig = plt.figure(figsize=(fs.WIDTH, height_units * fs.WIDTH / WIDTH_UNITS))
    ax = fs.diagram_axes(fig, (0, WIDTH_UNITS), (y_bottom, 0))

    # Upper panel: the split of 2^70 + 5 into three limbs.
    ax.text(X_LABEL, y_title, f"A natural number as little-endian 32-bit limbs: "
            f"LimbArray.ofNat ({pow2(70)} + 5) 3", ha="left", va="top", fontsize=10.5,
            color=fs.INK)
    row_label(ax, y_split, "limb value,\ndecimal and hex")
    for position, value in enumerate(split):
        x = limb_x(position, SPLIT_COUNT)
        limb_box(ax, x, y_split, value, facecolor=fs.SKY)
        hi, lo = 32 * position + 31, 32 * position
        ax.text(x + LIMB_W / 2, y_split + LIMB_H + 0.42, f"limb {position}", ha="center",
                va="bottom", fontsize=9.5, color=fs.INK)
        ax.text(x + 0.08, y_split + LIMB_H + 0.06, str(hi), ha="left", va="bottom", fontsize=8,
                color=fs.MUTED)
        ax.text(x + LIMB_W - 0.08, y_split + LIMB_H + 0.06, str(lo), ha="right", va="bottom",
                fontsize=8, color=fs.MUTED)
        ax.text(x + LIMB_W / 2, y_split + LIMB_H + 0.06, f"bits {hi} to {lo}", ha="center",
                va="bottom", fontsize=8, color=fs.MUTED)
        ax.text(x + LIMB_W / 2, y_split - 0.08, f"weight {pow2(32 * position)}", ha="center",
                va="top", fontsize=8.5, color=fs.MUTED)
    terms = " + ".join(f"{v} × {pow2(32 * i)}" for i, v in enumerate(split) if v)
    ax.text(X_LABEL, y_tonat, f"toNat = {terms} = {pow2(70)} + 5,   stored as limbs := "
            f"{lean_array(split)}  (index 0 is the low limb)",
            ha="left", va="top", fontsize=9.5, color=fs.INK)

    # Lower panel: 2^96 - 1 plus 1, the carry rippling through every limb.
    ax.plot([X_LABEL, WIDTH_UNITS - 0.2], [y_rule, y_rule], color=fs.LINE, lw=0.8)
    ax.text(X_LABEL, y_title2, f"A carry through every limb: LimbArray.add "
            f"(LimbArray.ofNat ({pow2(96)} - 1) 3) (LimbArray.ofNat 1 1)",
            ha="left", va="top", fontsize=10.5, color=fs.INK)
    for position in range(n_out):
        ax.text(limb_x(position, n_out) + LIMB_W / 2, y_a + LIMB_H + 0.08, f"limb {position}",
                ha="center", va="bottom", fontsize=9.5, color=fs.INK)
    row_label(ax, y_a, f"a = {pow2(96)} - 1, three limbs\nlimbs := #[{a[0]},\n"
              f"    {a[1]}, {a[2]}]")
    for position, value in enumerate(a):
        limb_box(ax, limb_x(position, n_out), y_a, value)
    row_label(ax, y_b, f"b = 1\nlimbs := {lean_array(b)}")
    for position in range(len(a)):
        limb_box(ax, limb_x(position, n_out), y_b, limb(b, position), stored=position < len(b))
    ax.text(X_LIMBS + LIMB_W - 0.3, y_b + LIMB_H / 2, "+", ha="right", va="center",
            fontsize=12, color=fs.INK)

    # Per-limb UInt64 sums with the stored low word and the carry out.
    row_label(ax, y_sum, "each limb sum in hex,\nformed in a UInt64")
    for step in steps:
        x = limb_x(step["index"], n_out) + LIMB_W / 2
        total_hex = f"{step['total']:X}"
        total_split = total_hex[:-8] + " " + total_hex[-8:] if len(total_hex) > 8 else total_hex
        text = (f"{hex32(step['a'])} + {hex32(step['b'])} + {step['carry_in']}\n"
                f"= {total_split}\n"
                f"store {hex32(step['stored'])}, carry {step['carry_out']}")
        ax.text(x, y_sum + LIMB_H / 2, text, ha="center", va="center", fontsize=8.5,
                color=fs.INK, family=MONO, linespacing=1.35)
    for step in steps:
        x_from = limb_x(step["index"], n_out) + LIMB_W / 2
        x_to = limb_x(step["index"] + 1, n_out) + LIMB_W / 2
        fs.arrow(ax, (x_from, y_arrow), (x_to, y_arrow), color=fs.VERMILION, linewidth=1.4)
        ax.text((x_from + x_to) / 2, y_arrow + 0.05, f"carry {step['carry_out']}", ha="center",
                va="bottom", fontsize=8.5, color=fs.VERMILION)

    row_label(ax, y_out, f"a + b = {pow2(96)}, four limbs\nlimbs := {lean_array(total)}")
    for position, value in enumerate(total):
        top_limb = position == n_out - 1
        limb_box(ax, limb_x(position, n_out), y_out, value,
                 facecolor=fs.ORANGE if top_limb else fs.PAPER_2)
    x_top = limb_x(n_out - 1, n_out)
    ax.text(x_top + LIMB_W / 2, y_out - 0.1, "the extra limb that add reserves;\n"
            "addLoop stores the final carry here", ha="center", va="top", fontsize=8.5,
            color=fs.INK, linespacing=1.25)

    out = fs.save(fig, "ch08-limb-arrays.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
