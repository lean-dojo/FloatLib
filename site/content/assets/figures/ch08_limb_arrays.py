#!/usr/bin/env python3
"""Draw content/assets/ch08-limb-arrays.png: one carry through three 32-bit limbs.

Chapter 13 introduces `FloatLib.Numerics.LimbArray` (FloatLib/Kernels/LimbArray/Core/Runtime.lean):
a natural number stored as a little-endian `Array UInt32`, limb i carrying weight 2^(32 i), with
limbs beyond the stored ones read as zero. Its Lean block prints two results checked here:

    #eval LimbArray.ofNat (2 ^ 70 + 5) 3
    -- { limbs := #[5, 0, 64] }
    #eval LimbArray.add (LimbArray.ofNat (2 ^ 96 - 1) 3) (LimbArray.ofNat 1 1)
    -- { limbs := #[0, 0, 0, 1] }

The figure follows only the second example, with B = 2^32 and array order stated explicitly.
`add` from FloatLib/Kernels/LimbArray/Arithmetic/Runtime.lean runs `addLoop`, which
at each limb forms `a_i + b_i + carry` in a UInt64, stores the low 32 bits, and passes the high
bits on as the next carry; the sum is placed in one limb more than the wider operand and the final
carry is stored there. Here every limb of 2^96 - 1 is 0xFFFFFFFF, so adding 1 carries through all
three limbs into the reserved fourth.

This script transcribes `ofNat` and `addLoop` into Python over integers, replays both examples,
and stops with an error if either result differs from the array the chapter prints. Every drawn
number (base-B digits, sums and carries) comes from that replay. Steps run left to right on
desktop and top to bottom on the phone.

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


def draw(mobile: bool, steps: list[dict]):
    fig = plt.figure(figsize=(3.8, 7.8) if mobile else (9, 4.7))
    fig.text(0.035, 0.98, "A carry through 32-bit limbs", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.915 if mobile else 0.87,
             "Each limb is a digit in base $B=2^{32}$.\nStart with [B−1, B−1, B−1] and add 1."
             if mobile else
             "Each limb is a base-$B$ digit, with $B=2^{32}$.  Add 1 to [B−1, B−1, B−1].",
             fontsize=12, linespacing=1.5, va="top" if mobile else "baseline")
    canvas = fig.add_axes([0, 0, 1, 1], zorder=0)
    canvas.set(xlim=(0, 1), ylim=(0, 1))
    canvas.axis("off")
    rects = ([(0.06, 0.64 - i * 0.175, 0.88, 0.125) for i in range(3)] if mobile else
             [(0.035 + i * 0.26, 0.36, 0.22, 0.29) for i in range(3)])
    for row, rect in zip(steps, rects):
        ax = fig.add_axes(rect)
        ax.set(xlim=(0, 1), ylim=(0, 1))
        ax.axis("off")
        ax.add_patch(Rectangle((0, 0), 1, 1, fc=fs.PAPER_2, ec=fs.LINE, lw=0.8))
        ax.text(0.05, 0.78, f"Limb {row['index']}", fontsize=12, weight="bold")
        ax.text(0.05, 0.45, "(B−1) + 1 = B", fontsize=13)
        ax.text(0.05, 0.11, "store 0; carry 1", fontsize=12, color=fs.BLUE)
    for i, (x, y, w, h) in enumerate(rects):
        if i < 2:
            nx, ny, nw, nh = rects[i + 1]
            start, end = ((x + w / 2, y), (nx + nw / 2, ny + nh)) if mobile else (
                (x + w, y + h / 2), (nx, ny + nh / 2))
        else:
            start, end = ((x + w / 2, y), (0.5, 0.235)) if mobile else (
                (x + w, y + h / 2), (0.85, y + h / 2))
        canvas.annotate("", end, start, arrowprops=dict(arrowstyle="->", color=fs.BLUE, lw=1.4))
        if mobile and i < 2:
            canvas.text(0.55, (start[1] + end[1]) / 2, "carry 1", fontsize=11.5, va="center")
    if mobile:
        canvas.add_patch(Rectangle((0.06, 0.155), 0.88, 0.077, fc=fs.PAPER_2, ec=fs.LINE, lw=0.8))
        canvas.text(0.10, 0.195, "New limb 3: store the final 1", fontsize=12, va="center")
    else:
        canvas.add_patch(Rectangle((0.85, 0.36), 0.12, 0.29, fc=fs.PAPER_2, ec=fs.LINE, lw=0.8))
        canvas.text(0.91, 0.585, "Limb 3", fontsize=12, ha="center", weight="bold")
        canvas.text(0.91, 0.47, "1", fontsize=16, ha="center", color=fs.BLUE)
        canvas.text(0.91, 0.39, "new limb", fontsize=11, ha="center")
    fig.text(0.035, 0.095 if mobile else 0.21,
             r"Result: $[0,0,0,1] = B^3 = 2^{96}$", fontsize=13, weight="bold")
    fig.text(0.035, 0.023 if mobile else 0.10,
             "Arrays list limb 0 first (lowest weight).\nThe added 1 enters limb 0; then it is a carry."
             if mobile else
             "Arrays list limb 0 first (lowest weight).  The added 1 enters limb 0; subsequent 1s are carries.",
             fontsize=11.5, color=fs.MUTED, linespacing=1.5)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    assert of_nat(SPLIT_VALUE, SPLIT_COUNT) == SPLIT_EXPECTED
    assert to_nat(SPLIT_EXPECTED) == SPLIT_VALUE
    a, b = of_nat(*ADD_LEFT), of_nat(*ADD_RIGHT)
    out_limbs, steps = add_loop(a, b)
    assert out_limbs == ADD_EXPECTED and to_nat(out_limbs) == 2 ** 96
    assert all(row["total"] == RADIX and row["stored"] == 0 and row["carry_out"] == 1 for row in steps)
    fs.setup()
    out = args.out or fs.ASSETS / "ch08-limb-arrays.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile, steps), target.name, target)}")


if __name__ == "__main__":
    main()
