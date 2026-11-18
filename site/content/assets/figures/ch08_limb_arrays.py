#!/usr/bin/env python3
"""Draw content/assets/ch08-limb-arrays.png: one carry through three 32-bit limbs.

The chapter on arithmetic performance introduces `FloatLib.Numerics.LimbArray` (FloatLib/Kernels/LimbArray/Core/Runtime.lean):
a natural number stored as a little-endian `Array UInt32`, limb i carrying weight 2^(32 i), with
limbs beyond the stored ones read as zero. Its Lean block prints two results checked here:

    #eval LimbArray.ofNat (2 ^ 70 + 5) 3
    -- { limbs := #[5, 0, 64] }
    #eval LimbArray.add (LimbArray.ofNat (2 ^ 96 - 1) 3) (LimbArray.ofNat 1 1)
    -- { limbs := #[0, 0, 0, 1] }

The figure follows only the second example, with B = 2^32; limb 0, the lowest, is drawn first.
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
    """Four limb cells, lowest limb first; each arrow carries one into the next cell."""
    width, height = (fs.MOBILE_WIDTH, 5.4) if mobile else (fs.WIDTH, 1.7)
    fig = plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    cells = len(steps) + 1
    if mobile:
        w, h, gap = 3.0, 0.95, 0.42
        origins = [(0.4, height - 0.15 - h - i * (h + gap)) for i in range(cells)]
    else:
        w, h, gap = 1.72, 1.3, 0.62
        origins = [(0.2 + i * (w + gap), 0.2) for i in range(cells)]
    for index, (x, y) in enumerate(origins):
        fs.box(ax, x, y, w, h)
        ax.text(x + 0.12, y + h - 0.22, f"limb {index}", fontsize=fs.SIZE_TICK, color=fs.MUTED,
                va="center")
        if index < len(steps):
            row = steps[index]
            assert row["total"] == RADIX and row["stored"] == 0 and row["carry_out"] == 1
            ax.text(x + w / 2, y + h / 2 - 0.02, "(B − 1) + 1 = B", fontsize=fs.SIZE_LABEL,
                    ha="center", va="center")
            ax.text(x + w / 2, y + 0.2, f"stores {row['stored']}", fontsize=fs.SIZE_TICK,
                    ha="center", va="center")
        else:
            ax.text(x + w / 2, y + h / 2 - 0.02, "1", fontsize=fs.SIZE_LABEL, ha="center",
                    va="center")
        if index + 1 < cells:
            nx, ny = origins[index + 1]
            start, end = ((x + w / 2, y), (nx + w / 2, ny + h)) if mobile else (
                (x + w, y + h / 2), (nx, ny + h / 2))
            fs.arrow(ax, start, end, color=fs.ROLE["main"], linewidth=fs.LW_REF + 0.4)
            if mobile:
                ax.text(start[0] + 0.12, (start[1] + end[1]) / 2, "carry 1",
                        fontsize=fs.SIZE_TICK, va="center")
            else:
                ax.text((start[0] + end[0]) / 2, start[1] + 0.12, "carry 1",
                        fontsize=fs.SIZE_TICK, ha="center", va="bottom")
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
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile, steps), target.name, target)}")


if __name__ == "__main__":
    main()
