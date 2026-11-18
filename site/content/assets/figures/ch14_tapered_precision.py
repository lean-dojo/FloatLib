#!/usr/bin/env python3
"""Draw content/assets/ch14-tapered-precision.png: significand bits against magnitude.

The chapter on posits compares a 32-bit posit with binary32: 28 significand bits at one against 24, 12
against 24 at 2^64, a range of [2^-120, 2^120] against binary32's 2^-149 (through subnormals) to
about 2^128. This figure plots the number of significand bits (fraction bits plus the implicit
leading one) that each format has for values in the binade [2^E, 2^(E+1)), as a function of E.

Both curves are arithmetic on parameters taken from the Lean source, nothing is measured:

* posit: FloatLib/Floats/Formats/Posit/Descriptor.lean (payloadBits = bits - 1,
  exponentBits = 2, regimeExponentStep = 4) with the field rules of
  FloatLib/Floats/Formats/Posit/Model/Fields.lean. For E = 4k + e the regime run is k + 1
  ones for k >= 0 and -k zeros for k < 0, one bit terminates it when room remains, up to two
  exponent bits follow, and the rest is fraction. At the extreme regimes fewer than two exponent
  bits remain. Missing low exponent bits must be zero, so some extreme binades are empty.
  Binades without fraction bits contain only a power of two; isolated markers show those
  values, with no line through the empty binades.
* binary32: FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean (expWidth 8,
  fracWidth 23, exponentBias 127): 24 bits for normal binades E in [-126, 127], and E + 150 bits
  in the subnormal binades E in [-149, -127], where the spacing is fixed at 2^-149.

Run from anywhere: python3 ch14_tapered_precision.py [--out PNG]
Also writes a <stem>-mobile.png companion beside the overview.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

POSIT_BITS = 32
PAYLOAD = POSIT_BITS - 1           # Format.payloadBits
EXPONENT_BITS = 2                  # Format.exponentBits
REGIME_STEP = 4                    # Format.regimeExponentStep

B32_EXP_WIDTH = 8                  # FloatFormat.binary32.expWidth
B32_FRAC_WIDTH = 23                # FloatFormat.binary32.fracWidth
B32_BIAS = 127                     # FloatFormat.binary32.exponentBias

POSIT_STYLE = dict(color=fs.ROLE["main"], linestyle="-", linewidth=fs.LW_DATA)
B32_STYLE = dict(color=fs.ROLE["second"], linestyle="--", linewidth=fs.LW_DATA)


def posit_significand_bits(binade: int) -> int | None:
    """Significand bits of a 32-bit posit for values in [2^binade, 2^(binade+1)), or None."""
    k, exponent = divmod(binade, REGIME_STEP)
    run = k + 1 if k >= 0 else -k
    # An all-zero payload is zero, whereas an all-one payload is maxpos.
    if run > PAYLOAD or (k < 0 and run == PAYLOAD):
        return None
    trailing = PAYLOAD - run - 1 if run < PAYLOAD else 0
    used = min(EXPONENT_BITS, trailing)
    if exponent % 2 ** (EXPONENT_BITS - used) != 0:
        return None
    return trailing - used + 1


def binary32_significand_bits(binade: int) -> int | None:
    min_normal = 1 - B32_BIAS                                   # -126
    max_normal = (2 ** B32_EXP_WIDTH - 2) - B32_BIAS            # 127
    min_subnormal = min_normal - B32_FRAC_WIDTH                 # -149
    if min_normal <= binade <= max_normal:
        return B32_FRAC_WIDTH + 1
    if min_subnormal <= binade < min_normal:
        return binade - min_subnormal + 1
    return None


def step_series(function, lo: int, hi: int, *, min_bits: int = 1):
    """Close each contiguous run of binades and break the line at omitted ones."""
    xs, ys = [], []
    previous = None
    for binade in range(lo, hi + 1):
        bits = function(binade)
        if bits is not None and bits < min_bits:
            bits = None
        if bits is None:
            if previous is not None:
                xs.extend((binade, binade))
                ys.extend((previous, float("nan")))
        else:
            xs.append(binade)
            ys.append(bits)
        previous = bits
    if previous is not None:
        xs.append(hi + 1)
        ys.append(previous)
    return xs, ys


ISOLATED_STYLE = dict(linestyle="None", marker="|", markersize=6, markeredgewidth=1,
                      color=fs.ROLE["main"])


def plot(ax, px, py, bx, by, isolated: list[int]) -> None:
    """Both precision curves on shared axes; thin marks stay distinct for adjacent binades."""
    ax.step(px, py, where="post", **POSIT_STYLE)
    ax.step(bx, by, where="post", **B32_STYLE)
    ax.plot(isolated, [1] * len(isolated), **ISOLATED_STYLE)
    ax.set_xlim(-160, 145)
    ax.set_ylim(0, 31.5)
    ax.set_yticks(range(0, 31, 4))
    ax.set_xlabel("magnitude of the value")
    ax.set_ylabel("significand (bits)")


def key() -> list:
    return [
        Line2D([], [], label="posit32", **POSIT_STYLE),
        Line2D([], [], label="binary32", **B32_STYLE),
        Line2D([], [], label="one posit in the binade", **ISOLATED_STYLE),
    ]


def draw_mobile(target: Path, px, py, bx, by, isolated: list[int]) -> Path:
    """Keep both precision curves and their comparison points at phone size."""
    fig, ax = fs.plt.subplots(figsize=(fs.MOBILE_WIDTH, 4.2))
    fig.subplots_adjust(left=0.19, right=0.96, bottom=0.20, top=0.80)
    plot(ax, px, py, bx, by, isolated)
    ticks = [-120, -60, 0, 60, 120]
    ax.set_xticks(ticks, labels=[rf"$2^{{{t}}}$" if t else "1" for t in ticks])
    fs.legend(fig, handles=key(), loc="upper center", bbox_to_anchor=(0.54, 0.99), ncols=2,
              columnspacing=1.0)
    return fs.save(fig, "ch14-tapered-precision.png", fs.mobile_path(target))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    fig, ax = fs.figure(4.0)

    px, py = step_series(posit_significand_bits, -160, 160, min_bits=2)
    bx, by = step_series(binary32_significand_bits, -160, 160)
    isolated = [e for e in range(-160, 161) if posit_significand_bits(e) == 1]
    plot(ax, px, py, bx, by, isolated)
    # The chapter's two comparison points, read off the same functions.
    assert (posit_significand_bits(0), binary32_significand_bits(0)) == (28, 24)
    assert (posit_significand_bits(64), binary32_significand_bits(64)) == (12, 24)
    ticks = list(range(-150, 151, 30))
    ax.set_xticks(ticks, labels=[rf"$2^{{{t}}}$" if t else "1" for t in ticks])
    fs.legend(ax, handles=key(), loc="lower left", bbox_to_anchor=(0.0, 1.02), ncols=3)

    out = fs.save(fig, "ch14-tapered-precision.png", args.out)
    draw_mobile(out, px, py, bx, by, isolated)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
