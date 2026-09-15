#!/usr/bin/env python3
"""Draw content/assets/ch14-tapered-precision.png: significand bits against magnitude.

Chapter 11 compares a 32-bit posit with binary32: 28 significand bits at one against 24, 12
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

POSIT_STYLE = dict(color=fs.BLUE, linestyle="-", linewidth=2.0)
B32_STYLE = dict(color=fs.ORANGE, linestyle="--", linewidth=2.0)


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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    fig, ax = fs.figure(4.0)

    px, py = step_series(posit_significand_bits, -160, 160, min_bits=2)
    bx, by = step_series(binary32_significand_bits, -160, 160)
    ax.step(px, py, where="post", **POSIT_STYLE)
    ax.step(bx, by, where="post", **B32_STYLE)
    isolated = [e for e in range(-160, 161) if posit_significand_bits(e) == 1]
    # Thin vertical markers remain distinct even for adjacent powers of two.
    ax.plot(isolated, [1] * len(isolated), linestyle="None", marker="|",
            markersize=6, markeredgewidth=1, color=fs.BLUE)

    # The chapter's two comparison points, read off the same functions. At one the binary32
    # marker sits inside the posit tent, so its label goes straight below it on two lines,
    # where the tent is still above the text; at 2^64 both labels fit to the right.
    for binade in (0, 64):
        p = posit_significand_bits(binade)
        b = binary32_significand_bits(binade)
        x = binade
        ax.plot([x], [p], marker="o", color=fs.BLUE, markersize=6, zorder=5)
        ax.plot([x], [b], marker="s", color=fs.ORANGE, markersize=6, markerfacecolor="white",
                markeredgewidth=1.4, zorder=5)
        if binade == 0:
            ax.annotate(f"posit {p} bits at 1", (x, p), textcoords="offset points",
                        xytext=(0, 9), ha="center", va="bottom", fontsize=9.5, color=fs.INK)
            ax.annotate(f"binary32\n{b} bits at 1", (x, b), textcoords="offset points",
                        xytext=(0, -12), ha="center", va="top", fontsize=9.5, color=fs.INK,
                        linespacing=1.2,
                        arrowprops=dict(arrowstyle="-", color=fs.INK, lw=0.7, shrinkA=0,
                                        shrinkB=5))
        else:
            at = rf"at $2^{{{binade}}}$"
            ax.annotate(f"posit {p} bits {at}", (x, p), textcoords="offset points",
                        xytext=(8, 9), ha="left", va="bottom", fontsize=9.5, color=fs.INK)
            ax.annotate(f"binary32 {b} bits {at}", (x, b), textcoords="offset points",
                        xytext=(8, -11), ha="left", va="top", fontsize=9.5, color=fs.INK)

    ax.set_xlim(-160, 145)
    ax.set_ylim(0, 31.5)
    ticks = list(range(-150, 151, 30))
    ax.set_xticks(ticks, labels=[rf"$2^{{{t}}}$" for t in ticks])
    ax.set_yticks(range(0, 31, 4))
    ax.set_xlabel("magnitude of the value")
    ax.set_ylabel("significand bits (fraction bits plus one)")

    handles = [
        Line2D([], [], marker="o", markersize=6, label="32-bit posit (Posit.Format with 32 bits)",
               **POSIT_STYLE),
        Line2D([], [], marker="s", markersize=6, markerfacecolor="white", markeredgewidth=1.4,
               label="binary32 (FloatFormat.binary32)", **B32_STYLE),
    ]
    ax.legend(handles=handles, loc="lower left", bbox_to_anchor=(0.0, 1.0), ncol=2,
              columnspacing=2.0)

    out = fs.save(fig, "ch14-tapered-precision.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
