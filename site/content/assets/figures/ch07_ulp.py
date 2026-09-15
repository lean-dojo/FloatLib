#!/usr/bin/env python3
"""Draw content/assets/ch07-ulp.png: the unit in the last place and the two error bounds.

Chapter 07 ("The unit in the last place", "What a rounded result promises") says that the ulp
is beta^cexp(x), that nearest rounding is within half a ulp, that in a fixed precision format the
relative bound becomes the constant u = 2^-p, and that near zero this small relative bound no
longer holds because gradual underflow keeps the absolute spacing fixed while the values shrink.
This figure draws all of that for binary16 on two log-log panels. Left: ulp(x) and ulp(x)/2 against x,
flat across the subnormal range and doubling at every power of two above it. Right: the half ulp
bound divided by x, which is the relative bound `relative_error_round_ulp` states; it stays
between u/2 and u in the normal range and climbs to 1/2 at the smallest subnormal.

Sources:
* binary16 is expWidth 5, fracWidth 10, exponentBias 15 in
  FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean; `Model.fexpOf` in
  FloatLib/Floats/Formats/BinaryInterchange/Rounding/Proof.lean is
  `fltExp fmt.minSubnormalExponent (fmt.fracWidth + 1)`, and `minSubnormalExponent` in
  FloatLib/Floats/Formats/BinaryInterchange/Format/Properties.lean is 1 - bias - fracWidth,
  so the exponent function is fltExp (-24) 11, computed below from those three fields;
* `fltExp emin prec = fun e => max (e - prec) emin` from
  FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean; `ulp` (bpow of cexp away from
  zero) and `magnitude` from FloatLib/Floats/Formats/Flocq/Theory/Core.lean;
* the largest finite binary16 value, (2 - 2^-10) * 2^15 = 65504, from the same descriptor,
  bounds the x axis on the right; the smallest subnormal 2^-24 bounds it on the left.

Every drawn number is arithmetic on those parameters; nothing is estimated.

Run from anywhere: python3 ch07_ulp.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

TWO = Fraction(2)

# binary16, from Catalog.lean.
EXP_WIDTH = 5
FRAC_WIDTH = 10
EXPONENT_BIAS = 15

PREC = FRAC_WIDTH + 1                                  # fexpOf: fracWidth + 1
EMIN = 1 - EXPONENT_BIAS - FRAC_WIDTH                  # minSubnormalExponent
EMAX_NORMAL = (2 ** EXP_WIDTH - 2) - EXPONENT_BIAS      # largest biased exponent below the special one
MAX_FINITE = (2 - TWO ** -FRAC_WIDTH) * TWO ** EMAX_NORMAL
MIN_NORMAL_MAG = EMIN + PREC                            # magnitude at which fltExp leaves the flat part
U = TWO ** -PREC                                        # the unit roundoff the chapter names, 2^-p


def flt_exp(e: int) -> int:
    """Formats.lean `fltExp EMIN PREC`."""
    return max(e - PREC, EMIN)


def ulp_at_magnitude(mag: int) -> Fraction:
    """Core.lean `ulp` for a nonzero x of magnitude `mag`: bpow (fexp mag)."""
    return TWO ** flt_exp(mag)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    assert (EMIN, PREC) == (-24, 11), (EMIN, PREC)
    assert MAX_FINITE == 65504

    # Magnitudes from the smallest subnormal (magnitude EMIN + 1) up to the largest finite value.
    mags = list(range(EMIN + 1, EMAX_NORMAL + 2))
    x_lo, x_hi = float(TWO ** EMIN), float(MAX_FINITE)

    fs.setup()
    fig, (ax_abs, ax_rel) = plt.subplots(1, 2, figsize=(fs.WIDTH, 4.4))
    fig.subplots_adjust(left=0.09, right=0.99, bottom=0.14, top=0.86, wspace=0.28)

    min_normal = float(TWO ** (MIN_NORMAL_MAG - 1))
    for ax in (ax_abs, ax_rel):
        ax.set_xscale("log", base=2)
        ax.set_yscale("log", base=2)
        ax.set_xlim(x_lo / 2, x_hi * 2)
        ax.axvspan(x_lo / 2, min_normal, color=fs.PAPER_2, zorder=0, linewidth=0)
        ax.axvline(min_normal, color=fs.MUTED, linestyle=":", linewidth=0.9)
        ax.set_xlabel("positive real input $x$ (binary16 grid)")
        xticks = [2 ** k for k in range(-24, 17, 8)]
        ax.set_xticks(xticks, labels=[f"$2^{{{k}}}$" for k in range(-24, 17, 8)])
        ax.minorticks_off()

    # Left panel: ulp and half ulp, as step functions of x, one step per binade.
    xs, ulps = [], []
    for mag in mags:
        left, right = TWO ** (mag - 1), TWO ** mag
        xs += [float(left), float(min(right, MAX_FINITE))]
        ulps += [float(ulp_at_magnitude(mag))] * 2
    ax_abs.plot(xs, ulps, color=fs.BLUE, linewidth=1.8, label="ulp$(x)$")
    ax_abs.plot(xs, [u / 2 for u in ulps], color=fs.ORANGE, linewidth=1.6, linestyle="--",
                label="ulp$(x)/2$")
    yticks = [2 ** k for k in range(-24, 9, 8)]
    ax_abs.set_yticks(yticks, labels=[f"$2^{{{k}}}$" for k in range(-24, 9, 8)])
    ax_abs.set_ylim(2.0 ** -27, 2.0 ** 8)
    ax_abs.set_ylabel("absolute spacing and error bound")
    ax_abs.set_title("ulp, and half ulp, the nearest rounding bound", loc="left")
    ax_abs.text(float(TWO ** -23.5), 2.0 ** -24 * 1.7, f"subnormal:\nulp $= 2^{{{EMIN}}}$",
                ha="left", va="bottom", fontsize=9, color=fs.INK)
    ax_abs.text(min_normal * 1.4, 2.0 ** 6, f"smallest normal\n$2^{{{MIN_NORMAL_MAG - 1}}}$",
                ha="left", va="top", fontsize=9, color=fs.MUTED)
    ax_abs.legend(loc="lower right", fontsize=9)

    # Right panel: the relative half ulp bound ulp(x) / (2x), continuous within a binade.
    rx, rel = [], []
    for mag in mags:
        left, right = TWO ** (mag - 1), min(TWO ** mag, MAX_FINITE)
        half = ulp_at_magnitude(mag) / 2
        rx += [float(left), float(right), None]
        rel += [float(half / left), float(half / right), None]
    ax_rel.plot(rx, rel, color=fs.BLUE, linewidth=1.4, label="ulp$(x) / (2x)$")
    ax_rel.axhline(float(U), color=fs.VERMILION, linestyle="--", linewidth=1.4,
                   label=f"$u = 2^{{{-PREC}}}$ (normal range)")
    ax_rel.axhline(float(U / 2), color=fs.VERMILION, linestyle=":", linewidth=1.0,
                   label="$u/2$")
    ryticks = [2 ** k for k in range(-12, 0, 2)]
    ax_rel.set_yticks(ryticks, labels=[f"$2^{{{k}}}$" for k in range(-12, 0, 2)])
    ax_rel.set_ylim(2.0 ** -13, 2.0 ** 0)
    ax_rel.set_ylabel("relative error bound")
    ax_rel.set_title("the same bound divided by $x$", loc="left")
    ax_rel.text(float(TWO ** -20.5), 2.0 ** -2.2, "subnormal range:\nbound exceeds $u$",
                ha="left", va="top", fontsize=9, color=fs.INK,
                bbox=dict(facecolor="white", edgecolor="none", pad=0.2))
    ax_rel.text(float(TWO ** 4), 2.0 ** -9.6, "normal range:\nbetween $u/2$ and $u$",
                ha="center", va="top", fontsize=9, color=fs.INK)
    ax_rel.legend(loc="center right", bbox_to_anchor=(1.0, 0.6), fontsize=9,
                  frameon=True, facecolor="white", edgecolor="none", framealpha=1.0)

    out = fs.save(fig, "ch07-ulp.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
