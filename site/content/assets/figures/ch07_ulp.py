#!/usr/bin/env python3
"""Draw content/assets/ch07-ulp.png: the unit in the last place and the two error bounds.

Chapter 07 ("The unit in the last place", "What a rounded result promises") says that the ulp
is beta^cexp(x), that nearest rounding is within half a ulp, that in a fixed precision format the
relative bound becomes the constant u = 2^-p, and that near zero this small relative bound no
longer holds because gradual underflow keeps the absolute spacing fixed while the values shrink.
This figure draws all of that for binary16 on two log-log panels, stacked on the phone.
First: ulp(x) and ulp(x)/2 against x, flat across the subnormal range and doubling at every
power of two above it. Second: the half ulp
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


def draw(mobile: bool):
    fig, axes = plt.subplots(2, 1, figsize=(3.8, 7.6)) if mobile else plt.subplots(
        1, 2, figsize=(9, 4.6))
    fig.subplots_adjust(left=0.19 if mobile else 0.09, right=0.97,
                        bottom=0.14 if mobile else 0.20, top=0.84 if mobile else 0.74,
                        hspace=0.60, wspace=0.30)
    ax_abs, ax_rel = axes
    fig.text(0.035, 0.98, "Spacing and nearest-rounding bounds", fontsize=13.5,
             weight="bold", va="top")
    fig.text(0.035, 0.915 if mobile else 0.90,
             "binary16; positive finite range", fontsize=11.5, color=fs.MUTED)
    mags = list(range(EMIN + 1, EMAX_NORMAL + 2))
    x_lo, x_hi = float(TWO ** EMIN), float(MAX_FINITE)
    min_normal = float(TWO ** (MIN_NORMAL_MAG - 1))
    for ax in axes:
        ax.set_xscale("log", base=2)
        ax.set_yscale("log", base=2)
        ax.set_xlim(x_lo, x_hi)
        ax.axvspan(x_lo, min_normal, color=fs.PAPER_2, zorder=0, linewidth=0)
        ax.axvline(min_normal, color=fs.MUTED, linestyle=":", linewidth=1)
        ax.set_xlabel("positive input $x$", fontsize=11.5)
        ticks = [-24, -14, 0, 15]
        ax.set_xticks([2.0 ** k for k in ticks], labels=[f"$2^{{{k}}}$" for k in ticks])
        ax.tick_params(labelsize=11)
        ax.minorticks_off()
    xs, ulps, rx, rel = [], [], [], []
    for mag in mags:
        left, right = TWO ** (mag - 1), min(TWO ** mag, MAX_FINITE)
        half = ulp_at_magnitude(mag) / 2
        xs += [float(left), float(right)]
        ulps += [float(2 * half)] * 2
        rx += [float(left), float(right), None]
        rel += [float(half / left), float(half / right), None]
    ax_abs.plot(xs, ulps, color=fs.BLUE, linewidth=1.8, label="ulp")
    ax_abs.plot(xs, [u / 2 for u in ulps], color=fs.ORANGE, linewidth=1.7,
                linestyle="--", label="half ulp")
    ticks = [-24, -16, -8, 0]
    ax_abs.set_yticks([2.0 ** k for k in ticks], labels=[f"$2^{{{k}}}$" for k in ticks])
    ax_abs.set_ylim(2.0 ** -27, 2.0 ** 7)
    ax_abs.set_title("Absolute spacing", fontsize=12.5, loc="left", pad=12)
    ax_abs.text(0.03, 0.92, "subnormal\nspacing stays fixed", transform=ax_abs.transAxes,
                fontsize=11, va="top")
    ax_abs.legend(loc="lower right", fontsize=11, frameon=True,
                  facecolor="white", edgecolor="none", framealpha=1)
    ax_rel.plot(rx, rel, color=fs.BLUE, linewidth=1.5)
    ax_rel.axhline(float(U), color=fs.VERMILION, linestyle="--", linewidth=1.3)
    ax_rel.axhline(float(U / 2), color=fs.VERMILION, linestyle=":", linewidth=1)
    ticks = [-12, -8, -4, 0]
    ax_rel.set_yticks([2.0 ** k for k in ticks], labels=[f"$2^{{{k}}}$" for k in ticks])
    ax_rel.set_ylim(2.0 ** -13, 1)
    ax_rel.set_title(r"Relative bound: $\mathrm{ulp}(x)/(2x)$", fontsize=12.5, loc="left", pad=12)
    ax_rel.text(0.03, 0.91, "near zero:\nbound grows", transform=ax_rel.transAxes,
                fontsize=11, va="top")
    ax_rel.text(0.42, 0.48, "$u=2^{-11}$\nnormal bound", transform=ax_rel.transAxes,
                fontsize=11.5, color=fs.VERMILION)
    fig.text(0.035, 0.017, r"Shading: subnormals. Normals start at $2^{-14}$.",
             fontsize=11.5, color=fs.MUTED)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    assert (EMIN, PREC) == (-24, 11)
    assert MAX_FINITE == 65504
    fs.setup()
    out = args.out or fs.ASSETS / "ch07-ulp.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
