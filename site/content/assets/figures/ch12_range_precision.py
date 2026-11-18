#!/usr/bin/env python3
"""Compare exact binary exponent limits with significand precision.

The descriptors come from BinaryInterchange/Format/Catalog.lean. For conventional
IEEE bias b = 2^(expWidth-1)-1, normal exponents run from 1-b to b, the least
subnormal is 2^(1-b-fracWidth), and precision p = fracWidth+1 includes the leading
bit. Panel (a) draws each range on a symmetric logarithmic exponent axis and writes the
exact least subnormal exponent and largest normal exponent at the ends of its bar; panel
(b) is linear in bits. Desktop and phone assets show the same five descriptors and limits,
with stacked panels on the phone.

Run: python3 ch12_range_precision.py [--out PNG]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

FORMATS = (
    ("binary16", 5, 10),
    ("bfloat16", 8, 7),
    ("binary32", 8, 23),
    ("binary64", 11, 52),
    ("binary128", 15, 112),
)


def constants(exp_width: int, frac_width: int) -> dict:
    bias = 2 ** (exp_width - 1) - 1
    return {"p": frac_width + 1, "e_min": 1 - bias, "e_max": bias,
            "e_sub": 1 - bias - frac_width}


def draw(mobile: bool):
    """(a) the exponents of normal and subnormal values, (b) the precision, one row per format."""
    if mobile:
        fig, (ax_range, ax_prec) = plt.subplots(2, 1, figsize=(fs.MOBILE_WIDTH, 6.2))
        fig.subplots_adjust(left=0.27, right=0.93, top=0.95, bottom=0.10, hspace=0.75)
    else:
        fig, (ax_range, ax_prec) = plt.subplots(
            1, 2, figsize=(fs.WIDTH, 3.3), gridspec_kw={"width_ratios": [1.9, 1.0]})
        fig.subplots_adjust(left=0.105, right=0.975, top=0.90, bottom=0.30, wspace=0.34)
    rows = [constants(e, f) for _, e, f in FORMATS]
    names = [name for name, _, _ in FORMATS]
    ys = list(range(len(FORMATS) - 1, -1, -1))
    main, second = fs.ROLE["main"], fs.ROLE["second"]

    ax_range.set_xscale("symlog", base=2, linthresh=8, linscale=0.6)
    for y, c in zip(ys, rows):
        ax_range.barh(y, c["e_min"] - c["e_sub"], left=c["e_sub"], height=0.3, color=second)
        ax_range.barh(y, c["e_max"] - c["e_min"], left=c["e_min"], height=0.52, color=main)
        ax_range.text(c["e_sub"] * 1.25, y, f"{c['e_sub']:,}".replace("-", "−"),
                      fontsize=fs.SIZE_SMALL, ha="right", va="center")
        ax_range.text(c["e_max"] * 1.25, y, f"{c['e_max']:,}", fontsize=fs.SIZE_SMALL,
                      ha="left", va="center")
    limit = 2 ** 25 if mobile else 2 ** 20
    ax_range.set_xlim(-limit, limit)
    ticks = [-2 ** 14, 0, 2 ** 14] if mobile else [-2 ** 14, -2 ** 7, 0, 2 ** 7, 2 ** 14]
    ax_range.set_xticks(ticks, labels=[f"{tick:,}".replace("-", "−") for tick in ticks])
    ax_range.minorticks_off()
    ax_range.set_yticks(ys, labels=names)
    ax_range.tick_params(axis="y", length=0)
    ax_range.set_xlabel("exponent $e$ of the leading digit")
    fs.value_grid(ax_range, "x")
    fs.panel_title(ax_range, 0, "exponent range")
    handles = [Patch(facecolor=main, label="normal"), Patch(facecolor=second, label="subnormal")]
    fs.legend(ax_range, handles=handles, loc="upper center",
              bbox_to_anchor=(0.5, -0.42 if mobile else -0.30), ncols=2)

    ax_prec.barh(ys, [c["p"] for c in rows], color=main, height=0.52)
    for y, c in zip(ys, rows):
        ax_prec.text(c["p"] + 3, y, str(c["p"]), fontsize=fs.SIZE_SMALL, va="center")
    ax_prec.set_yticks(ys, labels=names if mobile else [])
    ax_prec.tick_params(axis="y", length=0)
    ax_prec.set_xlim(0, 136)
    ax_prec.set_xticks([0, 32, 64, 96, 128])
    ax_prec.set_xlabel("precision $p$ (bits)")
    fs.value_grid(ax_prec, "x")
    fs.panel_title(ax_prec, 1, "precision")
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    assert [constants(e, f)["p"] for _, e, f in FORMATS] == [11, 8, 24, 53, 113]
    assert [constants(e, f)["e_sub"] for _, e, f in FORMATS] == [-24, -133, -149, -1074, -16494]
    fs.setup()
    out = args.out or fs.ASSETS / "ch12-range-precision.png"
    for mobile in (False, True):
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
