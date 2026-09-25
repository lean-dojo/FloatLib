#!/usr/bin/env python3
"""Compare exact binary exponent limits with significand precision.

The descriptors come from BinaryInterchange/Format/Catalog.lean. For conventional
IEEE bias b = 2^(expWidth-1)-1, normal exponents run from 1-b to b, the least
subnormal is 2^(1-b-fracWidth), and precision p = fracWidth+1 includes the leading
bit. The exponent table uses exact integers; the precision axis is linear in bits.
There is no compressed numeric-value axis. Desktop and phone assets show the same
five descriptors and limits, with stacked panels on the phone.

Run: python3 ch12_range_precision.py [--out PNG]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402

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
    fig = plt.figure(figsize=(3.8, 7.3) if mobile else (9, 4.35))
    fig.text(0.035, 0.98, "Range and precision", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.915 if mobile else 0.875,
             "Wider exponents or more significant bits?", fontsize=11.5, color=fs.MUTED)
    table = fig.add_axes([0.035, 0.49, 0.93, 0.36] if mobile else [0.025, 0.19, 0.59, 0.58])
    table.set(xlim=(0, 1), ylim=(-0.55, 5.25))
    table.axis("off")
    table.text(0, 5.05, "Exponent limits (base 2)", fontsize=12.5, weight="bold")
    table.text(0.48 if mobile else 0.47, 4.4, "normal $e$", fontsize=11, ha="center")
    table.text(0.86, 4.4, "least\nsubnormal", fontsize=11, ha="center", va="center")
    rows = [constants(e, f) for _, e, f in FORMATS]
    for i, ((name, _, _), c) in enumerate(zip(FORMATS, rows)):
        y = 3.55 - i * 0.85
        table.text(0, y, name, fontsize=11.5, va="center")
        table.text(0.48 if mobile else 0.47, y,
                   f"{c['e_min']} to {c['e_max']}", fontsize=11.5, ha="center", va="center")
        table.text(0.89, y, f"$2^{{{c['e_sub']}}}$", fontsize=12, ha="center", va="center")
        table.plot([0, 1], [y - 0.39, y - 0.39], color=fs.LINE, lw=0.5)
    ax = fig.add_axes([0.28, 0.18, 0.65, 0.25] if mobile else [0.72, 0.24, 0.25, 0.48])
    ys = list(range(4, -1, -1))
    colours = [fs.BLUE, fs.ORANGE, fs.BLUE, fs.BLUE, fs.BLUE]
    ax.barh(ys, [c["p"] for c in rows], color=colours, height=0.52)
    for y, c in zip(ys, rows):
        ax.text(c["p"] + 3, y, str(c["p"]), fontsize=11.5, va="center")
    ax.set_yticks(ys, labels=[name for name, _, _ in FORMATS], fontsize=11.5)
    ax.tick_params(axis="y", length=0)
    ax.tick_params(axis="x", labelsize=11)
    ax.set_xlim(0, 132)
    ax.set_xticks([0, 32, 64, 96, 128])
    ax.set_xlabel("precision $p$ (bits)", fontsize=11.5)
    ax.set_title("Significand precision", fontsize=12.5, loc="left", pad=12)
    ax.grid(axis="y", visible=False)
    fig.text(0.035, 0.025,
             "Normal values: $m\\,2^e$, with $1 \\leq m < 2$.\nPrecision includes the leading bit."
             if mobile else
             "Normal values: $m\\,2^e$, with $1 \\leq m < 2$.  Precision includes the leading bit.",
             fontsize=11.5, color=fs.MUTED, linespacing=1.5)
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
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile), target.name, target)}")


if __name__ == "__main__":
    main()
