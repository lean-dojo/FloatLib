#!/usr/bin/env python3
"""Draw content/assets/ch12-bit-layouts.png: the five named 16 to 128 bit layouts to one scale.

The chapter on IEEE binary formats tabulates binary16, bfloat16, binary32, binary64 and binary128 as five values of the
one `FloatFormat` descriptor. This figure draws the stored word of each as a row of three fields,
sign, exponent and fraction, with the same width per bit in every row, so the reader sees that the
exponent field grows from five bits to fifteen while the fraction grows from seven to one hundred
and twelve.

Sources. The field widths are the `expWidth` and `fracWidth` of the descriptors in
FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean (`binary16`, `bfloat16`,
`binary32`, `binary64`, `binary128`), and the total width is `bitWidth` from
FloatLib/Floats/Formats/BinaryInterchange/Format/Definition.lean, that is 1 + expWidth +
fracWidth. The same numbers appear in the chapter's table. Nothing else is drawn.

The phone companion keeps the common width per bit, puts each format name above its bar,
and moves the three field counts below it. --out writes both images beside the supplied path.

Run from anywhere: python3 ch12_bit_layouts.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

# (name, expWidth, fracWidth) as in Format/Catalog.lean, in the order of the chapter's table.
FORMATS = (
    ("binary16", 5, 10),
    ("bfloat16", 8, 7),
    ("binary32", 8, 23),
    ("binary64", 11, 52),
    ("binary128", 15, 112),
)

SIGN_COLOUR = fs.FIELD["sign"]
EXP_COLOUR = fs.FIELD["exponent"]
FRAC_COLOUR = fs.FIELD["fraction"]

ROW_HEIGHT = 0.8
ROW_PITCH = 1.45


def bit_width(exp_width: int, frac_width: int) -> int:
    """`FloatFormat.bitWidth`: sign + exponent + fraction."""
    return 1 + exp_width + frac_width


def key() -> list:
    """Legend handles shared by both arrangements."""
    return [Patch(facecolor=colour, edgecolor=fs.INK, linewidth=fs.LW_AXIS, label=label)
            for colour, label in ((SIGN_COLOUR, "sign"), (EXP_COLOUR, "exponent"),
                                  (FRAC_COLOUR, "fraction"))]


def draw_mobile():
    fig = plt.figure(figsize=(fs.MOBILE_WIDTH, 6.6))
    ax = fig.add_axes([0.04, 0.10, 0.92, 0.88])
    ax.set(xlim=(0, 130), ylim=(-0.05, 6.05))
    ax.axis("off")
    for row, (name, exponent, fraction) in enumerate(FORMATS):
        y = 5.2 - 1.15 * row
        total = bit_width(exponent, fraction)
        ax.text(0, y + 0.55, f"{name}, {total} bits", fontsize=fs.SIZE_LABEL)
        fields = [("", 1, SIGN_COLOUR), ("", exponent, EXP_COLOUR), ("", fraction, FRAC_COLOUR)]
        end = fs.bit_layout(ax, fields, y=y, height=0.25, label_bits=False)
        assert end == total
        ax.text(0, y - 0.30, f"1 + {exponent} + {fraction}", fontsize=fs.SIZE_TICK, color=fs.MUTED)
    fs.legend(fig, handles=key(), loc="lower center", bbox_to_anchor=(0.5, 0.02), ncols=3,
              columnspacing=1.0, handlelength=1.4)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    assert [bit_width(e, f) for _, e, f in FORMATS] == [16, 16, 32, 64, 128]

    fs.setup()
    widest = max(bit_width(e, f) for _, e, f in FORMATS)

    fig, ax = fs.figure(4.0)
    fig.subplots_adjust(left=0.0, right=1.0, top=1.0, bottom=0.0)
    ax.axis("off")
    ax.grid(False)

    for row, (name, exp_width, frac_width) in enumerate(FORMATS):
        # Most significant bit at the left; every row shares the origin so the fields line up.
        y = -(row * ROW_PITCH)
        fields = [
            ("", 1, SIGN_COLOUR),
            (str(exp_width), exp_width, EXP_COLOUR),
            (str(frac_width), frac_width, FRAC_COLOUR),
        ]
        end = fs.bit_layout(ax, fields, y=y, height=ROW_HEIGHT, label_bits=False, name_size=fs.SIZE_TICK)
        total = bit_width(exp_width, frac_width)
        assert end == total
        ax.text(-1.5, y + ROW_HEIGHT / 2, name, ha="right", va="center", fontsize=fs.SIZE_TICK,
                color=fs.INK)
        ax.text(end + 1.5, y + ROW_HEIGHT / 2, f"{total} bits", ha="left", va="center",
                fontsize=fs.SIZE_TICK, color=fs.MUTED)

    ax.set_xlim(-16, widest + 12)
    ax.set_ylim(-(len(FORMATS) - 1) * ROW_PITCH - 1.5, ROW_HEIGHT + 0.2)
    fs.legend(ax, handles=key(), loc="lower center", bbox_to_anchor=(0.5, 0.0), ncols=3,
              handlelength=1.6)

    out = fs.save(fig, "ch12-bit-layouts.png", out=args.out)
    print(f"wrote {out}")
    mobile = fs.mobile_path(out)
    print(f"wrote {fs.save(draw_mobile(), mobile.name, mobile)}")


if __name__ == "__main__":
    main()
