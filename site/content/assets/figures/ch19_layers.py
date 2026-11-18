#!/usr/bin/env python3
"""Draw the three source layers behind one binary32 addition, in two arrangements.

In the getting-started example, Floats supplies the
configured value and operation, Kernels supplies integer algorithms, and Numerics supplies
exact values and contracts used in their proofs. The solid arrow is an execution call;
the dotted arrow is a proof relationship, not another runtime call.

This explains those roles, not source counts or a complete import graph. It needs no Git.
Run from anywhere: python3 ch19_layers.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import figstyle as fs

OUT_NAME = "ch19-layers.png"


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (fs.MOBILE_WIDTH, 4.9) if mobile else (fs.WIDTH, 3.1)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    rows = [
        ("Floats", "formats and stored values", "x + y : Binary 8 23"),
        ("Kernels", "integer algorithms", "align, add, round"),
        ("Numerics", "exact values and contracts", "dyadics and rounding laws"),
    ]
    bottoms = [3.62, 1.92, 0.22] if mobile else [2.20, 1.20, 0.20]
    row_height = 1.12 if mobile else 0.70
    for (name, role, operation), bottom in zip(rows, bottoms):
        fs.box(ax, 0.18, bottom, width - 0.36, row_height)
        family = fs.MONO if name == "Floats" else None
        if mobile:
            ax.text(0.34, bottom + 0.88, name, fontsize=fs.SIZE_LABEL, va="center")
            ax.text(0.34, bottom + 0.60, role, fontsize=fs.SIZE_TICK, color=fs.MUTED,
                    va="center")
            ax.text(width / 2, bottom + 0.24, operation, fontsize=fs.SIZE_LABEL, ha="center",
                    va="center", family=family)
        else:
            ax.text(0.40, bottom + 0.46, name, fontsize=fs.SIZE_LABEL, va="center")
            ax.text(0.40, bottom + 0.20, role, fontsize=fs.SIZE_TICK, color=fs.MUTED,
                    va="center")
            ax.text(6.0, bottom + row_height / 2, operation, fontsize=fs.SIZE_LABEL,
                    ha="center", va="center", family=family)
    path_x = width / 2 if mobile else 6.0
    for index, label in enumerate(("calls", "proved using")):
        start = bottoms[index]
        end = bottoms[index + 1] + row_height
        ax.annotate("", xy=(path_x, end + 0.015), xytext=(path_x, start - 0.015),
                    arrowprops=dict(arrowstyle="-|>", lw=fs.LW_REF, color=fs.INK,
                                    linestyle="-" if index == 0 else ":"))
        ax.text(path_x + 0.15, (start + end) / 2, label, fontsize=fs.SIZE_TICK, va="center")
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    target = args.out or fs.ASSETS / OUT_NAME
    for mobile in (False, True):
        path = fs.mobile_path(target) if mobile else target
        print(f"wrote {fs.save(build_figure(mobile), OUT_NAME, path)}")


if __name__ == "__main__":
    main()
