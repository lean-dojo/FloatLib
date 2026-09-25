#!/usr/bin/env python3
"""Draw the three source layers behind one binary32 addition, in two arrangements.

The roles and example follow chapter 01, "A tour of the codebase": Floats supplies the
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
from matplotlib.colors import to_rgba
from matplotlib.patches import Rectangle

OUT_NAME = "ch19-layers.png"


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 5.7) if mobile else (9.0, 3.8)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18,
            "Three layers behind\none addition" if mobile else "Three layers behind one addition",
            fontsize=14 if mobile else 16, weight="bold", va="top")
    rows = [
        ("Floats", "Formats + stored values", "x + y : Binary 8 23", fs.GREEN),
        ("Kernels", "Integer algorithms", "Align · add · round", fs.ORANGE),
        ("Numerics", "Exact values + contracts", "Dyadics + rounding laws", fs.BLUE),
    ]
    bottoms = [3.72, 2.02, 0.32] if mobile else [2.40, 1.40, 0.40]
    row_height = 1.12 if mobile else 0.75
    for (name, role, operation, colour), bottom in zip(rows, bottoms):
        ax.add_patch(Rectangle((0.18, bottom), width - 0.36, row_height,
                               facecolor=to_rgba(colour, 0.07), edgecolor=fs.LINE, lw=0.8))
        ax.add_patch(Rectangle((0.18, bottom), 0.045, row_height,
                               facecolor=colour, edgecolor="none"))
        if mobile:
            ax.text(0.34, bottom + 0.90, name, fontsize=14, weight="bold", va="center")
            ax.text(0.34, bottom + 0.62, role, fontsize=11.5, color=fs.MUTED, va="center")
            ax.text(width / 2, bottom + 0.24, operation, fontsize=12, ha="center",
                    va="center", family="DejaVu Sans Mono" if name == "Floats" else None)
        else:
            ax.text(0.40, bottom + 0.49, name, fontsize=14, weight="bold", va="center")
            ax.text(0.40, bottom + 0.20, role, fontsize=11.5, color=fs.MUTED, va="center")
            ax.text(6.0, bottom + row_height / 2, operation, fontsize=13, ha="center",
                    va="center", family="DejaVu Sans Mono" if name == "Floats" else None)
    path_x = width / 2 if mobile else 6.0
    for index, label in enumerate(("calls", "proved using")):
        start = bottoms[index]
        end = bottoms[index + 1] + row_height
        ax.annotate("", xy=(path_x, end + 0.015), xytext=(path_x, start - 0.015),
                    arrowprops=dict(arrowstyle="-|>", lw=1.25, color=fs.INK,
                                    linestyle="-" if index == 0 else ":"))
        ax.text(path_x + 0.15, (start + end) / 2, label, fontsize=11.5, va="center")
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    target = args.out or fs.ASSETS / OUT_NAME
    for mobile in (False, True):
        path = target.with_name(f"{target.stem}-mobile{target.suffix}") if mobile else target
        print(f"wrote {fs.save(build_figure(mobile), OUT_NAME, path)}")


if __name__ == "__main__":
    main()
