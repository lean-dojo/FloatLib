#!/usr/bin/env python3
"""Draw an executable addition, its specification, and their checked equality.

Source: FloatLib/Floats/ExecFloat/Backends/Selection/Certified.lean, whose Certified
structure contains run and run_eq_spec : run = spec. Chapter 05 explains the Runtime.lean
and Proof.lean organization, proof erasure, compilation, and the trust boundary.

The equation is equality of encoded results for every input, including exceptional words.
Connectors denote that equality, not an instruction to evaluate the reference after run.
The diagram makes no assertion about the correctness of the compiler or host FPU.

Run from anywhere: python3 ch05_runtime_proof_split.py [--out PNG]
The mobile companion is written beside the desktop image as <stem>-mobile.png.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import figstyle as fs
from matplotlib.colors import to_rgba
from matplotlib.patches import Rectangle

OUT_NAME = "ch05-runtime-proof-split.png"


def operation(ax, x, y, width, name, role, colour):
    fs.box(ax, x, y, width, 1.12, "", facecolor=to_rgba(colour, 0.07), edgecolor=colour)
    ax.text(x + width / 2, y + 0.76, name, ha="center", va="center", fontsize=16,
            family="DejaVu Sans Mono", weight="bold")
    ax.text(x + width / 2, y + 0.32, role, ha="center", va="center", fontsize=12)


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (3.8, 6.0) if mobile else (9.0, 3.6)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    ax.text(0.18, height - 0.18,
            "Run, specification,\nand their equality" if mobile
            else "An implementation and its specification",
            fontsize=14 if mobile else 16, weight="bold", va="top")
    if mobile:
        operation(ax, 0.22, 3.83, 3.36, "run x y", "Word / limb arithmetic", fs.BLUE)
        operation(ax, 0.22, 1.29, 3.36, "spec x y", "Reference addition", fs.GREEN)
        ax.plot([1.90, 1.90], [2.42, 3.82], color=fs.LINE, lw=1.2, zorder=0)
        # The equality sign and theorem interrupt the line: this is not an execution stage.
        ax.add_patch(Rectangle((0.22, 2.60), 3.36, 1.00,
                               facecolor="white", edgecolor="none", zorder=1))
        ax.text(1.90, 3.37, "=", ha="center", va="center", fontsize=25, zorder=2)
        ax.text(1.90, 3.00, "run_eq_spec : run = spec", ha="center", va="center",
                fontsize=11.5, family="DejaVu Sans Mono", zorder=2)
        ax.text(1.90, 2.69, "Proof.lean · checked by Lean", ha="center", va="center",
                fontsize=11.5, color=fs.MUTED, zorder=2)
        ax.text(1.90, 0.66, "Same encoded result\nfor every input.", ha="center",
                va="center", fontsize=12, linespacing=1.4)
    else:
        operation(ax, 0.30, 1.51, 3.20, "run x y", "Word / limb arithmetic", fs.BLUE)
        operation(ax, 5.50, 1.51, 3.20, "spec x y", "Reference addition", fs.GREEN)
        ax.plot([3.51, 4.20], [2.07, 2.07], color=fs.LINE, lw=1.2)
        ax.plot([4.80, 5.49], [2.07, 2.07], color=fs.LINE, lw=1.2)
        ax.text(4.50, 2.07, "=", ha="center", va="center", fontsize=27)
        ax.plot([4.50, 4.50], [1.06, 1.80], color=fs.LINE, lw=1.2)
        ax.text(4.50, 0.95, "run_eq_spec : run = spec", ha="center", va="center",
                fontsize=13, family="DejaVu Sans Mono")
        ax.text(4.50, 0.63, "Proof.lean · checked by Lean", ha="center", va="center",
                fontsize=11.5, color=fs.MUTED)
        ax.text(4.50, 0.22, "Same encoded result for every input, including exceptional words.",
                ha="center", va="center", fontsize=12)
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
