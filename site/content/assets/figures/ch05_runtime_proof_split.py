#!/usr/bin/env python3
"""Draw an executable addition, its specification, and their checked equality.

Source: FloatLib/Kernels/Selection/Certified.lean, whose Certified
structure contains run and run_eq_spec : run = spec. The chapter on executable arithmetic explains the Runtime.lean
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
from matplotlib.patches import Rectangle

OUT_NAME = "ch05-runtime-proof-split.png"


def operation(ax, x, y, width, name, role):
    fs.box(ax, x, y, width, 1.0)
    ax.text(x + width / 2, y + 0.66, name, ha="center", va="center", fontsize=fs.SIZE_LABEL,
            family=fs.MONO)
    ax.text(x + width / 2, y + 0.30, role, ha="center", va="center", fontsize=fs.SIZE_TICK,
            color=fs.MUTED)


def build_figure(mobile: bool = False):
    fs.setup()
    width, height = (fs.MOBILE_WIDTH, 4.2) if mobile else (fs.WIDTH, 2.2)
    fig = fs.plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    if mobile:
        operation(ax, 0.22, 2.95, 3.36, "run x y", "word and limb arithmetic")
        operation(ax, 0.22, 0.25, 3.36, "spec x y", "reference addition")
        ax.plot([1.90, 1.90], [1.25, 2.95], color=fs.LINE, lw=fs.LW_REF, zorder=0)
        # The equality sign and theorem interrupt the line: this is not an execution stage.
        ax.add_patch(Rectangle((0.22, 1.72), 3.36, 0.80,
                               facecolor="white", edgecolor="none", zorder=1))
        ax.text(1.90, 2.30, "=", ha="center", va="center", fontsize=fs.SIZE_LABEL, zorder=2)
        ax.text(1.90, 1.94, "run_eq_spec : run = spec", ha="center", va="center",
                fontsize=fs.SIZE_TICK, family=fs.MONO, zorder=2)
    else:
        operation(ax, 0.30, 0.95, 3.20, "run x y", "word and limb arithmetic")
        operation(ax, 5.50, 0.95, 3.20, "spec x y", "reference addition")
        ax.plot([3.50, 4.25], [1.45, 1.45], color=fs.LINE, lw=fs.LW_REF)
        ax.plot([4.75, 5.50], [1.45, 1.45], color=fs.LINE, lw=fs.LW_REF)
        ax.text(4.50, 1.45, "=", ha="center", va="center", fontsize=fs.SIZE_LABEL)
        ax.plot([4.50, 4.50], [0.55, 1.22], color=fs.LINE, lw=fs.LW_REF)
        ax.text(4.50, 0.38, "run_eq_spec : run = spec", ha="center", va="center",
                fontsize=fs.SIZE_TICK, family=fs.MONO)
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
