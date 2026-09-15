#!/usr/bin/env python3
"""Draw content/assets/ch05-runtime-proof-split.png: the Runtime.lean and Proof.lean split.

The figure in chapter 05 shows the one convention that runs through the library: a concept's
executable definitions live in a Runtime.lean, the theorems about them in a sibling Proof.lean,
and the two routes out of those files, the compiled code the compiler ships and the proof
Lean's kernel checks, meet only at the equation run = spec.

Everything drawn is a statement of site/content/chapters/05-why-execution-and-proofs-are-separate.md,
in the chapter's own words:

* the import rules of the two files and the check that enforces them, tests/checks/architecture.sh
  (the rules are the ones the chapter lists under "The check that enforces the split");
* the example pair ExecFloat/Backends/Dispatch/Add/Runtime.lean, which defines the dispatcher
  AddBackend.word, and its Proof.lean, which proves word_eq_spec (paths relative to
  FloatLib/Floats/, as in the chapter);
* the three fields of Backend.Certified (a cost estimate, run, and run_eq_spec : run = spec),
  from FloatLib/Floats/ExecFloat/Backends/Selection/Certified.lean as the chapter describes it;
* the @[csimp] count, 38 `@[csimp] theorem` declarations in 14 files of FloatLib/ on the working
  tree, which the chapter states under "What csimp does, and what it does not".

Every string drawn is checked for em and en dashes before saving (figstyle.save does it).

Run from anywhere: python3 ch05_runtime_proof_split.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
from matplotlib.patches import FancyBboxPatch  # noqa: E402

OUT_NAME = "ch05-runtime-proof-split.png"

# Colours (Okabe and Ito, from figstyle). The compiled route is blue with solid edges, the
# kernel-checked route is green with dashed edges, so the two are told apart by line style and
# by their labels as well as by colour.
COMPILED = fs.BLUE
CHECKED = fs.GREEN
FORBIDDEN = fs.VERMILION


def tint(hex_colour: str, amount: float) -> str:
    """Mix a colour with white; amount 0 is white, 1 is the colour itself."""
    r, g, b = (int(hex_colour[i:i + 2], 16) for i in (1, 3, 5))
    mix = lambda c: int(round(255 + (c - 255) * amount))  # noqa: E731
    return f"#{mix(r):02x}{mix(g):02x}{mix(b):02x}"


def titled_box(ax, x, y, w, h, title, body, *, edgecolor=fs.INK, facecolor=fs.PAPER_2,
               linestyle="-", linewidth=1.1, title_size=10, body_size=9.2, pad=0.14,
               mono_title=False):
    """A rounded box with a bold title at the top left and a left-aligned body under it."""
    patch = FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0,rounding_size=0.08",
                           facecolor=facecolor, edgecolor=edgecolor, linewidth=linewidth,
                           linestyle=linestyle)
    ax.add_patch(patch)
    family = "DejaVu Sans Mono" if mono_title else "DejaVu Sans"
    ax.text(x + pad, y + h - pad, title, ha="left", va="top", fontsize=title_size,
            fontweight="bold", color=fs.INK, family=family)
    ax.text(x + pad, y + h - pad - 0.26, body, ha="left", va="top", fontsize=body_size,
            color=fs.INK, linespacing=1.32)
    return patch


def draw(out: Path | None) -> Path:
    fs.setup()
    height = 6.7
    fig, default_axes = fs.figure(height)
    default_axes.remove()
    ax = fs.diagram_axes(fig, (0, fs.WIDTH), (0, height))

    top = height - 0.15
    ax.text(fs.WIDTH / 2, top, "One concept, two files, two routes: what ships and what is proved "
            "meet at one equation", ha="center", va="top", fontsize=11, fontweight="bold")

    # Columns: two boxes of equal width with a gap for the import arrows between them.
    lx, rx, w = 0.25, 4.9, 3.85

    # Row 1: the two files.
    h1 = 1.5
    y1 = top - 0.45 - h1
    titled_box(ax, lx, y1, w, h1, "Runtime.lean",
               "executable definitions, for example the dispatcher\n"
               "AddBackend.word in\n"
               "ExecFloat/Backends/Dispatch/Add/Runtime.lean\n"
               "imports other runtime modules, shared core\n"
               "modules, and the Mathlib definitions its\n"
               "statements need",
               edgecolor=COMPILED, facecolor=tint(COMPILED, 0.10), mono_title=True)
    titled_box(ax, rx, y1, w, h1, "Proof.lean",
               "theorems about them, for example word_eq_spec,\n"
               "AddBackend.word x y = Spec.add x y, in\n"
               "ExecFloat/Backends/Dispatch/Add/Proof.lean\n"
               "imports the runtime module, the proof modules\n"
               "of whatever it builds on, and the Mathlib\n"
               "theories it needs",
               edgecolor=CHECKED, facecolor=tint(CHECKED, 0.10), linestyle="--",
               mono_title=True)

    # Proof imports Runtime; the reverse needs a documented exception.
    xm = (lx + w + rx) / 2
    ya = y1 + h1 - 0.3
    fs.arrow(ax, (rx, ya), (lx + w, ya), color=fs.INK, linewidth=1.2)
    ax.text(xm, ya + 0.06, "imports", ha="center", va="bottom", fontsize=9.2)
    yb = y1 + 0.3
    fs.arrow(ax, (lx + w, yb), (rx, yb), color=FORBIDDEN, linewidth=1.2, style="-|>")
    ax.plot([xm - 0.09, xm + 0.09], [yb - 0.09, yb + 0.09], color=FORBIDDEN, lw=1.6)
    ax.plot([xm - 0.09, xm + 0.09], [yb + 0.09, yb - 0.09], color=FORBIDDEN, lw=1.6)
    ax.text(xm, y1 - 0.08, "blocked unless a documented proof-import exception applies", ha="center",
            va="top", fontsize=9.2, color=FORBIDDEN)

    # Row 2: compiler and kernel.
    h2 = 1.3
    y2 = y1 - 0.5 - h2
    titled_box(ax, lx, y2, w, h2, "Lean's compiler: what ships",
               "compiles the runtime definitions; proofs are erased\n"
               "@[csimp] theorem readable = fast: the compiler\n"
               "replaces the readable definition by the fast one\n"
               "in generated code (38 such theorems in 14 files\n"
               "of FloatLib/)",
               edgecolor=COMPILED, facecolor=tint(COMPILED, 0.10))
    titled_box(ax, rx, y2, w, h2, "Lean's kernel: what is proved",
               "the small trusted checker that validates proof\n"
               "terms and reduces definitions\n"
               "checks run_eq_spec, and checks that both sides\n"
               "of every @[csimp] equation agree",
               edgecolor=CHECKED, facecolor=tint(CHECKED, 0.10), linestyle="--")

    # Row 3: what each route delivers.
    h3 = 0.95
    y3 = y2 - 0.5 - h3
    titled_box(ax, lx, y3, w, h3, "At run time",
               "x + y calls the selected implementation, run,\n"
               "chosen by its cost estimate; no theorem is ever\n"
               "executed",
               edgecolor=COMPILED, facecolor=tint(COMPILED, 0.10))
    titled_box(ax, rx, y3, w, h3, "In the certificate",
               "Certified spec: a cost estimate, an executable run,\n"
               "and the proof run_eq_spec : run = spec,\n"
               "a Prop field the compiler erases",
               edgecolor=CHECKED, facecolor=tint(CHECKED, 0.10), linestyle="--")

    # Vertical arrows down each route.
    for x, colour, ls in ((lx + w / 2, COMPILED, "-"), (rx + w / 2, CHECKED, "--")):
        for ytop, ybot in ((y1, y2 + h2), (y2, y3 + h3)):
            ax.annotate("", xy=(x, ybot), xytext=(x, ytop),
                        arrowprops=dict(arrowstyle="-|>", color=colour, lw=1.4,
                                        linestyle=ls, shrinkA=2, shrinkB=2))

    # The equation where the two routes meet.
    ew, eh = 2.6, 0.62
    ex, ey = (fs.WIDTH - ew) / 2, 0.22
    patch = FancyBboxPatch((ex, ey), ew, eh, boxstyle="round,pad=0,rounding_size=0.08",
                           facecolor="white", edgecolor=fs.INK, linewidth=1.4)
    ax.add_patch(patch)
    ax.text(ex + ew / 2, ey + eh - 0.12, "run = spec", ha="center", va="top", fontsize=12,
            fontweight="bold", family="DejaVu Sans Mono")
    ax.text(ex + ew / 2, ey + 0.1, "the only place the two routes meet", ha="center",
            va="bottom", fontsize=9.2, color=fs.MUTED)
    ymid = ey + eh / 2 + 0.05
    ax.annotate("", xy=(ex, ymid), xytext=(lx + w / 2, y3),
                arrowprops=dict(arrowstyle="-|>", color=COMPILED, lw=1.4, shrinkA=2, shrinkB=2,
                                connectionstyle="angle,angleA=-90,angleB=180,rad=8"))
    ax.annotate("", xy=(ex + ew, ymid), xytext=(rx + w / 2, y3),
                arrowprops=dict(arrowstyle="-|>", color=CHECKED, lw=1.4, linestyle="--",
                                shrinkA=2, shrinkB=2,
                                connectionstyle="angle,angleA=-90,angleB=0,rad=8"))
    ax.text(lx + w / 2 - 0.1, (y3 + ymid) / 2 + 0.05, "what runs", ha="right", va="center",
            fontsize=9.2, color=COMPILED)
    ax.text(rx + w / 2 + 0.1, (y3 + ymid) / 2 + 0.05, "what it is proved equal to", ha="left",
            va="center", fontsize=9.2, color=CHECKED)

    return fs.save(fig, OUT_NAME, out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None, help="output PNG (default: assets)")
    args = parser.parse_args()
    target = draw(args.out)
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
