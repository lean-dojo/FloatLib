#!/usr/bin/env python3
"""Draw content/assets/ch09-backend-ladder.png: addition on six public carrier choices.

The boxes show the candidate kernel families described in chapter 14 for addition.
The exact baseline works for every descriptor. Every eligibility condition drawn is
copied from the Lean source named beside it:

* exhaustive table: `StoragePlan.byte (width_le : format.bitWidth ≤ 8)` in
  FloatLib/Floats/Formats/BinaryInterchange/Configured/Storage/Core.lean, the plan under which
  `automaticAddCandidates` in Configured/Plan/Automatic.lean prepends the byte table;
* fixed-format word kernel: `isFixedFormat` in Descriptor/Plan/Routes.lean, which decides
  `FloatFormat.IsBinary32 format ∨ FloatFormat.IsBinary64 format`, layout equalities defined in
  Format/Catalog.lean;
* machine-word kernel: `Model.NativeSmallWord.StorageEligible`, `fmt.isIEEE = true ∧
  fmt.bitWidth ≤ 64`, in FloatLib/Floats/ExecFloat/Backends/Word/Small/Core/Runtime.lean (the
  route `structuralRoute?` tests for addition; the per-operation capacity contracts the chapter
  describes live in the same directory);
* fixed-limb kernel: `Model.NativePair.Eligible`, `fmt.isIEEE = true ∧ 64 < fmt.fracWidth ∧
  fmt.bitWidth ≤ 128`, in Backends/FixedLimb/Pair/Core/Runtime.lean;
* wide-limb kernel: `Model.WideLimb.Eligible`, `fmt.isIEEE = true ∧ 128 < fmt.bitWidth ∧
  fmt.expWidth ≤ 32`, in Backends/WideLimb/Core/Runtime.lean, offered by `wideLimbAdd?` in
  Configured/Plan/WideLimbCandidates.lean only under `StoragePlan.limbs (width_gt : 128 <
  format.bitWidth)`, the carrier `ExecFloat.BinaryLimbs` names;
* exact baseline: the `baseline` field of `addCandidates` in Configured/Plan/Candidates.lean,
  present for every descriptor and plan.

The layouts are FloatFormat.binary16, binary32, binary64, and binary128 from Format/Catalog.lean
(exponent and fraction widths 5/10, 8/23, 11/52, 15/112), plus the 256-bit layout on both
`ExecFloat.Binary 19 236` and `ExecFloat.BinaryLimbs 19 236`. Each encoded width is
`1 + expWidth + fracWidth` as `FloatFormat.bitWidth` defines it in Format/Definition.lean.
The arrows record chapter 14's `ExecFloat.Add.selectedCandidate` examples: `Binary.Family`
5 10, 8 23, 11 52, 15 112, and 19 236 select `nativeWord`, `fixedFormat`, `fixedFormat`,
`fixedLimbs`, and `generic`; `Binary.LimbFamily 19 236` selects `wideLimbs`. The six limb
forwarding instances in Configured/Plan/Instances.lean reuse the automatic capabilities with
the caller's PolicyFor instance. These arrows describe the default policy, not a promise that
every input uses a fast path. This script draws the chapter's statements; it does not run the
planner.

Run from anywhere: python3 ch09_backend_ladder.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import FancyBboxPatch  # noqa: E402


def bit_width(exp_width: int, frac_width: int) -> int:
    """`FloatFormat.bitWidth`: 1 + expWidth + fracWidth (Format/Definition.lean)."""
    return 1 + exp_width + frac_width


# (label, expWidth, fracWidth, kernel class the chapter's #eval reports for addition)
FORMATS = [
    ("binary16", 5, 10, "nativeWord"),
    ("binary32", 8, 23, "fixedFormat"),
    ("binary64", 11, 52, "fixedFormat"),
    ("binary128", 15, 112, "fixedLimbs"),
    ("BinaryLimbs 19 236", 19, 236, "wideLimbs"),
    ("Binary 19 236", 19, 236, "generic"),
]

RUNGS = {
    "exhaustiveTable": dict(
        title="exhaustive encoded-value table",
        condition="bitWidth ≤ 8, byte storage; competes with the word kernel on estimated cost",
        source="Configured/Storage/Core.lean (StoragePlan.byte), Configured/Plan/Automatic.lean",
        colour=fs.ORANGE),
    "fixedFormat": dict(
        title="fixed-format word kernel",
        condition="IsBinary32 ∨ IsBinary64: the fields must match the binary32 or binary64 layout",
        source="Descriptor/Plan/Routes.lean (isFixedFormat), Format/Catalog.lean",
        colour=fs.SKY),
    "nativeWord": dict(
        title="machine-word kernel",
        condition="isIEEE ∧ bitWidth ≤ 64 (StorageEligible); each operation adds a capacity contract",
        source="ExecFloat/Backends/Word/Small/Core/Runtime.lean",
        colour=fs.SKY),
    "fixedLimbs": dict(
        title="fixed-limb kernel, two UInt64 limbs",
        condition="isIEEE ∧ 64 < fracWidth ∧ bitWidth ≤ 128",
        source="ExecFloat/Backends/FixedLimb/Pair/Core/Runtime.lean (NativePair.Eligible)",
        colour=fs.GREEN),
    "wideLimbs": dict(
        title="wide-limb kernel, an array of 32-bit limbs",
        condition="isIEEE ∧ 128 < bitWidth ∧ expWidth ≤ 32\n"
                  "requires limb storage (StoragePlan.limbs, used by ExecFloat.BinaryLimbs)\n"
                  "add, sub, mul, and fma; div and sqrt keep the baseline\n"
                  "normal fast paths; declined calls use the exact baseline",
        source="ExecFloat/Backends/WideLimb/Core/Runtime.lean, Configured/Plan/WideLimbCandidates.lean",
        colour=fs.PURPLE),
    "generic": dict(
        title="exact baseline",
        condition="works for every descriptor and storage type; always available as a fallback",
        source="Configured/Plan/Candidates.lean (addCandidates.baseline)",
        colour=fs.LINE),
}

# Layout in axis units; the figure is 9 inches wide.
WIDTH_UNITS = 18.0
LADDER_X0, LADDER_X1 = 0.25, 11.9
FORMAT_X0, FORMAT_X1 = 13.75, 17.85
RUNG_H = 1.42
GROUP_HEAD = 0.5
GAP = 0.28


def rounded(ax, x, y, w, h, *, facecolor, edgecolor=fs.INK, lw=1.0, ls="-", alpha=1.0):
    patch = FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0,rounding_size=0.12",
                           facecolor=facecolor, edgecolor=edgecolor, linewidth=lw, linestyle=ls,
                           alpha=alpha)
    ax.add_patch(patch)
    return patch


def tint(colour: str) -> tuple:
    r, g, b = (int(colour[i:i + 2], 16) / 255 for i in (1, 3, 5))
    k = 0.78  # blend towards white so 9 pt text stays legible on top
    return (r + (1 - r) * k, g + (1 - g) * k, b + (1 - b) * k)


def draw_rung(ax, key: str, y: float, h: float, x0=LADDER_X0, x1=LADDER_X1) -> None:
    rung = RUNGS[key]
    rounded(ax, x0, y, x1 - x0, h, facecolor=tint(rung["colour"]))
    pad = 0.22
    ax.text(x0 + pad, y + h - 0.18, rung["title"], ha="left", va="top", fontsize=10,
            fontweight="bold", color=fs.INK)
    ax.text(x1 - pad, y + h - 0.18, f"KernelClass.{key}", ha="right", va="top", fontsize=9,
            color=fs.MUTED, family="DejaVu Sans Mono")
    ax.text(x0 + pad, y + h - 0.62, rung["condition"], ha="left", va="top", fontsize=9.3,
            color=fs.INK, linespacing=1.25)
    ax.text(x0 + pad, y + 0.1, rung["source"], ha="left", va="bottom", fontsize=8.3,
            color=fs.MUTED)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    # Vertical plan, from the top: header, then the rungs.
    order = ["exhaustiveTable", "word", "fixedLimbs", "wideLimbs", "generic"]
    heights = {"exhaustiveTable": RUNG_H, "fixedFormat": RUNG_H, "nativeWord": RUNG_H,
               "fixedLimbs": RUNG_H, "wideLimbs": RUNG_H + 0.94, "generic": RUNG_H}
    word_h = GROUP_HEAD + 2 * RUNG_H + 3 * 0.14
    header_h = 1.15
    total = header_h + sum(word_h if k == "word" else heights[k] for k in order) \
        + GAP * (len(order) - 1) + 0.25
    fig = plt.figure(figsize=(fs.WIDTH, total * fs.WIDTH / WIDTH_UNITS))
    ax = fs.diagram_axes(fig, (0, WIDTH_UNITS), (0, total))

    ax.text(LADDER_X0, total - 0.1,
            "The default addition kernel depends on the format and how values are stored.",
            ha="left", va="top", fontsize=9.5, color=fs.INK)
    ax.text(LADDER_X0, total - 0.5,
            "Arrows show selectedCandidate for public ExecFloat types; every candidate carries a proof.",
            ha="left", va="top", fontsize=9.5, color=fs.INK)

    centres: dict[str, float] = {}
    y = total - header_h
    for key in order:
        if key == "word":
            y -= word_h
            rounded(ax, LADDER_X0, y, LADDER_X1 - LADDER_X0, word_h, facecolor="white",
                    edgecolor=fs.INK, lw=1.0, ls=(0, (4, 3)))
            ax.text(LADDER_X0 + 0.22, y + word_h - 0.12,
                    "word kernels, bitWidth ≤ 64: the encoding fits one UInt64",
                    ha="left", va="top", fontsize=9.5, color=fs.INK, fontweight="bold")
            inner_x0, inner_x1 = LADDER_X0 + 0.16, LADDER_X1 - 0.16
            yy = y + word_h - GROUP_HEAD - 0.14
            for sub in ("nativeWord", "fixedFormat"):
                yy -= RUNG_H
                draw_rung(ax, sub, yy, RUNG_H, x0=inner_x0, x1=inner_x1)
                centres[sub] = yy + RUNG_H / 2
                yy -= 0.14
        else:
            h = heights[key]
            y -= h
            draw_rung(ax, key, y, h)
            centres[key] = y + h / 2
        y -= GAP

    # Formats on the right, one box each, in order of width from the top.
    box_h = 1.32
    span_top = total - header_h - 0.05
    span_bottom = 0.3
    n = len(FORMATS)
    step = (span_top - span_bottom - box_h) / (n - 1)
    for i, (label, e, f, kind) in enumerate(FORMATS):
        yb = span_top - box_h - i * step
        rounded(ax, FORMAT_X0, yb, FORMAT_X1 - FORMAT_X0, box_h, facecolor=fs.PAPER_2)
        width = bit_width(e, f)
        ax.text(FORMAT_X0 + 0.18, yb + box_h - 0.16, label, ha="left", va="top", fontsize=9.5,
                fontweight="bold", color=fs.INK)
        storage = ".limbs" if label.startswith("BinaryLimbs") else ".wide"
        detail = f"{storage} storage, {width} bits" if width > 128 else f"1 + {e} + {f} = {width} bits"
        ax.text(FORMAT_X0 + 0.18, yb + box_h / 2 + 0.02, detail,
                ha="left", va="center", fontsize=9, color=fs.INK)
        yc = yb + box_h / 2
        target = centres[kind]
        # Arrows to the same rung fan out a little so their heads do not sit on one point.
        offset = {"fixedFormat": {"binary32": 0.22, "binary64": -0.22}}.get(kind, {}).get(label, 0.0)
        fs.arrow(ax, (FORMAT_X0, yc), (LADDER_X1, target + offset), color=fs.INK, linewidth=1.1,
                 shrink=3.0)
        ax.text(FORMAT_X0 + 0.18, yb + 0.14, f"add selects {kind}", ha="left", va="bottom",
                fontsize=8.8, color=fs.MUTED, family="DejaVu Sans Mono")

    out = fs.save(fig, "ch09-backend-ladder.png", args.out)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
