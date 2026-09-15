#!/usr/bin/env python3
"""Draw content/assets/ch19-layers.png: the three layers of FloatLib/ with their module counts.

The figure in chapter 01 lays out the library the way "The shape of the tree" describes it:
Numerics/ at the bottom, Kernels/ above it, Floats/ on top with Formats/, ExecFloat/ and its
Backends/, and Interval/ inside, with the dependency arrow pointing one way, Numerics to Kernels
to Floats, and Examples/ beside the layers.

Every count is computed when the script runs, from the repository's own file list:

    cd <repository root> && git ls-files --cached --others --exclude-standard 'FloatLib/**/*.lean'

grouped by directory prefix (a module is counted under every directory on its path, so the
Floats/ total includes Formats/ and ExecFloat/, and ExecFloat/ includes Backends/). In git's
pathspec syntax that pattern requires at least one directory between FloatLib/ and the file,
so the four layer roots that sit directly in FloatLib/ (Numerics.lean, Kernels.lean,
Floats.lean, Examples.lean) are listed separately with git ls-files 'FloatLib/*.lean',
filtered to depth one because git's `*` also crosses slashes. Deleted paths are excluded and
untracked source files are included, so an unstaged namespace rename has the same counts.
Runtime and Proof pairs are the directories in the same listing holding both a Runtime.lean
and a Proof.lean. The script prints the current counts when it regenerates the figure.

The description of each directory is the chapter's; the layer rule the arrows carry is the one
tests/checks/architecture.sh enforces, quoted from the chapter.

Every string drawn is checked for em and en dashes before saving (figstyle.save does it).

Run from anywhere: python3 ch19_layers.py [--out PNG]
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
from matplotlib.patches import FancyBboxPatch  # noqa: E402

OUT_NAME = "ch19-layers.png"

NUMERICS = fs.BLUE
KERNELS = fs.ORANGE
FLOATS = fs.GREEN
BESIDE = fs.PURPLE


def tint(hex_colour: str, amount: float) -> str:
    """Mix a colour with white; amount 0 is white, 1 is the colour itself."""
    r, g, b = (int(hex_colour[i:i + 2], 16) for i in (1, 3, 5))
    mix = lambda c: int(round(255 + (c - 255) * amount))  # noqa: E731
    return f"#{mix(r):02x}{mix(g):02x}{mix(b):02x}"


def titled_box(ax, x, y, w, h, title, body, *, edgecolor=fs.INK, facecolor=fs.PAPER_2,
               linestyle="-", linewidth=1.1, title_size=10, body_size=9.0, pad=0.12,
               title_offset=0.25):
    """A rounded box with a bold title at the top left and a left-aligned body under it."""
    patch = FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0,rounding_size=0.08",
                           facecolor=facecolor, edgecolor=edgecolor, linewidth=linewidth,
                           linestyle=linestyle)
    ax.add_patch(patch)
    ax.text(x + pad, y + h - pad, title, ha="left", va="top", fontsize=title_size,
            fontweight="bold", color=fs.INK)
    if body:
        ax.text(x + pad, y + h - pad - title_offset, body, ha="left", va="top",
                fontsize=body_size, color=fs.INK, linespacing=1.32)
    return patch


def git_ls(pattern: str) -> list[str]:
    result = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard",
                             "--", pattern], cwd=fs.REPO, check=True,
                            capture_output=True, text=True)
    return sorted({line for line in result.stdout.splitlines()
                   if line and (fs.REPO / line).is_file()})


def count_tree() -> dict:
    """Module counts by directory prefix, Runtime/Proof pairs by layer, and the layer roots."""
    modules = git_ls("FloatLib/**/*.lean")
    by_prefix: Counter[str] = Counter()
    for path in modules:
        parts = path.split("/")
        for depth in range(2, len(parts)):          # FloatLib/A, FloatLib/A/B, ...
            by_prefix["/".join(parts[:depth])] += 1
    direct: Counter[str] = Counter()               # files directly inside a directory
    for path in modules:
        direct[path.rsplit("/", 1)[0]] += 1
    pair_dirs = Counter()
    for path in modules:
        if path.endswith("/Runtime.lean") or path.endswith("/Proof.lean"):
            pair_dirs[path.rsplit("/", 1)[0]] += 1
    pairs_by_layer: Counter[str] = Counter()
    for directory, n in pair_dirs.items():
        if n == 2:
            pairs_by_layer[directory.split("/")[1]] += 1
    roots = [p for p in git_ls("FloatLib/*.lean") if p.count("/") == 1]
    return {"modules": modules, "by_prefix": by_prefix, "direct": direct,
            "pairs": pairs_by_layer, "roots": roots}


def draw(out: Path | None) -> Path:
    tree = count_tree()
    n = tree["by_prefix"]
    direct = tree["direct"]
    pairs = tree["pairs"]
    total = len(tree["modules"])
    roots = tree["roots"]

    def sub(prefix: str, names: list[str]) -> str:
        """'Name 12, Other 7' for the given children of prefix, in the given order."""
        return ", ".join(f"{name} {n[prefix + '/' + name]}" for name in names)

    fs.setup()
    height = 7.15
    fig, default_axes = fs.figure(height)
    default_axes.remove()
    ax = fs.diagram_axes(fig, (0, fs.WIDTH), (0, height))

    top = height - 0.15
    ax.text(fs.WIDTH / 2, top, "The layers of FloatLib/", ha="center", va="top", fontsize=11,
            fontweight="bold")

    lx, lw = 0.25, 6.35            # the layer column
    bx, bw = 6.75, 2.05            # the column beside the layers

    # Floats, the top layer, with its parts inside.
    fh = 3.25
    fy = top - 0.4 - fh
    F = "FloatLib/Floats"
    titled_box(ax, lx, fy, lw, fh,
               f"Floats/   {n[F]} modules, {pairs['Floats']} Runtime and Proof pairs",
               "the formats and the universal carrier ExecFloat; connects operations to kernels",
               edgecolor=FLOATS, facecolor=tint(FLOATS, 0.08))
    inner_top = fy + fh - 0.62
    inner_h = 2.3
    # Formats/ on the left, with Interval/ in a small box under it.
    fmx, fmw = lx + 0.15, 3.0
    ivh = 0.36
    fmh = inner_h - ivh - 0.1
    fmy = inner_top - fmh
    family_rows = [
        ["BinaryInterchange"],
        ["DecimalInterchange", "Posit"],
        ["Flocq", "FixedPoint", "OCP"],
        ["P3109", "Codebook", "Logarithmic"],
        ["Block", "IEEE754", "FiniteOnly"],
    ]
    fam_lines = [", ".join(f"{name} {n[F + '/Formats/' + name]}" for name in row)
                 for row in family_rows]
    titled_box(ax, fmx, fmy, fmw, fmh, f"Formats/   {n[F + '/Formats']} modules",
               "encodings and their meaning,\none directory per family:\n"
               + "\n".join(fam_lines)
               + f"\nand {direct[F + '/Formats']} family roots directly in Formats/",
               edgecolor=FLOATS, facecolor="white", title_size=9.6)
    titled_box(ax, fmx, fmy - 0.1 - ivh, fmw, ivh, f"Interval/   {n[F + '/Interval']} modules",
               "", edgecolor=FLOATS, facecolor="white", title_size=9.6)
    # ExecFloat/ on the right, with Backends/ nested inside it.
    exx, exw, exh = fmx + fmw + 0.15, lw - 0.45 - fmw, inner_h
    exy = inner_top - exh
    E = F + "/ExecFloat"
    titled_box(ax, exx, exy, exw, exh, f"ExecFloat/   {n[E]} modules",
               "the carrier and its backends:\nCarrier, Core, Dispatch, Spec,\nProof, Selection, "
               "Conversion, Info",
               edgecolor=FLOATS, facecolor="white", title_size=9.6)
    bkh = 1.22
    bky = exy + 0.12
    backends = ["TinyTable", "Word", "FixedLimb", "WideLimb", "Generic", "Dispatch", "Selection"]
    bk_lines = [", ".join(f"{name} {n[E + '/Backends/' + name]}" for name in backends[i:i + 3])
                for i in range(0, len(backends), 3)]
    titled_box(ax, exx + 0.12, bky, exw - 0.24, bkh,
               f"Backends/   {n[E + '/Backends']} modules",
               "one directory per kernel class:\n" + "\n".join(bk_lines),
               edgecolor=FLOATS, facecolor=tint(FLOATS, 0.08), title_size=9.4)
    # The three roots along the bottom of the Floats box.
    ax.text(lx + 0.15, fy + 0.1,
            "and the three roots Formats.lean, ExecFloat.lean, and Interval.lean directly in Floats/",
            ha="left", va="bottom", fontsize=9.0, color=fs.INK)

    # Kernels, the middle layer.
    kh = 1.0
    ky = fy - 0.45 - kh
    K = "FloatLib/Kernels"
    titled_box(ax, lx, ky, lw, kh,
               f"Kernels/   {n[K]} modules, {pairs['Kernels']} Runtime and Proof pairs",
               "integer and fixed-word algorithms with refinement proofs:\n"
               f"{sub(K, ['FixedWord', 'LimbArray'])}, and the root FixedWord.lean; "
               "the declarations sit in the\nFloatLib.Numerics namespace",
               edgecolor=KERNELS, facecolor=tint(KERNELS, 0.10))

    # Numerics, the bottom layer.
    nh = 1.25
    ny = ky - 0.45 - nh
    N = "FloatLib/Numerics"
    titled_box(ax, lx, ny, lw, nh,
               f"Numerics/   {n[N]} modules, {pairs['Numerics']} Runtime and Proof pairs",
               "exact values and contracts without choosing an encoding:\n"
               f"{sub(N, ['Core', 'Exact', 'Operation', 'Quantization', 'Representations', 'Capabilities'])},\n"
               f"{sub(N, ['Enclosure', 'Automation', 'IEEEStatus', 'Order', 'ShiftRightJam'])},\n"
               f"and {direct[N]} files directly in Numerics/",
               edgecolor=NUMERICS, facecolor=tint(NUMERICS, 0.10))

    # The dependency arrow points one way, Numerics to Kernels to Floats.
    ax_x = lx + 0.9
    fs.arrow(ax, (ax_x, ky + kh), (ax_x, fy), color=fs.INK, linewidth=1.4)
    fs.arrow(ax, (ax_x, ny + nh), (ax_x, ky), color=fs.INK, linewidth=1.4)
    ax.text(ax_x + 0.15, (ky + kh + fy) / 2, "Floats may import Kernels and Numerics; "
            "a Kernels module may not import Floats", ha="left", va="center", fontsize=9.0)
    ax.text(ax_x + 0.15, (ny + nh + ky) / 2, "a Numerics module may not import Kernels or "
            "Floats (tests/checks/architecture.sh rejects both)", ha="left", va="center",
            fontsize=9.0)

    # Beside the layers.
    X = "FloatLib/Examples"
    eh = 1.25
    ey = fy + fh - eh
    titled_box(ax, bx, ey, bw, eh, f"Examples/   {n[X]} modules",
               "teaching modules that\nimport the library; no\nproduction module may\nimport them",
               edgecolor=BESIDE, facecolor=tint(BESIDE, 0.10), title_size=9.6, linestyle="--")
    rh = 1.35
    ry = ey - 0.3 - rh
    layer_order = ["Numerics.lean", "Kernels.lean", "Floats.lean", "Examples.lean"]
    names = sorted((Path(r).name for r in roots),
                   key=lambda name: layer_order.index(name) if name in layer_order else 99)
    root_lines = [", ".join(names[i:i + 2]) for i in range(0, len(names), 2)]
    titled_box(ax, bx, ry, bw, rh, f"{len(roots)} layer roots",
               ",\n".join(root_lines) + "\nsit directly in FloatLib/\nand are counted apart from\n"
               "the nested modules",
               edgecolor=fs.INK, facecolor=fs.PAPER_2, title_size=9.6)
    ax.text(bx, ry - 0.25, "tests/ and benchmarks/\nare separate Lake\nworkspaces that import\n"
            "the library.\n\nsite/ is the checked\nwebsite and guide.",
            ha="left", va="top", fontsize=9.0, color=fs.MUTED, linespacing=1.32)

    target = fs.save(fig, OUT_NAME, out)
    print(f"counted {total} modules: " + ", ".join(
        f"{layer} {n['FloatLib/' + layer]}" for layer in ("Floats", "Numerics", "Kernels",
                                                          "Examples"))
          + f"; pairs {dict(pairs)}; roots {', '.join(names)}")
    return target


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None, help="output PNG (default: assets)")
    args = parser.parse_args()
    target = draw(args.out)
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
