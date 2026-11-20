#!/usr/bin/env python3
"""Draw content/assets/ch03-binary32-accumulation.png: ten thousand binary32 additions of 0.1.

The history chapter (site/content/chapters/03-a-short-history-of-floating-point.md, the Vancouver section) adds the
binary32 value of 0.1 to itself ten thousand times with `ExecFloat.Binary.add` and
`(status := true)`, once rounding to nearest even and once toward zero, and prints 999.90289306640625 and
999.80487060546875. This script recomputes both sequences exactly and plots the running total
minus k/10 against the number of additions k, with the binade boundaries the total crosses marked.

Every number is either stated in the chapter or is arithmetic on binary32's parameters:

* the stored tenth is 13421773 / 2^27, the chapter's `toRat?` result for `(0.1 : Binary32)`;
* binary32 has 23 fraction bits and an implicit leading bit, so 24 bits of precision
  (FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean, `binary32`, fracWidth := 23);
* rounding is performed on exact rationals (fractions.Fraction), to the nearest multiple of the
  binade's unit in the last place with ties to even, or toward zero by discarding the remainder.
  No exponent range check is needed: every total lies between 0 and 1000.

The script refuses to draw unless both final totals equal the values printed in the chapter, so
the figure and the Lean output cannot drift apart. The representation error of the tenth alone
(k copies of 13421773 / 2^27 minus k/10) reaches only about 1.5e-5 at k = 10000, the chapter's
"1000 plus about 1.5 x 10^-5", and is not drawn: everything visible is rounding of the additions.

Run from anywhere: python3 ch03_binary32_accumulation.py [--out PATH]
Also writes a <stem>-mobile.png companion beside the overview.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

from matplotlib.lines import Line2D  # noqa: E402

OUT_NAME = "ch03-binary32-accumulation.png"

STEP = Fraction(13421773, 2 ** 27)        # (0.1 : Binary32), from the chapter's #eval
STEPS = 10000
PRECISION = 24                            # 23 fraction bits + implicit leading bit
EXPECTED_TEXT = {                         # the chapter's two #eval results, as printed
    "nearestEven": "999.90289306640625",
    "towardZero": "999.80487060546875",
}
EXPECTED = {mode: Fraction(text) for mode, text in EXPECTED_TEXT.items()}
LABELLED_BINADES = (6, 7, 8, 9)           # the total reaching 64, 128, 256, 512

SERIES = {
    "nearestEven": dict(label="nearest even", color=fs.ROLE["main"], linestyle="-"),
    "towardZero": dict(label="toward zero", color=fs.ROLE["second"], linestyle="--"),
}
BINADE_LABEL = "total reaches a power of two"


def binade_exponent(x: Fraction) -> int:
    """The e with 2^e <= x < 2^(e+1), for x > 0."""
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Fraction(2) ** e > x:
        e -= 1
    if Fraction(2) ** (e + 1) <= x:
        e += 1
    return e


def round_binary32(x: Fraction, mode: str) -> Fraction:
    """Round a positive rational to binary32 precision in the given mode."""
    if x == 0:
        return x
    ulp = Fraction(2) ** (binade_exponent(x) - (PRECISION - 1))
    q, r = divmod(x, ulp)
    if mode == "towardZero" or 2 * r < ulp:
        return q * ulp
    if 2 * r > ulp:
        return (q + 1) * ulp
    return (q + q % 2) * ulp              # a tie: to even


def accumulate(mode: str) -> list[Fraction]:
    totals = [Fraction(0)]
    for _ in range(STEPS):
        totals.append(round_binary32(totals[-1] + STEP, mode))
    return totals


def first_crossings(totals: list[Fraction]) -> dict[int, int]:
    """For each binade exponent j, the first k at which the total is at least 2^j."""
    crossings: dict[int, int] = {}
    for k, total in enumerate(totals):
        if total > 0:
            j = binade_exponent(total)
            crossings.setdefault(j, k)
    return crossings


def draw_mobile(target: Path, ks: list[int], errors: dict[str, list[float]],
                crossings: dict[int, int]) -> Path:
    """Reuse the exact accumulation curves on a narrow canvas."""
    fig, ax = fs.plt.subplots(figsize=(fs.MOBILE_WIDTH, 4.6))
    fig.subplots_adjust(left=0.24, right=0.91, bottom=0.14, top=0.78)

    for index, j in enumerate(LABELLED_BINADES):
        k = crossings[j]
        ax.axvline(k, color=fs.MUTED, linestyle=":", linewidth=1.0, zorder=1)
        # The lines of 64 and 128 are closer than a label is wide, so the labels sit above the
        # lines, every second one a row higher.
        ax.annotate(str(2 ** j), (k, 1.0), xycoords=("data", "axes fraction"),
                    xytext=(0, 3 if index % 2 == 0 else 14), textcoords="offset points",
                    ha="center", va="bottom", fontsize=fs.SIZE_SMALL, color=fs.MUTED)
    ax.axhline(0, color=fs.INK, linewidth=0.8, zorder=1)
    labels = {mode: style["label"] for mode, style in SERIES.items()}
    for mode, style in SERIES.items():
        ax.plot(ks, errors[mode], color=style["color"], linestyle=style["linestyle"],
                linewidth=1.8, zorder=3, label=labels[mode])

    ax.set_xlim(0, STEPS)
    ax.set_ylim(-0.225, 0.075)
    ax.set_xticks([0, 2500, 5000, 7500, 10000],
                  labels=["0", "2,500", "5,000", "7,500", "10,000"])
    ax.set_yticks([-0.20, -0.15, -0.10, -0.05, 0, 0.05])
    ax.set_xlabel("additions performed, k")
    ax.set_ylabel("running total minus k/10")

    handles, _ = ax.get_legend_handles_labels()
    handles.append(Line2D([], [], color=fs.MUTED, linestyle=":", linewidth=fs.LW_REF,
                          label=BINADE_LABEL))
    fs.legend(fig, handles=handles, loc="upper left", bbox_to_anchor=(0.06, 0.99))
    return fs.save(fig, OUT_NAME, fs.mobile_path(target))


def draw(out: Path | None) -> Path:
    totals = {mode: accumulate(mode) for mode in SERIES}
    for mode, expected in EXPECTED.items():
        if totals[mode][-1] != expected:
            raise SystemExit(f"{mode}: computed {totals[mode][-1]} but the history chapter prints {expected}")

    fs.setup()
    fig, ax = fs.figure(4.2)
    ks = list(range(STEPS + 1))
    errors = {mode: [float(t - Fraction(k, 10)) for k, t in enumerate(totals[mode])]
              for mode in SERIES}

    crossings = first_crossings(totals["nearestEven"])
    top = 0.056
    for j in LABELLED_BINADES:
        k = crossings[j]
        ax.axvline(k, color=fs.MUTED, linestyle=":", linewidth=1.0, zorder=1)
        ax.annotate(str(2 ** j), (k, top), xytext=(3, 0), textcoords="offset points",
                    ha="left", va="bottom", fontsize=fs.SIZE_SMALL, color=fs.MUTED)
    ax.axhline(0, color=fs.INK, linewidth=0.8, zorder=1)

    for mode, style in SERIES.items():
        ax.plot(ks, errors[mode], color=style["color"], linestyle=style["linestyle"],
                linewidth=1.8, zorder=3)

    ax.set_xlim(0, STEPS)
    ax.set_ylim(-0.225, 0.075)
    ax.set_xlabel("additions performed, k")
    ax.set_ylabel("running total minus k/10")
    ticks = [0, 2000, 4000, 6000, 8000, 10000]
    ax.set_xticks(ticks, labels=[f"{tick:,}" for tick in ticks])

    handles = [Line2D([], [], color=s["color"], linestyle=s["linestyle"], linewidth=fs.LW_DATA,
                      label=s["label"]) for s in SERIES.values()]
    handles.append(Line2D([], [], color=fs.MUTED, linestyle=":", linewidth=fs.LW_REF,
                          label=BINADE_LABEL))
    fig.subplots_adjust(left=0.125, right=0.9, top=0.97, bottom=0.25)
    fs.legend(fig, handles=handles, loc="lower center", bbox_to_anchor=(0.5, 0.0), ncols=3)
    target = fs.save(fig, OUT_NAME, out)
    draw_mobile(target, ks, errors, crossings)
    return target


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    print(f"wrote {draw(args.out)}")


if __name__ == "__main__":
    main()
