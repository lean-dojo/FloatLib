#!/usr/bin/env python3
"""Draw content/assets/ch03-binary32-accumulation.png: ten thousand binary32 additions of 0.1.

The history chapter (site/content/chapters/03-a-short-history-of-floating-point.md, the Vancouver section) adds the
binary32 value of 0.1 to itself ten thousand times with `ExecFloat.Binary.addWithStatus`, once
rounding to nearest even and once toward zero, and prints 999.90289306640625 and
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
    "nearestEven": dict(label="round to nearest even", color=fs.BLUE, linestyle="-"),
    "towardZero": dict(label="round toward zero (truncation)", color=fs.ORANGE,
                       linestyle="--"),
}


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


def draw(out: Path | None) -> Path:
    totals = {mode: accumulate(mode) for mode in SERIES}
    for mode, expected in EXPECTED.items():
        if totals[mode][-1] != expected:
            raise SystemExit(f"{mode}: computed {totals[mode][-1]} but the history chapter prints {expected}")

    fs.setup()
    fig, ax = fs.figure(4.6)
    ks = list(range(STEPS + 1))
    errors = {mode: [float(t - Fraction(k, 10)) for k, t in enumerate(totals[mode])]
              for mode in SERIES}

    crossings = first_crossings(totals["nearestEven"])
    top = 0.056
    for j in LABELLED_BINADES:
        k = crossings[j]
        ax.axvline(k, color=fs.MUTED, linestyle=":", linewidth=1.0, zorder=1)
        ax.text(k, top, str(2 ** j), ha="center", va="bottom", fontsize=9, color=fs.MUTED)
    ax.axhline(0, color=fs.INK, linewidth=0.8, zorder=1)

    for mode, style in SERIES.items():
        ax.plot(ks, errors[mode], color=style["color"], linestyle=style["linestyle"],
                linewidth=1.8, zorder=3)

    # Direct labels beside the lines where they have separated, and the exact final totals
    # (the chapter's printed decimals), each placed in the clear band between the two lines
    # or below the lower one.
    # Both lines fall to the right, so a label above a line extends rightwards and a label
    # below a line extends leftwards, each into the side the line falls away from.
    k_ne, k_tz = 7000, 8000
    ax.annotate(SERIES["nearestEven"]["label"], (k_ne, errors["nearestEven"][k_ne]),
                xytext=(8, 2), textcoords="offset points", ha="left", va="bottom",
                fontsize=9, color=fs.INK)
    ax.annotate(SERIES["towardZero"]["label"], (k_tz, errors["towardZero"][k_tz]),
                xytext=(-8, -2), textcoords="offset points", ha="right", va="top",
                fontsize=9, color=fs.INK,
                bbox=dict(facecolor="white", edgecolor="none", pad=0.2))
    ax.annotate(f"total {EXPECTED_TEXT['nearestEven']}", (STEPS, errors["nearestEven"][-1]),
                xytext=(-8, -7), textcoords="offset points", ha="right", va="top",
                fontsize=9, color=fs.INK)
    ax.annotate(f"total {EXPECTED_TEXT['towardZero']}", (STEPS, errors["towardZero"][-1]),
                xytext=(-8, -7), textcoords="offset points", ha="right", va="top",
                fontsize=9, color=fs.INK)

    ax.set_xlim(0, STEPS)
    ax.set_ylim(-0.225, 0.075)
    ax.set_xlabel("additions performed, k")
    ax.set_ylabel("running total minus k/10")
    ax.grid(False, axis="x")

    handles = [Line2D([], [], color=s["color"], linestyle=s["linestyle"], linewidth=1.8,
                      label=s["label"]) for s in SERIES.values()]
    handles.append(Line2D([], [], color=fs.MUTED, linestyle=":", linewidth=1.0,
                          label="the running total reaches a power of two"))
    ax.legend(handles=handles, loc="upper right", frameon=False)
    return fs.save(fig, OUT_NAME, out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    print(f"wrote {draw(args.out)}")


if __name__ == "__main__":
    main()
