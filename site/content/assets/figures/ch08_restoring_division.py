#!/usr/bin/env python3
"""Draw content/assets/ch08-restoring-division.png: restoring division one quotient bit at a time.

Chapter 13 quotes `natQuotientStep` from FloatLib/Kernels/FixedWord/Quotient/Proof.lean (checked
against the library by `rfl` in the chapter's own Lean block) and runs the word loop
`quotientSteps` from FloatLib/Kernels/FixedWord/Quotient/Runtime.lean on one example:

    #eval quotientSteps 3 4 { quotient := 1, remainder := 1 }
    -- { quotient := 21, remainder := 1 }

that is, start from 4 = 1 * 3 + 1 and generate four more quotient bits, reaching 4 * 2^4 = 64 =
21 * 3 + 1. This script re-runs the same step over Python integers (a transcription of the
natural-number step: double the remainder, compare with the divisor, append a 0 and keep, or
append a 1 and subtract) and stops with an error if the final state is not the one the chapter
prints. Every number drawn is a value of that recurrence: the remainder in, the doubled
remainder, the quotient bits, the remainder out, and the invariant `q * d + r = 4 * 2^n` from
`natQuotientSteps_spec`, checked on every row.

Run from anywhere: python3 ch08_restoring_division.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

# The chapter's example: dividend 4, divisor 3, initial state 4 = 1 * 3 + 1, four more bits.
DIVIDEND = 4
DIVISOR = 3
STEPS = 4
EXPECTED = (21, 1)  # the `-- { quotient := 21, remainder := 1 }` comment in chapter 13


def nat_quotient_step(den: int, quotient: int, remainder: int) -> tuple[int, int, int, int]:
    """One step of the restoring recurrence; returns (2r, bit, new quotient, new remainder)."""
    doubled = 2 * remainder
    if doubled < den:
        return doubled, 0, 2 * quotient, doubled
    return doubled, 1, 2 * quotient + 1, doubled - den


def trace() -> list[dict]:
    quotient, remainder = DIVIDEND // DIVISOR, DIVIDEND % DIVISOR
    rows = [dict(step=0, r_in=None, doubled=None, bit=None, q=quotient, r_out=remainder)]
    for n in range(1, STEPS + 1):
        doubled, bit, quotient_new, remainder_new = nat_quotient_step(DIVISOR, quotient, remainder)
        rows.append(dict(step=n, r_in=remainder, doubled=doubled, bit=bit, q=quotient_new,
                         r_out=remainder_new))
        quotient, remainder = quotient_new, remainder_new
    if (quotient, remainder) != EXPECTED:
        raise SystemExit(f"trace ended at {(quotient, remainder)}, chapter prints {EXPECTED}")
    for row in rows:
        # natQuotientSteps_spec: q' * d + r' = (q * d + r) * 2^n and r' < d.
        assert row["q"] * DIVISOR + row["r_out"] == DIVIDEND * 2 ** row["step"]
        assert row["r_out"] < DIVISOR
    return rows


def remainder_bar(ax, row: dict, *, y: float, x: float, width: float, height: float,
                  show_zero: bool = True):
    """A common 0..5 scale shows the doubled remainder and the divisor threshold."""
    unit = width / 5
    ax.plot([x, x + width], [y, y], color=fs.LINE, lw=0.8)
    ax.add_patch(Rectangle((x, y), row["doubled"] * unit, height,
                           fc=fs.SKY, ec=fs.BLUE, lw=0.8))
    if row["bit"]:
        ax.add_patch(Rectangle((x, y), DIVISOR * unit, height,
                               fc="white", ec=fs.MUTED, hatch="///", lw=0.6))
    ax.plot([x + DIVISOR * unit] * 2, [y - 0.05, y + height + 0.1],
            color=fs.VERMILION, lw=1)
    ax.text(x + DIVISOR * unit, y + height + 0.14, "3", fontsize=11.5,
            color=fs.VERMILION, ha="center", va="bottom")
    if show_zero:
        ax.text(x, y - 0.06, "0", fontsize=11, va="top")


def draw(mobile: bool, rows: list[dict]):
    fig = plt.figure(figsize=(3.8, 8.5) if mobile else (9, 4.9))
    fig.text(0.035, 0.98, "4 ÷ 3: grow the quotient one bit", fontsize=13.5, weight="bold", va="top")
    fig.text(0.035, 0.915 if mobile else 0.875,
             "Start: 4 = 1 × 3 + 1\nquotient q = 1, remainder r = 1" if mobile else
             "Start: 4 = 1 × 3 + 1, so quotient q = 1 and remainder r = 1.",
             fontsize=12, linespacing=1.5, va="top" if mobile else "baseline")
    if not mobile:
        fig.text(0.08, 0.76, "step", fontsize=11.5, color=fs.MUTED)
        fig.text(0.23, 0.76, "Double r; compare with 3", fontsize=11.5, color=fs.MUTED)
        fig.text(0.59, 0.76, "next bit", fontsize=11.5, color=fs.MUTED)
        fig.text(0.74, 0.76, "new q, r", fontsize=11.5, color=fs.MUTED)
    for i, row in enumerate(rows[1:]):
        if mobile:
            rect = [0.035, 0.64 - i * 0.168, 0.93, 0.148]
            ax = fig.add_axes(rect)
            ax.set(xlim=(0, 1), ylim=(0, 1))
            ax.axis("off")
            ax.add_patch(Rectangle((0, 0), 1, 1, fc=fs.PAPER_2, ec=fs.LINE, lw=0.6))
            ax.text(0.04, 0.84, f"Step {row['step']}: 2r = {row['doubled']}", fontsize=12, weight="bold")
            remainder_bar(ax, row, y=0.34, x=0.07, width=0.40, height=0.17)
            action = "keep 2" if row["bit"] == 0 else "subtract 3"
            ax.text(0.58, 0.55, action, fontsize=11.5)
            ax.text(0.58, 0.29, f"append {row['bit']}", fontsize=12, color=fs.BLUE)
            ax.text(0.04, 0.04, f"q = {row['q']} ({row['q']:b}₂),   r = {row['r_out']}", fontsize=11.5)
        else:
            ax = fig.add_axes([0.04, 0.59 - i * 0.13, 0.92, 0.13])
            ax.set(xlim=(0, 1), ylim=(0, 1))
            ax.axis("off")
            ax.text(0.06, 0.48, str(row['step']), fontsize=12, ha="center")
            remainder_bar(ax, row, y=0.32, x=0.21, width=0.24, height=0.22, show_zero=False)
            action = f"2r = {row['doubled']}; " + ("keep" if row["bit"] == 0 else "subtract 3")
            ax.text(0.20, 0.05, action, fontsize=11.5)
            ax.text(0.62, 0.48, str(row['bit']), fontsize=13, color=fs.BLUE)
            ax.text(0.76, 0.57, f"q = {row['q']} ({row['q']:b}₂)", fontsize=12)
            ax.text(0.76, 0.17, f"r = {row['r_out']}", fontsize=12)
    fig.text(0.035, 0.07 if mobile else 0.09,
             "Final: 21 × 3 + 1 = 64 = 4 × 2⁴", fontsize=12, weight="bold")
    fig.text(0.035, 0.022,
             "Hatching: subtract one divisor.\nEvery step keeps 0 ≤ r < 3." if mobile else
             "Hatching removes one divisor.  Every step keeps q × 3 + r = 4 × 2ⁿ and 0 ≤ r < 3.",
             fontsize=11.5, color=fs.MUTED, linespacing=1.5)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    rows = trace()
    fs.setup()
    out = args.out or fs.ASSETS / "ch08-restoring-division.png"
    for mobile in (False, True):
        target = out.with_name(out.stem + "-mobile.png") if mobile else out
        print(f"wrote {fs.save(draw(mobile, rows), target.name, target)}")


if __name__ == "__main__":
    main()
