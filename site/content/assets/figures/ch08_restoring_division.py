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


# Layout in axis units; the figure is 9 inches wide, so one unit is 9 / (X_END + 0.2) inches.
X_STEP, X_RIN, X_LINE0, X_LINE1, X_TEXT, X_BIT, X_Q, X_ROUT, X_INV, X_END = (
    0.2, 1.7, 3.4, 6.4, 7.7, 11.0, 11.9, 15.2, 16.3, 20.1)
ROW_H = 1.45
TOP_PAD = 1.55
BOTTOM_PAD = 0.35


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    fs.setup()
    rows = trace()
    height_units = TOP_PAD + ROW_H * len(rows) + BOTTOM_PAD
    width_units = X_END + 0.2
    fig = plt.figure(figsize=(fs.WIDTH, height_units * fs.WIDTH / width_units))
    ax = fs.diagram_axes(fig, (0, width_units), (0, height_units))

    top = height_units - 0.15
    ax.text(X_STEP, top, f"{DIVIDEND} / {DIVISOR}: start from {DIVIDEND} = "
            f"{DIVIDEND // DIVISOR} × {DIVISOR} + {DIVIDEND % DIVISOR}, then run the step "
            f"{STEPS} times. Each step doubles r, compares it with d = {DIVISOR}, "
            "and appends one quotient bit.",
            ha="left", va="top", fontsize=9.5, color=fs.INK)

    # Column headings.
    y_head = height_units - TOP_PAD + 0.12
    for x, label, ha in (
        (X_STEP, "step", "left"),
        ((X_RIN + X_LINE0) / 2 - 0.35, "r in", "center"),
        ((X_LINE0 + X_LINE1) / 2, f"2r against d = {DIVISOR}", "center"),
        (X_TEXT, "decision (2r < d?)", "left"),
        (X_BIT + 0.4, "bit", "center"),
        (X_Q, "quotient q\n(new bit boxed)", "left"),
        ((X_ROUT + X_INV) / 2, "r out", "center"),
        (X_INV, f"q × {DIVISOR} + r = {DIVIDEND} × 2ⁿ", "left"),
    ):
        ax.text(x, y_head, label, ha=ha, va="bottom", fontsize=9, color=fs.MUTED,
                linespacing=1.2)
    ax.plot([X_STEP, X_END], [y_head - 0.05, y_head - 0.05], color=fs.LINE, lw=0.8)

    scale = (X_LINE1 - X_LINE0) / (2 * DIVISOR)  # the mini number line runs from 0 to 2d
    for i, row in enumerate(rows):
        y0 = height_units - TOP_PAD - ROW_H * (i + 1)
        yc = y0 + ROW_H / 2
        if i % 2 == 1:
            ax.add_patch(Rectangle((X_STEP - 0.1, y0), X_END - X_STEP + 0.2, ROW_H,
                                   facecolor=fs.PAPER_2, edgecolor="none", zorder=0))
        label = "start" if row["step"] == 0 else f"step {row['step']}"
        ax.text(X_STEP, yc, label, ha="left", va="center", fontsize=10, color=fs.INK)

        if row["step"] > 0:
            ax.text((X_RIN + X_LINE0) / 2 - 0.35, yc, str(row["r_in"]), ha="center",
                    va="center", fontsize=10.5, color=fs.INK)
            # Mini number line: 0 to 2d, the divisor as a dashed marker, 2r as a bar.
            base = yc - 0.32
            ax.plot([X_LINE0, X_LINE1], [base, base], color=fs.INK, lw=0.8)
            for value in range(0, 2 * DIVISOR + 1):
                x = X_LINE0 + value * scale
                ax.plot([x, x], [base - 0.05, base + 0.05], color=fs.INK, lw=0.6)
            for value in (0, DIVISOR, 2 * DIVISOR):
                ax.text(X_LINE0 + value * scale, base - 0.1, str(value), ha="center", va="top",
                        fontsize=8, color=fs.MUTED)
            xd = X_LINE0 + DIVISOR * scale
            ax.plot([xd, xd], [base, base + 0.62], color=fs.INK, lw=0.9, ls="--")
            ax.text(xd + 0.05, base + 0.63, "d", ha="left", va="bottom", fontsize=8.5,
                    color=fs.INK)
            bar_y, bar_h = base + 0.12, 0.34
            doubled = row["doubled"]
            if row["bit"] == 0:
                ax.add_patch(Rectangle((X_LINE0, bar_y), doubled * scale, bar_h,
                                       facecolor=fs.ORANGE, edgecolor=fs.INK, lw=0.8))
                decision = f"{doubled} < {DIVISOR}: keep\nr = {doubled}"
            else:
                # The part below d is subtracted (hatched); what is left is the new remainder.
                ax.add_patch(Rectangle((X_LINE0, bar_y), DIVISOR * scale, bar_h,
                                       facecolor="white", edgecolor=fs.BLUE, lw=0.8,
                                       hatch="////"))
                ax.add_patch(Rectangle((X_LINE0 + DIVISOR * scale, bar_y),
                                       (doubled - DIVISOR) * scale, bar_h,
                                       facecolor=fs.BLUE, edgecolor=fs.INK, lw=0.8))
                decision = (f"{doubled} ≥ {DIVISOR}: subtract d\n"
                            f"r = {doubled} - {DIVISOR} = {row['r_out']}")
            ax.text(X_LINE1 + 0.15, bar_y + bar_h / 2, f"2r = {doubled}",
                    ha="left", va="center", fontsize=8.5, color=fs.INK)
            ax.text(X_TEXT, yc, decision, ha="left", va="center", fontsize=9, color=fs.INK,
                    linespacing=1.35)
            bit_colour = fs.ORANGE if row["bit"] == 0 else fs.BLUE
            ax.text(X_BIT + 0.4, yc, str(row["bit"]), ha="center", va="center", fontsize=12,
                    color=bit_colour, fontweight="bold")
        else:
            ax.text(X_TEXT, yc, f"initial state: {DIVIDEND} = "
                    f"{row['q']} × {DIVISOR} + {row['r_out']}",
                    ha="left", va="center", fontsize=9, color=fs.MUTED)

        # The quotient bits, most significant first, the newest boxed and coloured.
        bits = format(row["q"], "b")
        cell = 0.42
        for j, digit in enumerate(bits):
            x = X_Q + j * cell
            newest = row["step"] > 0 and j == len(bits) - 1
            if newest:
                ax.add_patch(Rectangle((x, yc - 0.3), cell, 0.6,
                                       facecolor=(fs.ORANGE if row["bit"] == 0 else fs.BLUE),
                                       edgecolor=fs.INK, lw=0.9, alpha=0.9))
            ax.text(x + cell / 2, yc, digit, ha="center", va="center", fontsize=11,
                    color=fs.INK, fontweight="bold" if newest else "normal",
                    family="DejaVu Sans Mono")
        ax.text(X_Q + len(bits) * cell + 0.15, yc, f"= {row['q']}", ha="left", va="center",
                fontsize=10, color=fs.INK)

        ax.text((X_ROUT + X_INV) / 2, yc, str(row["r_out"]), ha="center", va="center",
                fontsize=10.5, color=fs.INK)
        total = row["q"] * DIVISOR + row["r_out"]
        ax.text(X_INV, yc, f"{row['q']} × {DIVISOR} + {row['r_out']} = {total} = "
                f"{DIVIDEND} × 2{superscript(row['step'])}",
                ha="left", va="center", fontsize=9.5, color=fs.INK)

    out = fs.save(fig, "ch08-restoring-division.png", args.out)
    print(f"wrote {out}")


SUPERSCRIPTS = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")


def superscript(n: int) -> str:
    return str(n).translate(SUPERSCRIPTS)


if __name__ == "__main__":
    main()
