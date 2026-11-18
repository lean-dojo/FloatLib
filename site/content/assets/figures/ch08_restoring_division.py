#!/usr/bin/env python3
"""Draw content/assets/ch08-restoring-division.png: restoring division one quotient bit at a time.

The example in Arithmetic performance divides 4 by 3. Starting with quotient 1 and
remainder 1, four steps of `quotientSteps` produce quotient 21 and remainder 1.
The Python recurrence below follows `natQuotientStep` in
FloatLib/Kernels/FixedWord/Quotient/Proof.lean. For each row it checks the invariant
from `natQuotientSteps_spec`, q * 3 + r = 4 * 2^n, and the bound on the remainder.

Run from anywhere: python3 ch08_restoring_division.py [--out PNG]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import Patch, Rectangle  # noqa: E402

# The chapter's example: dividend 4, divisor 3, initial state 4 = 1 * 3 + 1, four more bits.
DIVIDEND = 4
DIVISOR = 3
STEPS = 4
EXPECTED = (21, 1)  # quotient and remainder


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


BAR = dict(fc=fs.SKY, ec=fs.ROLE["main"], lw=fs.LW_AXIS)
REMOVED = dict(fc="white", ec=fs.MUTED, hatch="///", lw=fs.LW_GRID)


def remainder_bar(ax, row: dict, *, y: float, x: float, width: float, height: float):
    """A common 0..5 scale shows the doubled remainder and the divisor threshold."""
    unit = width / 5
    ax.plot([x, x + width], [y, y], color=fs.LINE, lw=fs.LW_AXIS)
    ax.add_patch(Rectangle((x, y), row["doubled"] * unit, height, **BAR))
    if row["bit"]:
        ax.add_patch(Rectangle((x, y), DIVISOR * unit, height, **REMOVED))
    ax.plot([x + DIVISOR * unit] * 2, [y - 0.05, y + height + 0.05],
            color=fs.ROLE["mark"], lw=fs.LW_REF + 0.4)


def draw(mobile: bool, rows: list[dict]):
    """One row per step: the doubled remainder against the divisor, the bit, the new q and r."""
    width = fs.MOBILE_WIDTH if mobile else fs.WIDTH
    pitch = 0.62 if mobile else 0.5
    height = 0.75 + pitch * len(rows) + 0.55
    fig = plt.figure(figsize=(width, height))
    ax = fs.diagram_axes(fig, (0, width), (0, height))
    # Column positions: step, bar (left edge and width), bit, quotient, remainder.
    step_x, bar_x, bar_w, bit_x, q_x, r_x = (
        (0.3, 0.75, 1.15, 2.2, 2.85, 3.55) if mobile else (0.6, 1.6, 2.6, 5.0, 6.4, 8.2))
    top = height - 0.3
    for x, label, align in ((step_x, "step", "center"), (bar_x, "$2r$ against 3", "left"),
                            (bit_x, "bit", "center"), (q_x, "$q$", "center"),
                            (r_x, "$r$", "center")):
        ax.text(x, top, label, fontsize=fs.SIZE_TICK, color=fs.MUTED, ha=align, va="center")
    ax.plot([0.15, width - 0.15], [top - 0.22] * 2, color=fs.LINE, lw=fs.LW_AXIS)
    for index, row in enumerate(rows):
        y = top - 0.22 - pitch * (index + 0.5)
        ax.text(step_x, y, str(row["step"]), fontsize=fs.SIZE_LABEL, ha="center", va="center")
        if row["doubled"] is not None:
            remainder_bar(ax, row, y=y - 0.11, x=bar_x, width=bar_w, height=0.22)
            ax.text(bit_x, y, str(row["bit"]), fontsize=fs.SIZE_LABEL, ha="center", va="center")
        quotient = f"{row['q']} = ${row['q']:b}_2$"
        if mobile:
            quotient = f"{row['q']}\n${row['q']:b}_2$"
        ax.text(q_x, y, quotient, fontsize=fs.SIZE_LABEL if not mobile else fs.SIZE_TICK,
                ha="center", va="center", linespacing=1.2)
        ax.text(r_x, y, str(row["r_out"]), fontsize=fs.SIZE_LABEL, ha="center", va="center")
    handles = [
        Patch(label="$2r$", **BAR),
        Patch(label="divisor subtracted", **REMOVED),
        Line2D([], [], color=fs.ROLE["mark"], lw=fs.LW_REF + 0.4, label="divisor 3"),
    ]
    fs.legend(ax, handles=handles, loc="center", bbox_to_anchor=(width / 2, 0.3),
              bbox_transform=ax.transData, ncols=1 if mobile else 3)
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    rows = trace()
    fs.setup()
    out = args.out or fs.ASSETS / "ch08-restoring-division.png"
    for mobile in (False, True):
        target = fs.mobile_path(out) if mobile else out
        print(f"wrote {fs.save(draw(mobile, rows), target.name, target)}")


if __name__ == "__main__":
    main()
