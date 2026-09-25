#!/usr/bin/env python3
"""Draw direct comparison counts and the widths tested.

We wanted this page to answer two questions without making a reader dig through thirteen result
directories: how much independent comparison was run, and whether widths such as 5 and 6 were
really included. Numbers come from the release campaign and the sampled-width follow-up. The script
stops if a result has a nonzero FloatLib mismatch where the figure says zero.

SoftPosit's raw differences stay visible. The retained adjudication found zero FloatLib
exact-specification mismatches in those rows. The plot keeps the comparison differences
visible; chapter 16 gives the diagnosis and provenance.

The original asset contains suite totals; a separate ch11-conformance-widths.png contains
per-width counts. Both have stacked phone companions. All four outputs are written beside
the --out path when it is supplied; no series manifest is required.

Sources:
tests/results/main/release/external/{01-testfloat,02-format-standards,
03-mpfr-primitives,04-mpfr-reductions,07-binary16-mpfr-rows,
08-testfloat-level2-smoke,09-ibm-fpgen,10-smt-qf-fp,11-softposit}.
tests/results/main/softposit-widths.json.

Run from anywhere: python3 ch11_conformance_evidence.py [--out PNG]
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402


EXTERNAL = fs.REPO / "tests" / "results" / "main" / "release" / "external"
SOFTPOSIT_FOLLOWUP = EXTERNAL.parent.parent / "softposit-widths.json"
OUT_NAME = "ch11-conformance-evidence.png"


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    if not rows:
        raise SystemExit(f"empty retained table: {path}")
    return rows


def one_csv_row(path: Path) -> dict[str, str]:
    rows = read_csv(path)
    if len(rows) != 1:
        raise SystemExit(f"expected one retained row in {path}, found {len(rows)}")
    return rows[0]


def require_zero(value: int, label: str) -> None:
    if value != 0:
        raise SystemExit(f"{label} has {value} mismatches; refusing to draw it as a pass")


def marker_count(path: Path, pattern: str, label: str) -> int:
    match = re.search(pattern, path.read_text(encoding="utf-8"))
    if match is None:
        raise SystemExit(f"cannot read {label} from {path}")
    return int(match.group(1))


def softposit_rows() -> list[dict]:
    """Add newly measured widths, checking that repeated cells reproduce the release."""
    original = read_csv(EXTERNAL / "11-softposit" / "summary.csv")
    if sum(int(row["mismatches"]) for row in original) != 7562:
        raise SystemExit("SoftPosit release differences changed; review its adjudication")
    followup = json.loads(SOFTPOSIT_FOLLOWUP.read_text(encoding="utf-8"))
    cells = followup["summary"]
    for field in ("cases", "mismatches"):
        key = "differences" if field == "mismatches" else field
        if sum(int(row[field]) for row in cells) != followup["checks"][key]:
            raise SystemExit(f"SoftPosit follow-up {field} do not reproduce its total")
    if not followup["checks"]["public_and_exact_spec_agree_on_all_distinct_inputs"]:
        raise SystemExit("SoftPosit follow-up needs a new exact-specification review")
    old = {
        (row["family"], int(row["bits"]), row["operation"]): row
        for row in original
    }
    added = []
    seen = set()
    for row in cells:
        key = row["family"], int(row["bits"]), row["operation"]
        if key in seen:
            raise SystemExit(f"duplicate SoftPosit follow-up cell: {key}")
        seen.add(key)
        if key in old:
            for field in ("cases", "mismatches"):
                if int(row[field]) != int(old[key][field]):
                    raise SystemExit(f"SoftPosit rerun changed {key} {field}")
        else:
            added.append(row)
    operations = {"add", "sub", "mul", "div", "fma", "sqrt", "rint", "eq", "le", "lt"}
    expected = {("px2", width, op) for width in range(9, 16) for op in operations}
    actual = {(row["family"], int(row["bits"]), row["operation"]) for row in added}
    if actual != expected:
        raise SystemExit("SoftPosit follow-up does not cover every requested cell at 9–15 bits")
    return original + added


def direct_comparisons() -> list[tuple[str, int, str]]:
    """Return comparable case counts; suites without a case counter stay in the status table."""
    rows: list[tuple[str, int, str]] = []

    testfloat = one_csv_row(EXTERNAL / "01-testfloat" / "summary.csv")
    for field in ("value_mismatches", "flag_mismatches", "parse_errors"):
        require_zero(int(testfloat[field]), f"TestFloat {field}")
    rows.append(("Berkeley TestFloat level 1", int(testfloat["cases"]), "pass"))

    softposit_cases = sum(int(row["cases"]) for row in softposit_rows())
    adjudication = (EXTERNAL / "11-softposit" / "ADJUDICATION.md").read_text(
        encoding="utf-8"
    )
    if not re.search(
        # The retained adjudication predates the public rename; its bytes are evidence.
        r"FloatLib specification mismatches in these rows:\s+\*\*0\*\*",
        adjudication,
    ):
        raise SystemExit("SoftPosit adjudication no longer supports the figure's label")
    rows.append(("SoftPosit", softposit_cases, "external"))

    standards = {
        row["oracle"]: row
        for row in read_csv(EXTERNAL / "02-format-standards" / "summary.csv")
    }
    for oracle, label in (
        ("P3109 4.0.3 value tables", "IEEE P3109 value tables"),
        ("ONNX low-bit decode", "ONNX low-bit tables"),
    ):
        row = standards[oracle]
        require_zero(int(row["mismatches"]), f"{oracle}")
        rows.append((label, int(row["cases"]), "pass"))

    level2 = one_csv_row(EXTERNAL / "08-testfloat-level2-smoke" / "summary.csv")
    for field in ("value_mismatches", "flag_mismatches", "parse_errors"):
        require_zero(int(level2[field]), f"TestFloat level 2 {field}")
    rows.append(("Selected TestFloat level 2", int(level2["cases"]), "pass"))

    for suite, label, pattern in (
        (
            "03-mpfr-primitives",
            "MPFR primitive arithmetic",
            r"passed: ([0-9]+) cases",
        ),
        (
            "04-mpfr-reductions",
            "MPFR exact reductions",
            r"passed: ([0-9]+) cases",
        ),
    ):
        rows.append(
            (
                label,
                marker_count(
                    EXTERNAL / "logs" / f"{suite}.log",
                    pattern,
                    label,
                ),
                "pass",
            )
        )

    binary16_log = (
        EXTERNAL / "logs" / "07-binary16-mpfr-rows.log"
    ).read_text(encoding="utf-8")
    binary16_counts = [
        int(value)
        for value in re.findall(r"passed: ([0-9]+) ordered pairs", binary16_log)
    ]
    if binary16_counts != [65536, 65536]:
        raise SystemExit(f"unexpected binary16 MPFR rows: {binary16_counts}")
    rows.append(("binary16 MPFR rows", sum(binary16_counts), "pass"))

    ibm = json.loads(
        (EXTERNAL / "09-ibm-fpgen" / "summary.json").read_text(encoding="utf-8")
    )
    retained_ibm_cases = 0
    for group in ibm["groups"]:
        retained_ibm_cases += int(group["cases"])
        log = EXTERNAL / "09-ibm-fpgen" / (
            f"{group['format']}_{group['operation']}_{group['rounding']}.oracle.log"
        )
        result_lines = [
            line
            for line in log.read_text(encoding="utf-8").splitlines()
            if line.startswith("RESULT ")
        ]
        if len(result_lines) != 1:
            raise SystemExit(f"expected one IBM FPgen RESULT line in {log}")
        fields = dict(
            field.split("=", 1)
            for field in result_lines[0].removeprefix("RESULT ").split()
        )
        for field in ("value_mismatches", "flag_mismatches", "parse_errors"):
            require_zero(int(fields[field]), f"IBM FPgen {field}")
    if retained_ibm_cases != int(ibm["counters"]["emitted"]):
        raise SystemExit("IBM FPgen group counts do not reproduce the emitted total")
    rows.append(("IBM FPgen", int(ibm["counters"]["emitted"]), "pass"))

    smt = json.loads(
        (EXTERNAL / "10-smt-qf-fp" / "summary.json").read_text(encoding="utf-8")
    )
    require_zero(int(smt["counts"]["mismatches"]), "SMT QF_FP")
    rows.append(("Z3 QF_FP", int(smt["counts"]["generated"]), "pass"))

    return sorted(rows, key=lambda row: row[1])


def p3109_by_width() -> dict[int, tuple[int, int]]:
    rows: dict[int, tuple[int, int]] = {}
    shards = EXTERNAL / "02-format-standards" / "p3109-shards"
    for path in shards.glob("*.csv"):
        width = int(path.stem)
        with path.open(newline="", encoding="utf-8") as handle:
            values = list(csv.reader(handle))
        if len(values) != 1 or len(values[0]) != 5:
            raise SystemExit(f"unexpected P3109 shard: {path}")
        _oracle, status, formats, cases, mismatches = values[0]
        if status != "pass":
            raise SystemExit(f"P3109 width {width} is not a retained pass")
        require_zero(int(mismatches), f"P3109 width {width}")
        rows[width] = (int(formats), int(cases))
    if set(rows) != set(range(3, 17)):
        raise SystemExit(f"P3109 width set changed: {sorted(rows)}")
    return rows


def softposit_by_width() -> dict[int, tuple[int, int, str]]:
    totals: dict[int, dict[str, object]] = defaultdict(
        lambda: {"cases": 0, "differences": 0, "modes": set()}
    )
    for row in softposit_rows():
        width = int(row["bits"])
        totals[width]["cases"] = int(totals[width]["cases"]) + int(row["cases"])
        totals[width]["differences"] = (
            int(totals[width]["differences"]) + int(row["mismatches"])
        )
        modes = totals[width]["modes"]
        assert isinstance(modes, set)
        modes.add(row["mode"])
    result = {}
    for width, values in totals.items():
        modes = values["modes"]
        assert isinstance(modes, set)
        if len(modes) != 1:
            raise SystemExit(f"mixed SoftPosit modes at width {width}: {modes}")
        result[width] = (
            int(values["cases"]),
            int(values["differences"]),
            next(iter(modes)),
        )
    expected = set(range(2, 17)) | {32}
    if set(result) != expected:
        raise SystemExit(f"SoftPosit width set changed: {sorted(result)}")
    return result


def draw_totals(mobile: bool, direct, softposit):
    fig = plt.figure(figsize=(3.8, 9.6) if mobile else (9, 6.8))
    fig.text(0.035, 0.98, "Cases compared", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.928 if mobile else 0.905,
             "Counts, not time or input coverage", fontsize=12, color=fs.MUTED)
    ax = fig.add_axes([0.065, 0.365, 0.89, 0.515] if mobile else [0.31, 0.35, 0.65, 0.48])
    rows = list(reversed(direct))
    positions = list(range(len(rows)))[::-1]
    ax.set_xscale("log")
    ax.set_xlim(100, 10 ** 9)
    ax.set_ylim(-0.7, len(rows) - 0.15)
    for y, (label, value, status) in zip(positions, rows):
        colour = fs.GREEN if status == "external" else fs.BLUE
        ax.barh(y, value - 100, left=100, height=0.24 if mobile else 0.48, color=colour)
        if mobile:
            ax.text(0, y + 0.27, label.replace("Berkeley ", ""),
                    transform=ax.get_yaxis_transform(), fontsize=11.5, va="bottom")
            ax.text(1, y + 0.27, f"{value:,}", transform=ax.get_yaxis_transform(),
                    fontsize=11.5, ha="right", va="bottom")
        else:
            ax.text(value * 1.18, y, f"{value:,}", fontsize=11.5, va="center")
        if status == "external":
            ax.plot(value, y, marker="D", ms=6, color=fs.VERMILION)
    ax.set_yticks([] if mobile else positions,
                  labels=[] if mobile else [r[0] for r in rows], fontsize=11.5)
    ax.tick_params(axis="y", length=0)
    ax.tick_params(axis="x", labelsize=11)
    ax.set_xticks([10 ** n for n in (2, 4, 6, 8)],
                  labels=["100", "10,000", "1M", "100M"])
    ax.minorticks_off()
    ax.grid(axis="y", visible=False)
    ax.spines['left'].set_visible(False)
    ax.set_xlabel("compared cases (log scale)", fontsize=11.5)
    differences = sum(row[1] for row in softposit.values())
    fig.text(0.035, 0.282 if mobile else 0.245,
             f"◆ SoftPosit: {differences:,} differences" +
              ("\nfrom seven distinct inputs." if mobile else " from seven distinct inputs."),
              fontsize=12, color=fs.VERMILION, linespacing=1.45,
              va="top" if mobile else "baseline")
    fig.text(0.035, 0.217 if mobile else 0.185,
             "All seven agree with FloatLib's\nexact specification." if mobile else
             "All seven agree with FloatLib's exact specification. Other suites report zero mismatches.",
             fontsize=11.5, linespacing=1.45, va="top" if mobile else "baseline")
    fig.text(0.035, 0.166 if mobile else 0.123,
             "Other suites: zero mismatches under\ntheir stated comparison rules." if mobile else
             "Each suite has its own comparison rule; a case is not a common unit of input coverage.",
             fontsize=11.5, color=fs.MUTED, linespacing=1.45,
             va="top" if mobile else "baseline")
    fig.text(0.035, 0.026,
             "TestFloat: non-NaN bits and flags;\nNaN class and signaling, not all payloads.\nZ3: encodings where defined; abstract NaNs."
             if mobile else
             "TestFloat checks non-NaN bits and flags; NaN class and signaling, without a universal payload rule.\n"
             "Z3 checks encodings where defined by SMT; its NaNs are abstract.",
             fontsize=11.5, color=fs.MUTED, linespacing=1.5)
    return fig


def width_panel(fig, rect, rows, *, title: str, colour, mobile: bool, differences: bool):
    ax = fig.add_axes(rect)
    widths = sorted(rows)
    positions = list(range(len(widths)))[::-1]
    ax.set_xscale("log")
    ax.set_xlim(10, 10 ** 8)
    ax.set_ylim(-0.7, len(widths) - 0.25)
    for y, width in zip(positions, widths):
        value = rows[width][0] if differences else rows[width][1]
        mismatch = rows[width][1] if differences else 0
        # Hatching separates sampled cases without treating them as failures.
        sampled = differences and rows[width][2] != "exhaustive"
        ax.barh(y, value - 10, left=10, height=0.58, color=colour,
                edgecolor="white", lw=0.3, hatch="///" if sampled else None)
        if mismatch:
            ax.plot(value, y, "D", color=fs.VERMILION, ms=5)
        ax.text(value * 1.20, y, f"{value:,}", fontsize=11 if mobile else 10.5, va="center")
    ax.set_yticks(positions, labels=[str(w) for w in widths], fontsize=11.5)
    ax.tick_params(axis="y", length=0)
    ax.tick_params(axis="x", labelsize=11)
    ax.set_xticks([100, 10000, 1000000], labels=["100", "10,000", "1M"])
    ax.minorticks_off()
    ax.grid(axis="y", visible=False)
    ax.spines["left"].set_visible(False)
    ax.set_xlabel("cases (log scale)", fontsize=11.5)
    ax.set_ylabel("width (bits)", fontsize=11.5)
    ax.set_title(title, fontsize=12.5, weight="bold", loc="left", pad=13)


def draw_widths(mobile: bool, p3109, softposit):
    fig = plt.figure(figsize=(3.8, 13.0) if mobile else (9, 6.5))
    fig.text(0.035, 0.98, "Which widths were checked?", fontsize=14, weight="bold", va="top")
    fig.text(0.035, 0.94 if mobile else 0.89,
             "Case counts, with each suite's own rules", fontsize=11.5, color=fs.MUTED)
    width_panel(fig, [0.18, 0.59, 0.78, 0.30] if mobile else [0.09, 0.28, 0.38, 0.51],
                p3109, title="P3109 value tables: zero mismatches", colour=fs.BLUE,
                mobile=mobile, differences=False)
    width_panel(fig, [0.18, 0.195, 0.78, 0.295] if mobile else [0.59, 0.28, 0.38, 0.51],
                softposit, title="SoftPosit operation comparisons", colour=fs.GREEN,
                mobile=mobile, differences=True)
    fig.text(0.035, 0.135 if mobile else 0.17,
             "SoftPosit, for the operations tested:\nsolid: exhaustive at 2 to 8 bits;\nhatched: sampled at 9 to 16 and 32 bits."
             if mobile else
             "SoftPosit: exhaustive for tested operations at 2 to 8 bits; hatched bars sample 9 to 16 and 32 bits.",
             fontsize=11.5, linespacing=1.45, va="top" if mobile else "baseline")
    diff_labels = [f"{w} bit: {d:,}" for w, (_, d, _) in sorted(softposit.items()) if d]
    diff_text = "; ".join(diff_labels[:2]) + ";\n" + "; ".join(diff_labels[2:]) if mobile else "; ".join(diff_labels)
    fig.text(0.035, 0.078 if mobile else 0.10,
             "◆ Differences: " + diff_text + ".", fontsize=11.5, color=fs.VERMILION, linespacing=1.45,
             va="top" if mobile else "baseline")
    fig.text(0.035, 0.031 if mobile else 0.028,
             "32-bit cases include pX2 and p32.\nReruns count once. Counts are not timings."
             if mobile else
             "32-bit cases include generic pX2 and dedicated p32. Repeated runs count once. Counts are not timings.",
             fontsize=11.5 if mobile else 11, color=fs.MUTED, linespacing=1.45,
             va="top" if mobile else "baseline")
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    direct = direct_comparisons()
    p3109, softposit = p3109_by_width(), softposit_by_width()
    assert sum(v[1] for v in softposit.values()) == 7564
    assert sum(v[0] for v in softposit.values()) == 32893800
    fs.setup()
    out = args.out or fs.ASSETS / OUT_NAME
    width_out = out.with_name("ch11-conformance-widths.png")
    for mobile in (False, True):
        for target, fig in [(out, draw_totals(mobile, direct, softposit)),
                             (width_out, draw_widths(mobile, p3109, softposit))]:
            target = target.with_name(target.stem + "-mobile.png") if mobile else target
            print(f"wrote {fs.save(fig, target.name, target)}")
    print(json.dumps({"totals": direct, "p3109_by_width": p3109,
                      "softposit_by_width": softposit}, sort_keys=True))


if __name__ == "__main__":
    main()
