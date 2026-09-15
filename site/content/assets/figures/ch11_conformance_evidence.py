#!/usr/bin/env python3
"""Draw direct comparison counts and the widths tested.

We wanted this page to answer two questions without making a reader dig through thirteen result
directories: how much independent comparison was run, and whether widths such as 5 and 6 were
really included. Numbers come from the release campaign and the sampled-width follow-up. The script
stops if a result has a nonzero FloatLib mismatch where the figure says zero.

SoftPosit's raw differences stay visible. The retained adjudication found zero FloatLib
exact-specification mismatches in those rows. The plot keeps the comparison differences
visible; chapter 16 gives the diagnosis and provenance.

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

from matplotlib.patches import Patch  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402


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


def draw() -> object:
    fs.setup()
    direct = direct_comparisons()
    p3109 = p3109_by_width()
    softposit = softposit_by_width()

    fig, (top, bottom) = fs.figure(
        10.0,
        nrows=2,
        gridspec_kw={"height_ratios": [1.15, 1]},
    )
    # Reserve space above each axes for its title and legend, and below for the
    # small-width counts. None of those labels should cover a plotted case.
    fig.subplots_adjust(left=0.22, right=0.97, bottom=0.16, top=0.82, hspace=0.85)

    labels = [row[0] for row in direct]
    values = [row[1] for row in direct]
    colors = [fs.GREEN if row[0] == "SoftPosit" else fs.BLUE for row in direct]
    positions = list(range(len(direct)))
    top.barh(positions, values, color=colors, alpha=0.9)
    top.set_yticks(positions, labels=labels)
    top.set_xscale("log")
    top.set_xlim(right=max(values) * 8)
    top.set_xlabel("evaluated cases (log scale)")
    top.set_title(
        "Cases compared",
        loc="left",
        fontweight="bold",
        pad=60,
    )
    for position, value in zip(positions, values, strict=True):
        top.annotate(
            f" {value:,}",
            (value, position),
            xytext=(3, 0),
            textcoords="offset points",
            va="center",
            fontsize=9,
        )
    difference_marker = Line2D(
        [], [], marker="D", linestyle="none", color=fs.ORANGE,
        label="Differences (see labelled counts)", markersize=5,
    )
    for position, (_label, value, status) in enumerate(direct):
        if status == "external":
            top.plot(value, position, "D", color=fs.ORANGE, markersize=5)
    top.legend(
        handles=[
            Patch(color=fs.BLUE, label="Other comparisons: no mismatches"),
            Patch(
                color=fs.GREEN,
                label=(
                    f"SoftPosit: {sum(row[1] for row in softposit.values()):,} differences "
                    f"in {sum(row[0] for row in softposit.values()):,} cases"
                ),
            ),
            difference_marker,
        ],
        loc="lower left",
        bbox_to_anchor=(0, 1.015),
        borderaxespad=0,
    )

    widths = sorted(set(p3109) | set(softposit))
    x = list(range(len(widths)))
    p_values = [p3109.get(width, (0, 0))[1] for width in widths]
    s_values = [softposit.get(width, (0, 0, ""))[0] for width in widths]
    bar_width = 0.39
    bottom.bar(
        [value - bar_width / 2 for value in x],
        p_values,
        width=bar_width,
        color=fs.BLUE,
        label="P3109 public value tables, zero mismatches",
    )
    bottom.bar(
        [value + bar_width / 2 for value in x],
        s_values,
        width=bar_width,
        color=fs.GREEN,
        label="SoftPosit comparisons",
    )
    # Colour identifies the implementation, not whether its entire suite had zero
    # differences. A separate marker cannot make two mismatches look like a whole
    # bar of failures, and unlike a stacked segment it remains visible on a log axis.
    for position, width in zip(x, widths, strict=True):
        cases, differences, _mode = softposit.get(width, (0, 0, ""))
        if differences:
            location = position + bar_width / 2
            bottom.plot(location, cases, "D", color=fs.ORANGE, markersize=5)
            bottom.annotate(
                f"{differences:,}",
                (location, cases),
                xytext=(0, 8),
                textcoords="offset points",
                ha="center",
                fontsize=9,
            )
    bottom.set_yscale("log")
    bottom.set_xticks(x, labels=[str(width) for width in widths])
    bottom.set_xlabel("encoded width (bits)")
    bottom.set_ylabel("evaluated cases (log scale)")
    bottom.set_title(
        "Cases checked at each width",
        loc="left",
        fontweight="bold",
        pad=60,
    )
    bottom.legend(
        handles=[
            Patch(color=fs.BLUE, label="P3109 value tables"),
            Patch(color=fs.GREEN, label="SoftPosit: all compared cases"),
            difference_marker,
        ],
        loc="lower left",
        bbox_to_anchor=(0, 1.015),
        borderaxespad=0,
    )
    disagreement_counts = "; ".join(
        f"{width} bit: {differences:,}"
        for width, (_cases, differences, _mode) in sorted(softposit.items())
        if differences
    )
    fig.text(
        0.22,
        0.025,
        "SoftPosit: exhaustive at 2 to 8 bits; sampled at 9 to 16 and 32 bits.\n"
        "The 32-bit count includes generic pX2 and dedicated p32. Reruns count once.\n"
        "Differences: " + disagreement_counts + ".",
        ha="left",
        va="bottom",
        fontsize=9,
        color=fs.INK,
    )

    fig.suptitle(
        "Checks against independent implementations",
        x=0.02,
        ha="left",
        fontsize=14,
        fontweight="bold",
    )
    fig.text(
        0.02, 0.947,
        "Counts, not timings. Longer bars mean more cases checked.",
        ha="left", fontsize=10, color=fs.INK,
    )
    return fig


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()
    target = fs.save(draw(), OUT_NAME, out=arguments.out)
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
