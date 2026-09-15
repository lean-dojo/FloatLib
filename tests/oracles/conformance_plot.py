#!/usr/bin/env python3
"""Plot case coverage and failures from a conformance CSV."""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "floatlib-conformance"
import matplotlib.pyplot as plt
from matplotlib.patches import Patch


PASS_COLOR = "#15803d"
FAIL_COLOR = "#b91c1c"
GRID_COLOR = "#d1d5db"


@dataclass(frozen=True)
class Aggregate:
    """One displayed group after summing all matching input rows."""

    name: str
    rows: int
    cases: int
    mismatches: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Aggregate a conformance CSV and plot tested cases with pass/fail annotations."
        )
    )
    parser.add_argument("input", type=Path, help="source CSV")
    parser.add_argument(
        "output_prefix",
        type=Path,
        help="output path without an extension; PNG, SVG, and PDF are written",
    )
    parser.add_argument(
        "--group-column",
        action="append",
        required=True,
        help="CSV column to aggregate; repeat to create another panel",
    )
    parser.add_argument(
        "--group-label",
        action="append",
        default=[],
        metavar="COLUMN=LABEL",
        help="human label for a grouping column",
    )
    parser.add_argument(
        "--cases-column",
        default="cases",
        help="nonnegative integer coverage column (default: cases)",
    )
    parser.add_argument(
        "--mismatch-column",
        action="append",
        required=True,
        help="nonnegative integer failure column; repeat to sum distinct failure classes",
    )
    parser.add_argument(
        "--status-column",
        help="optional pass/fail column checked against the mismatch total",
    )
    parser.add_argument("--title", required=True, help="figure title")
    parser.add_argument(
        "--subtitle",
        default="",
        help="short scope statement shown below the title",
    )
    return parser.parse_args()


def parse_labels(entries: list[str]) -> dict[str, str]:
    labels: dict[str, str] = {}
    for entry in entries:
        if "=" not in entry:
            raise ValueError(f"group label must be COLUMN=LABEL: {entry}")
        column, label = entry.split("=", 1)
        if not column or not label:
            raise ValueError(f"group label must be COLUMN=LABEL: {entry}")
        if column in labels:
            raise ValueError(f"duplicate label for grouping column: {column}")
        labels[column] = label
    return labels


def nonnegative_int(row: dict[str, str], column: str, row_number: int) -> int:
    try:
        value = int(row[column])
    except KeyError as error:
        raise ValueError(f"CSV has no {column!r} column") from error
    except ValueError as error:
        raise ValueError(
            f"row {row_number} has a non-integer {column!r}: {row[column]!r}"
        ) from error
    if value < 0:
        raise ValueError(f"row {row_number} has a negative {column!r}: {value}")
    return value


def read_rows(
    path: Path,
    required_columns: set[str],
    cases_column: str,
    mismatch_columns: list[str],
    status_column: str | None,
) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames is None:
            raise ValueError(f"{path}: missing CSV header")
        missing = required_columns - set(reader.fieldnames)
        if missing:
            raise ValueError(f"{path}: missing columns: {', '.join(sorted(missing))}")
        rows = list(reader)

    if not rows:
        raise ValueError(f"{path}: no result rows")

    for row_number, row in enumerate(rows, 2):
        cases = nonnegative_int(row, cases_column, row_number)
        if cases == 0:
            raise ValueError(f"row {row_number} reports zero tested cases")
        mismatches = sum(
            nonnegative_int(row, column, row_number)
            for column in mismatch_columns
        )
        if status_column is not None:
            status = row[status_column].strip().lower()
            if status not in {"pass", "fail"}:
                raise ValueError(
                    f"row {row_number} has invalid status {row[status_column]!r}"
                )
            expected = "pass" if mismatches == 0 else "fail"
            if status != expected:
                raise ValueError(
                    f"row {row_number} says {status!r} but its mismatch total "
                    f"requires {expected!r}"
                )
    return rows


def aggregate(
    rows: list[dict[str, str]],
    group_column: str,
    cases_column: str,
    mismatch_columns: list[str],
) -> list[Aggregate]:
    grouped: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        name = row[group_column].strip()
        if not name:
            raise ValueError(f"empty value in grouping column {group_column!r}")
        grouped[name].append(row)

    result = []
    for name in sorted(grouped, key=str.casefold):
        members = grouped[name]
        result.append(
            Aggregate(
                name=name,
                rows=len(members),
                cases=sum(int(row[cases_column]) for row in members),
                mismatches=sum(
                    int(row[column])
                    for row in members
                    for column in mismatch_columns
                ),
            )
        )
    return result


def configure_case_axis(axis: plt.Axes, aggregates: list[Aggregate]) -> None:
    positive = [entry.cases for entry in aggregates if entry.cases > 0]
    if max(positive) / min(positive) >= 50:
        axis.set_xscale("log")
    axis.set_xlabel("Cases checked")
    axis.grid(axis="x", color=GRID_COLOR, linewidth=0.7, alpha=0.8)
    axis.set_axisbelow(True)


def plot_panel(
    axis: plt.Axes,
    aggregates: list[Aggregate],
    heading: str,
) -> None:
    positions = list(range(len(aggregates)))
    colors = [
        PASS_COLOR if entry.mismatches == 0 else FAIL_COLOR
        for entry in aggregates
    ]
    axis.barh(
        positions,
        [entry.cases for entry in aggregates],
        color=colors,
        alpha=0.88,
    )
    axis.set_yticks(positions, [entry.name for entry in aggregates])
    axis.invert_yaxis()
    axis.set_title(heading, loc="left", fontweight="bold")
    configure_case_axis(axis, aggregates)

    for position, entry in zip(positions, aggregates, strict=True):
        verdict = "PASS" if entry.mismatches == 0 else "FAIL"
        annotation = (
            f" {entry.cases:,} cases · {verdict} · "
            f"{entry.mismatches:,} mismatches"
        )
        axis.annotate(
            annotation,
            (entry.cases, position),
            xytext=(4, 0),
            textcoords="offset points",
            va="center",
            fontsize=8,
            color="#111827",
        )


def write_plot(
    output_prefix: Path,
    title: str,
    subtitle: str,
    panels: list[tuple[str, list[Aggregate]]],
) -> None:
    widest_panel = max(len(aggregates) for _, aggregates in panels)
    figure_width = max(8.5, 7.2 * len(panels))
    figure_height = max(4.8, 0.42 * widest_panel + 2.8)
    figure, axes = plt.subplots(
        1,
        len(panels),
        figsize=(figure_width, figure_height),
        squeeze=False,
        constrained_layout=True,
    )

    for axis, (heading, aggregates) in zip(axes[0], panels, strict=True):
        plot_panel(axis, aggregates, heading)

    total_cases = sum(entry.cases for entry in panels[0][1])
    total_mismatches = sum(entry.mismatches for entry in panels[0][1])
    verdict = "PASS" if total_mismatches == 0 else "FAIL"
    summary = (
        f"{total_cases:,} checked cases · {total_mismatches:,} mismatches · {verdict}"
    )
    if subtitle:
        summary = f"{subtitle}\n{summary}"
    figure.suptitle(f"{title}\n{summary}", fontsize=14, fontweight="bold")
    figure.legend(
        handles=[
            Patch(facecolor=PASS_COLOR, label="No reported mismatches"),
            Patch(facecolor=FAIL_COLOR, label="One or more mismatches"),
        ],
        loc="outside lower center",
        ncols=2,
        frameon=False,
    )

    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(
        output_prefix.with_suffix(".png"),
        dpi=180,
        metadata={"Software": "FloatLib"},
    )
    figure.savefig(
        output_prefix.with_suffix(".svg"),
        metadata={"Date": None},
    )
    figure.savefig(
        output_prefix.with_suffix(".pdf"),
        metadata={
            "Creator": "FloatLib",
            "CreationDate": None,
            "ModDate": None,
        },
    )
    plt.close(figure)


def main() -> None:
    args = parse_args()
    labels = parse_labels(args.group_label)
    unknown_labels = set(labels) - set(args.group_column)
    if unknown_labels:
        raise ValueError(
            "labels provided for unused grouping columns: "
            + ", ".join(sorted(unknown_labels))
        )

    required_columns = {
        *args.group_column,
        args.cases_column,
        *args.mismatch_column,
    }
    if args.status_column is not None:
        required_columns.add(args.status_column)
    rows = read_rows(
        args.input,
        required_columns,
        args.cases_column,
        args.mismatch_column,
        args.status_column,
    )
    panels = [
        (
            labels.get(column, column.replace("_", " ").title()),
            aggregate(rows, column, args.cases_column, args.mismatch_column),
        )
        for column in args.group_column
    ]
    write_plot(args.output_prefix, args.title, args.subtitle, panels)


if __name__ == "__main__":
    main()
