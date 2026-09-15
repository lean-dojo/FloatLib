#!/usr/bin/env python3

"""Render the strict external release summary and duration figure."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "floatlib-external-release"
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402


STATUSES = {
    "pass": ("pass", "#2878b5"),
    "qualified-pass": ("qualified pass", "#e69f00"),
    "observational-complete": ("observational", "#6f58a6"),
    "external-limitation": ("external limitation", "#c46b36"),
}


def read_summary(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != ["suite", "status", "seconds", "log"]:
            raise SystemExit(f"unexpected summary header in {path}")
        rows = list(reader)
    if not rows:
        raise SystemExit(f"empty release summary: {path}")
    for row in rows:
        if row["status"] not in STATUSES:
            raise SystemExit(
                f"unknown release status for {row['suite']}: {row['status']}"
            )
        try:
            seconds = int(row["seconds"])
        except ValueError as error:
            raise SystemExit(
                f"invalid duration for {row['suite']}: {row['seconds']}"
            ) from error
        if seconds < 0:
            raise SystemExit(f"negative duration for {row['suite']}")
    return rows


def write_summary(rows: list[dict[str, str]], output: Path) -> None:
    with (output / "summary.md").open("w", encoding="utf-8", newline="") as stream:
        stream.write("| Suite | Status | Seconds | Log |\n")
        stream.write("| --- | ---: | ---: | --- |\n")
        for row in rows:
            stream.write(
                f"| {row['suite']} | {row['status']} | {row['seconds']} | "
                f"`{row['log']}` |\n"
            )


def render(rows: list[dict[str, str]], output: Path) -> None:
    names = [row["suite"] for row in rows]
    seconds = [int(row["seconds"]) for row in rows]
    colors = [STATUSES[row["status"]][1] for row in rows]
    height = max(5.2, 0.42 * len(rows) + 2.2)
    figure, axis = plt.subplots(figsize=(11, height), layout="constrained")
    positions = list(range(len(rows)))
    axis.barh(positions, seconds, color=colors, alpha=0.88)
    axis.set_yticks(positions, names)
    axis.invert_yaxis()
    axis.set_xlabel("Elapsed wall time (seconds)")
    axis.set_title("FloatLib external release campaign", loc="left", weight="bold")
    axis.grid(axis="x", color="#d1d5db", linewidth=0.7)
    axis.set_axisbelow(True)
    for position, row, elapsed in zip(positions, rows, seconds, strict=True):
        axis.annotate(
            f" {elapsed:,} s · {row['status'].upper()}",
            (elapsed, position),
            xytext=(4, 0),
            textcoords="offset points",
            va="center",
            fontsize=8,
        )
    used_statuses = dict.fromkeys(row["status"] for row in rows)
    axis.legend(
        handles=[
            Patch(
                facecolor=STATUSES[status][1],
                label=STATUSES[status][0],
            )
            for status in used_statuses
        ],
        frameon=False,
        loc="lower right",
    )

    for suffix in ("png", "svg", "pdf"):
        metadata = (
            {"Date": None}
            if suffix == "svg"
            else {"CreationDate": None, "ModDate": None}
            if suffix == "pdf"
            else None
        )
        figure.savefig(
            output / f"campaign-duration.{suffix}",
            dpi=180,
            metadata=metadata,
        )
    plt.close(figure)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary", type=Path)
    parser.add_argument("output", type=Path)
    arguments = parser.parse_args()
    arguments.output.mkdir(parents=True, exist_ok=True)
    rows = read_summary(arguments.summary)
    write_summary(rows, arguments.output)
    render(rows, arguments.output)


if __name__ == "__main__":
    main()
