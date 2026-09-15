#!/usr/bin/env python3

"""Render the retained ecosystem campaign from its tab-separated summary."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "floatlib-ecosystem-result"
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402


STATUSES = {
    "pass": ("pass", "#2878b5"),
    "qualified-pass": ("qualified pass", "#e69f00"),
    "observational-complete": ("observational", "#6f58a6"),
    "unsupported": ("unsupported", "#8d8d8d"),
    "external-limitation": ("external limitation", "#c46b36"),
    "diagnostic-failure": ("diagnostic failure", "#c23b53"),
    "upstream-failure": ("upstream failure", "#7f1d1d"),
}

EVIDENCE = {
    "upstream-qualification",
    "direct-differential",
    "direct-observational",
}


def read_summary(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != [
            "suite",
            "evidence",
            "status",
            "seconds",
            "log",
        ]:
            raise SystemExit(f"unexpected summary header in {path}")
        rows = list(reader)
    if not rows:
        raise SystemExit(f"empty ecosystem summary: {path}")
    for row in rows:
        if row["status"] not in STATUSES:
            raise SystemExit(
                f"unknown status for {row['suite']}: {row['status']}"
            )
        if row["evidence"] not in EVIDENCE:
            raise SystemExit(
                f"unknown evidence class for {row['suite']}: "
                f"{row['evidence']}"
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


def duration_text(seconds: int) -> str:
    if seconds < 60:
        return f"{seconds}s"
    minutes, seconds = divmod(seconds, 60)
    if minutes < 60:
        return f"{minutes}m {seconds:02d}s"
    hours, minutes = divmod(minutes, 60)
    return f"{hours}h {minutes:02d}m"


def render(rows: list[dict[str, str]], output: Path) -> None:
    output.mkdir(parents=True, exist_ok=True)
    ordered = sorted(rows, key=lambda row: int(row["seconds"]))
    names = [row["suite"] for row in ordered]
    measured_seconds = [int(row["seconds"]) for row in ordered]
    bar_seconds = [max(1, value) for value in measured_seconds]
    colors = [STATUSES[row["status"]][1] for row in ordered]

    height = max(5.0, 0.43 * len(rows) + 1.8)
    fig, axis = plt.subplots(figsize=(11.5, height))
    positions = list(range(len(rows)))
    axis.barh(
        positions,
        bar_seconds,
        color=colors,
        edgecolor="#333333",
        linewidth=0.5,
    )
    axis.set_yticks(positions, labels=names)
    axis.set_xscale("log")
    axis.set_xlabel("wall time in seconds (log scale)")
    axis.set_title(
        "Retained external-tool campaign: duration and reported outcome",
        loc="left",
    )
    axis.spines[["top", "right"]].set_visible(False)
    axis.grid(axis="x", color="#d9d9d6", linewidth=0.6)
    axis.set_axisbelow(True)

    for position, bar_value, measured in zip(
        positions, bar_seconds, measured_seconds, strict=True
    ):
        axis.annotate(
            duration_text(measured),
            (bar_value, position),
            xytext=(5, 0),
            textcoords="offset points",
            va="center",
            fontsize=9,
            color="#333333",
        )

    used_statuses = dict.fromkeys(row["status"] for row in ordered)
    handles = [
        Patch(
            facecolor=STATUSES[status][1],
            edgecolor="#333333",
            label=STATUSES[status][0],
        )
        for status in used_statuses
    ]
    axis.legend(handles=handles, frameon=False, loc="lower right")
    fig.tight_layout()

    for extension in ("png", "svg", "pdf"):
        metadata = (
            {"Date": None}
            if extension == "svg"
            else {"CreationDate": None, "ModDate": None}
            if extension == "pdf"
            else None
        )
        fig.savefig(
            output / f"ecosystem-duration.{extension}",
            dpi=180,
            metadata=metadata,
        )
    plt.close(fig)


def write_summary(rows: list[dict[str, str]], output: Path) -> None:
    with (output / "summary.md").open("w", encoding="utf-8", newline="") as stream:
        stream.write("| Suite | Evidence | Status | Seconds | Log |\n")
        stream.write("| --- | --- | --- | ---: | --- |\n")
        for row in rows:
            stream.write(
                f"| {row['suite']} | {row['evidence']} | {row['status']} | "
                f"{row['seconds']} | `{row['log']}` |\n"
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary", type=Path)
    parser.add_argument("output", type=Path)
    arguments = parser.parse_args()
    rows = read_summary(arguments.summary)
    render(rows, arguments.output)
    write_summary(rows, arguments.output)


if __name__ == "__main__":
    main()
