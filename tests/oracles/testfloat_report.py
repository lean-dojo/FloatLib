#!/usr/bin/env python3
"""Write CSV and Markdown summaries for a Berkeley TestFloat campaign."""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path
from typing import TextIO


FIELDS = (
    "format",
    "operation",
    "rounding",
    "cases",
    "value_mismatches",
    "flag_mismatches",
    "parse_errors",
)
COUNT_FIELDS = (
    "cases",
    "value_mismatches",
    "flag_mismatches",
    "parse_errors",
)


def read_campaigns(path: Path) -> list[dict[str, str]]:
    campaigns: list[dict[str, str]] = []
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            words = line.split()
            if not words or words[0] != "RESULT":
                raise ValueError(f"{path}:{line_number}: invalid campaign result")
            row = dict(word.split("=", 1) for word in words[1:])
            missing = [field for field in FIELDS if field not in row]
            if missing:
                raise ValueError(
                    f"{path}:{line_number}: missing fields: {', '.join(missing)}"
                )
            for field in COUNT_FIELDS:
                int(row[field])
            campaigns.append({field: row[field] for field in FIELDS})
    if not campaigns:
        raise ValueError(f"{path}: no TestFloat campaign results")
    return campaigns


def totals(rows: list[dict[str, str]]) -> dict[str, int]:
    result = {"campaigns": len(rows)}
    for field in COUNT_FIELDS:
        result[field] = sum(int(row[field]) for row in rows)
    return result


def grouped(
    rows: list[dict[str, str]], field: str
) -> list[tuple[str, dict[str, int]]]:
    groups: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        groups[row[field]].append(row)
    return [(name, totals(groups[name])) for name in sorted(groups)]


def write_campaigns(path: Path, rows: list[dict[str, str]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def write_summary_csv(
    path: Path,
    profile: str,
    level: int,
    seed: int,
    result: dict[str, int],
) -> None:
    fields = ("profile", "level", "seed", "campaigns", *COUNT_FIELDS)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerow(
            {
                "profile": profile,
                "level": level,
                "seed": seed,
                **result,
            }
        )


def write_group_table(
    stream: TextIO,
    title: str,
    label: str,
    groups: list[tuple[str, dict[str, int]]],
) -> None:
    stream.write(f"\n## {title}\n\n")
    stream.write(
        f"| {label} | Campaigns | Cases | Value mismatches | "
        "Flag mismatches | Parse errors |\n"
    )
    stream.write("| --- | ---: | ---: | ---: | ---: | ---: |\n")
    for name, result in groups:
        stream.write(
            f"| {name} | {result['campaigns']:,} | {result['cases']:,} | "
            f"{result['value_mismatches']:,} | {result['flag_mismatches']:,} | "
            f"{result['parse_errors']:,} |\n"
        )


def write_summary_markdown(
    path: Path,
    profile: str,
    level: int,
    seed: int,
    rows: list[dict[str, str]],
) -> None:
    result = totals(rows)
    with path.open("w", encoding="utf-8") as stream:
        stream.write("# Berkeley TestFloat result\n\n")
        stream.write("| Profile | Level | Seed | Campaigns | Cases | Value mismatches | ")
        stream.write("Flag mismatches | Parse errors |\n")
        stream.write("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n")
        stream.write(
            f"| {profile} | {level} | {seed} | {result['campaigns']:,} | "
            f"{result['cases']:,} | {result['value_mismatches']:,} | "
            f"{result['flag_mismatches']:,} | {result['parse_errors']:,} |\n"
        )
        write_group_table(stream, "By source format", "Format", grouped(rows, "format"))
        write_group_table(stream, "By operation", "Operation", grouped(rows, "operation"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", required=True, type=Path)
    parser.add_argument("--profile", required=True)
    parser.add_argument("--level", required=True, type=int)
    parser.add_argument("--seed", required=True, type=int)
    args = parser.parse_args()

    rows = read_campaigns(args.results / "results.txt")
    result = totals(rows)
    write_campaigns(args.results / "campaigns.csv", rows)
    write_summary_csv(
        args.results / "summary.csv",
        args.profile,
        args.level,
        args.seed,
        result,
    )
    write_summary_markdown(
        args.results / "summary.md",
        args.profile,
        args.level,
        args.seed,
        rows,
    )


if __name__ == "__main__":
    main()
