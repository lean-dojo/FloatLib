#!/usr/bin/env python3

"""Summarize and plot configured Binary32/Binary64 public-versus-direct trials."""

from __future__ import annotations

import argparse
import csv
import math
import statistics
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
IMPLEMENTATIONS = ("ConfiguredPublic", "ConfiguredDirect")


@dataclass(frozen=True)
class Sample:
    nanos_per_operation: float
    sink: str
    execution_class: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw", type=Path, help="directory containing trial-*.csv")
    parser.add_argument("output", type=Path, help="output directory")
    return parser.parse_args()


def percentile(values: list[float], fraction: float) -> float:
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = fraction * (len(ordered) - 1)
    lower = math.floor(position)
    upper = math.ceil(position)
    if lower == upper:
        return ordered[lower]
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def read_trials(
    raw: Path,
) -> dict[tuple[int, str, str], list[Sample]]:
    samples: dict[tuple[int, str, str], list[Sample]] = defaultdict(list)
    trial_paths = sorted(raw.glob("trial-*.csv"))
    if not trial_paths:
        raise SystemExit(f"no trial-*.csv files found in {raw}")

    expected = {
        (width, operation, implementation)
        for width in (32, 64)
        for operation in OPERATIONS
        for implementation in IMPLEMENTATIONS
    }

    for path in trial_paths:
        seen: set[tuple[int, str, str]] = set()
        with path.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream):
                width = int(row["width"])
                implementation = row["implementation"]
                operation = row["operation"]
                key = (width, operation, implementation)
                if key not in expected:
                    raise SystemExit(f"unexpected row in {path}: {row}")
                if key in seen:
                    raise SystemExit(f"duplicate {key} row in {path}")
                seen.add(key)
                iterations = int(row["iterations"])
                total_nanos = int(row["totalNanos"])
                if iterations <= 0 or total_nanos <= 0:
                    raise SystemExit(f"invalid timing row in {path}: {row}")
                samples[key].append(
                    Sample(
                        nanos_per_operation=total_nanos / iterations,
                        sink=row["sink"],
                        execution_class=row["executionClass"],
                    )
                )
        if seen != expected:
            missing = sorted(expected - seen)
            raise SystemExit(f"{path} is missing rows: {missing}")

    for width in (32, 64):
        for operation in OPERATIONS:
            public = samples[(width, operation, "ConfiguredPublic")]
            direct = samples[(width, operation, "ConfiguredDirect")]
            if len(public) != len(trial_paths) or len(direct) != len(trial_paths):
                raise SystemExit(f"incomplete samples for binary{width} {operation}")
            if {sample.sink for sample in public} != {sample.sink for sample in direct}:
                raise SystemExit(f"sink mismatch for binary{width} {operation}")
            if (
                {sample.execution_class for sample in public}
                != {sample.execution_class for sample in direct}
            ):
                raise SystemExit(f"execution-class mismatch for binary{width} {operation}")

    return samples


def summarize(values: list[float]) -> dict[str, float]:
    median = statistics.median(values)
    deviations = [abs(value - median) for value in values]
    return {
        "minimum": min(values),
        "q1": percentile(values, 0.25),
        "median": median,
        "mean": statistics.fmean(values),
        "q3": percentile(values, 0.75),
        "maximum": max(values),
        "standard_deviation": statistics.stdev(values) if len(values) > 1 else 0.0,
        "median_absolute_deviation": statistics.median(deviations),
    }


def write_tables(
    output: Path,
    samples: dict[tuple[int, str, str], list[Sample]],
) -> dict[tuple[int, str, str], dict[str, float]]:
    summaries = {
        key: summarize([sample.nanos_per_operation for sample in values])
        for key, values in samples.items()
    }
    output.mkdir(parents=True, exist_ok=True)

    with (output / "summary.csv").open("w", newline="", encoding="utf-8") as stream:
        fieldnames = [
            "width",
            "operation",
            "implementation",
            "executionClass",
            "trials",
            "minimumNanosPerOp",
            "q1NanosPerOp",
            "medianNanosPerOp",
            "meanNanosPerOp",
            "q3NanosPerOp",
            "maximumNanosPerOp",
            "standardDeviationNanosPerOp",
            "medianAbsoluteDeviationNanosPerOp",
            "medianOperationsPerSecond",
        ]
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        for width in (32, 64):
            for operation in OPERATIONS:
                for implementation in IMPLEMENTATIONS:
                    key = (width, operation, implementation)
                    summary = summaries[key]
                    execution_class = samples[key][0].execution_class
                    writer.writerow(
                        {
                            "width": width,
                            "operation": operation,
                            "implementation": implementation,
                            "executionClass": execution_class,
                            "trials": len(samples[key]),
                            "minimumNanosPerOp": f"{summary['minimum']:.9f}",
                            "q1NanosPerOp": f"{summary['q1']:.9f}",
                            "medianNanosPerOp": f"{summary['median']:.9f}",
                            "meanNanosPerOp": f"{summary['mean']:.9f}",
                            "q3NanosPerOp": f"{summary['q3']:.9f}",
                            "maximumNanosPerOp": f"{summary['maximum']:.9f}",
                            "standardDeviationNanosPerOp": (
                                f"{summary['standard_deviation']:.9f}"
                            ),
                            "medianAbsoluteDeviationNanosPerOp": (
                                f"{summary['median_absolute_deviation']:.9f}"
                            ),
                            "medianOperationsPerSecond": (
                                f"{1_000_000_000 / summary['median']:.3f}"
                            ),
                        }
                    )

    with (output / "ratios.csv").open("w", newline="", encoding="utf-8") as stream:
        fieldnames = [
            "width",
            "operation",
            "publicMedianNanosPerOp",
            "directMedianNanosPerOp",
            "publicOverDirect",
            "publicOverheadPercent",
        ]
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        for width in (32, 64):
            for operation in OPERATIONS:
                public = summaries[(width, operation, "ConfiguredPublic")]["median"]
                direct = summaries[(width, operation, "ConfiguredDirect")]["median"]
                ratio = public / direct
                writer.writerow(
                    {
                        "width": width,
                        "operation": operation,
                        "publicMedianNanosPerOp": f"{public:.9f}",
                        "directMedianNanosPerOp": f"{direct:.9f}",
                        "publicOverDirect": f"{ratio:.9f}",
                        "publicOverheadPercent": f"{(ratio - 1.0) * 100:.6f}",
                    }
                )

    return summaries


def plot(
    output: Path,
    summaries: dict[tuple[int, str, str], dict[str, float]],
) -> None:
    figure, axes = plt.subplots(2, 2, figsize=(13.0, 8.0), constrained_layout=True)
    colors = {
        "ConfiguredPublic": "#1768ac",
        "ConfiguredDirect": "#f28e2b",
    }
    x_values = list(range(len(OPERATIONS)))
    bar_width = 0.38

    for column, width in enumerate((32, 64)):
        latency_axis = axes[0][column]
        ratio_axis = axes[1][column]
        for offset, implementation in zip((-0.5, 0.5), IMPLEMENTATIONS):
            medians = [
                summaries[(width, operation, implementation)]["median"]
                for operation in OPERATIONS
            ]
            lower = [
                summaries[(width, operation, implementation)]["median"]
                - summaries[(width, operation, implementation)]["q1"]
                for operation in OPERATIONS
            ]
            upper = [
                summaries[(width, operation, implementation)]["q3"]
                - summaries[(width, operation, implementation)]["median"]
                for operation in OPERATIONS
            ]
            positions = [x + offset * bar_width for x in x_values]
            latency_axis.bar(
                positions,
                medians,
                width=bar_width,
                color=colors[implementation],
                label=implementation,
                yerr=[lower, upper],
                capsize=2,
            )

        ratios = [
            summaries[(width, operation, "ConfiguredPublic")]["median"]
            / summaries[(width, operation, "ConfiguredDirect")]["median"]
            for operation in OPERATIONS
        ]
        ratio_axis.axhline(1.0, color="#333333", linewidth=1.0, linestyle="--")
        ratio_axis.plot(
            x_values,
            ratios,
            marker="o",
            linewidth=1.8,
            color=colors["ConfiguredPublic"],
        )
        spread = max(max(abs(ratio - 1.0) for ratio in ratios), 0.02)
        ratio_axis.set_ylim(1.0 - spread * 1.25, 1.0 + spread * 1.25)

        latency_axis.set_title(f"Configured binary{width}")
        latency_axis.set_ylabel("median ns / operation")
        latency_axis.set_yscale("log")
        latency_axis.set_xticks(x_values, OPERATIONS)
        latency_axis.grid(axis="y", alpha=0.25)
        ratio_axis.set_ylabel("public / direct")
        ratio_axis.set_xticks(x_values, OPERATIONS)
        ratio_axis.grid(axis="y", alpha=0.25)

    axes[0][0].legend(loc="upper left")
    figure.suptitle(
        "Configured ExecFloat dispatch equality\n"
        "Identical inputs, monomorphic loops, and verified result sinks",
        fontsize=14,
    )
    for extension in ("png", "svg", "pdf"):
        figure.savefig(output / f"configured_binary_dispatch.{extension}", dpi=180)
    plt.close(figure)


def main() -> None:
    args = parse_args()
    samples = read_trials(args.raw)
    summaries = write_tables(args.output, samples)
    plot(args.output, summaries)


if __name__ == "__main__":
    main()
