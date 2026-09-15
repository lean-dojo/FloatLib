#!/usr/bin/env python3

"""Summarize the public posit benchmark and render backend-aware latency plots."""

from __future__ import annotations

import argparse
import csv
import math
import statistics
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
CANONICAL_BINARY_FORMATS = {
    "binary16",
    "binary32",
    "binary64",
    "binary128",
    "binary256",
}
REFERENCE_PRECISION_TO_WIDTH = {
    2: 2,
    3: 3,
    4: 4,
    5: 5,
    6: 6,
    7: 7,
    8: 8,
    11: 16,
    24: 32,
    53: 64,
    113: 128,
    237: 256,
    493: 512,
}
REFERENCE_LABELS = {
    "ExecFloat configured/descriptor": "ExecFloat IEEE binary (same storage bits)",
    "MPFR (same p)": "MPFR fixed-p reference",
    "Rocq/Flocq (same p)": "Rocq/Flocq fixed-p reference",
}
EXTERNAL_REFERENCE_LABELS = {
    "MPFR": "MPFR fixed-p reference",
    "Rocq/Flocq (extracted)": "Rocq/Flocq fixed-p reference",
}
REFERENCE_STYLES = {
    "ExecFloat IEEE binary (same storage bits)": {
        "color": "#1d4ed8",
        "marker": "s",
        "linestyle": "--",
        "linewidth": 1.6,
        "markersize": 4.5,
    },
    "MPFR fixed-p reference": {
        "color": "#c05a12",
        "marker": "^",
        "linestyle": ":",
        "linewidth": 1.6,
        "markersize": 4.5,
    },
    "Rocq/Flocq fixed-p reference": {
        "color": "#2f7d32",
        "marker": "D",
        "linestyle": ":",
        "linewidth": 1.6,
        "markersize": 4,
    },
}
KERNEL_STYLES = {
    "exhaustive encoded-value table": {
        "color": "#0f766e",
        "marker": "o",
        "label": "Posit: exhaustive encoded-value table",
    },
    "direct packed-word kernel": {
        "color": "#6d28d9",
        "marker": "*",
        "label": "Posit: direct packed-word kernel",
    },
    "direct packed-pair kernel": {
        "color": "#4f46e5",
        "marker": "h",
        "label": "Posit: direct packed-pair kernel",
    },
    "exact-dyadic integer kernel": {
        "color": "#7c3aed",
        "marker": "P",
        "label": "Posit: exact-dyadic integer kernel",
    },
    "exact generic fallback": {
        "color": "#b42318",
        "marker": "X",
        "label": "Posit: exact arbitrary-precision backend",
    },
}
DEFAULT_KERNEL_STYLE = {
    "color": "#7c3aed",
    "marker": "P",
    "label": "Posit: other selected kernel",
}


@dataclass(frozen=True)
class Metadata:
    backend: str
    kernel_class: str
    storage: str
    policy: str
    expected_calls: int


@dataclass(frozen=True)
class RunConfiguration:
    cold_iterations: int
    cold_sink: int
    warmup_iterations: int
    warmup_sink: int
    iterations: int
    sink: int


@dataclass(frozen=True)
class Observation:
    nanos_per_op: float
    cold_nanos_per_op: float


@dataclass(frozen=True)
class Distribution:
    trials: int
    minimum: float
    p05: float
    q1: float
    median: float
    mean: float
    q3: float
    p95: float
    maximum: float
    standard_deviation: float
    median_absolute_deviation: float
    coefficient_of_variation: float


@dataclass(frozen=True)
class SummaryRow:
    operation: str
    total_bits: int
    timing: Distribution
    cold_timing: Distribution
    metadata: Metadata
    run: RunConfiguration


@dataclass(frozen=True)
class ReferencePoint:
    storage_bits: int
    precision: int
    trials: int
    nanos_per_op: float
    backend: str


@dataclass(frozen=True)
class ProcessObservation:
    max_resident_set_kib: int
    major_page_faults: int
    minor_page_faults: int
    user_seconds: float
    system_seconds: float
    elapsed_seconds: float


@dataclass(frozen=True)
class ProcessSummary:
    operation: str
    total_bits: int
    max_resident_set_kib: Distribution
    major_page_faults: Distribution
    minor_page_faults: Distribution
    user_seconds: Distribution
    system_seconds: Distribution
    elapsed_seconds: Distribution


def read_trials(
    raw_dir: Path,
) -> tuple[
    dict[tuple[str, int], list[Observation]],
    dict[tuple[str, int], Metadata],
    dict[tuple[str, int], RunConfiguration],
]:
    samples: dict[tuple[str, int], list[Observation]] = defaultdict(list)
    metadata: dict[tuple[str, int], Metadata] = {}
    configurations: dict[tuple[str, int], RunConfiguration] = {}
    expected_keys: set[tuple[str, int]] | None = None
    for path in sorted(raw_dir.glob("*.csv")):
        seen: set[tuple[str, int]] = set()
        with path.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream):
                if row["implementation"] != "ExecFloat" or row["family"] != "posit":
                    raise ValueError(f"unexpected implementation or family in {path}: {row}")
                operation = row["operation"]
                if operation not in OPERATIONS:
                    raise ValueError(f"unknown operation in {path}: {operation}")
                total_bits = int(row["totalBits"])
                cold_iterations = int(row["coldIterations"])
                cold_nanos = int(row["coldNanos"])
                cold_sink = int(row["coldSink"])
                warmup_iterations = int(row["warmupIterations"])
                warmup_sink = int(row["warmupSink"])
                iterations = int(row["iterations"])
                total_nanos = int(row["totalNanos"])
                sink = int(row["sink"])
                if (
                    total_bits < 2
                    or cold_iterations <= 0
                    or cold_nanos < 0
                    or warmup_iterations <= 0
                    or iterations <= 0
                    or total_nanos < 0
                ):
                    raise ValueError(f"invalid posit benchmark row in {path}: {row}")
                key = (operation, total_bits)
                if key in seen:
                    raise ValueError(f"duplicate {key} row in {path}")
                seen.add(key)
                current = Metadata(
                    backend=row["backend"],
                    kernel_class=row["kernelClass"],
                    storage=row["storage"],
                    policy=row["policy"],
                    expected_calls=int(row["expectedCalls"]),
                )
                previous = metadata.setdefault(key, current)
                if previous != current:
                    raise ValueError(
                        f"dispatch metadata changed for {key}: "
                        f"{previous!r} versus {current!r} in {path}"
                    )
                configuration = RunConfiguration(
                    cold_iterations=cold_iterations,
                    cold_sink=cold_sink,
                    warmup_iterations=warmup_iterations,
                    warmup_sink=warmup_sink,
                    iterations=iterations,
                    sink=sink,
                )
                previous_configuration = configurations.setdefault(key, configuration)
                if previous_configuration != configuration:
                    raise ValueError(
                        f"run counts or observable sinks changed for {key}: "
                        f"{previous_configuration!r} versus {configuration!r} in {path}"
                    )
                samples[key].append(
                    Observation(
                        nanos_per_op=total_nanos / iterations,
                        cold_nanos_per_op=cold_nanos / cold_iterations,
                    )
                )
        if not seen:
            raise ValueError(f"no posit CSV rows found in {path}")
        if expected_keys is None:
            expected_keys = seen
        elif seen != expected_keys:
            missing = sorted(expected_keys - seen)
            extra = sorted(seen - expected_keys)
            raise ValueError(
                f"trial key set changed in {path}: missing={missing}, extra={extra}"
            )
    if not samples:
        raise ValueError(f"no posit CSV rows found under {raw_dir}")
    return samples, metadata, configurations


def read_process_resources(
    path: Path,
) -> dict[tuple[str, int], list[ProcessObservation]]:
    """Read whole-process GNU time counters for fresh, row-isolated invocations."""

    samples: dict[tuple[str, int], list[ProcessObservation]] = defaultdict(list)
    seen_trials: set[tuple[str, str, int]] = set()
    with path.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            if row["totalBits"] == "all" or row["operation"] == "all":
                continue
            operation = row["operation"]
            if operation not in OPERATIONS:
                raise ValueError(f"unknown resource operation in {path}: {operation}")
            total_bits = int(row["totalBits"])
            trial_key = (row["trial"], operation, total_bits)
            if trial_key in seen_trials:
                raise ValueError(f"duplicate process-resource row in {path}: {trial_key}")
            seen_trials.add(trial_key)
            exit_status = int(row["exitStatus"])
            observation = ProcessObservation(
                max_resident_set_kib=int(row["maxResidentSetKiB"]),
                major_page_faults=int(row["majorPageFaults"]),
                minor_page_faults=int(row["minorPageFaults"]),
                user_seconds=float(row["userSeconds"]),
                system_seconds=float(row["systemSeconds"]),
                elapsed_seconds=float(row["elapsedSeconds"]),
            )
            if (
                total_bits < 2
                or exit_status != 0
                or observation.max_resident_set_kib <= 0
                or observation.major_page_faults < 0
                or observation.minor_page_faults < 0
                or observation.user_seconds < 0
                or observation.system_seconds < 0
                or observation.elapsed_seconds < 0
            ):
                raise ValueError(f"invalid process-resource row in {path}: {row}")
            samples[(operation, total_bits)].append(observation)
    return samples


def percentile(values: list[float], fraction: float) -> float:
    """Return a linearly interpolated sample percentile for `0 ≤ fraction ≤ 1`."""

    ordered = sorted(values)
    position = (len(ordered) - 1) * fraction
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def distribution(values: list[float]) -> Distribution:
    if not values:
        raise ValueError("cannot summarize an empty timing distribution")
    median = statistics.median(values)
    mean = statistics.fmean(values)
    standard_deviation = statistics.stdev(values) if len(values) > 1 else 0.0
    median_absolute_deviation = statistics.median(
        abs(value - median) for value in values
    )
    return Distribution(
        trials=len(values),
        minimum=min(values),
        p05=percentile(values, 0.05),
        q1=percentile(values, 0.25),
        median=median,
        mean=mean,
        q3=percentile(values, 0.75),
        p95=percentile(values, 0.95),
        maximum=max(values),
        standard_deviation=standard_deviation,
        median_absolute_deviation=median_absolute_deviation,
        coefficient_of_variation=standard_deviation / mean if mean else 0.0,
    )


def summarize(
    samples: dict[tuple[str, int], list[Observation]],
    metadata: dict[tuple[str, int], Metadata],
    configurations: dict[tuple[str, int], RunConfiguration],
) -> list[SummaryRow]:
    return [
        SummaryRow(
            operation=operation,
            total_bits=total_bits,
            timing=distribution([observation.nanos_per_op for observation in values]),
            cold_timing=distribution(
                [observation.cold_nanos_per_op for observation in values]
            ),
            metadata=metadata[(operation, total_bits)],
            run=configurations[(operation, total_bits)],
        )
        for (operation, total_bits), values in sorted(samples.items())
    ]


def summarize_process_resources(
    samples: dict[tuple[str, int], list[ProcessObservation]],
) -> list[ProcessSummary]:
    return [
        ProcessSummary(
            operation=operation,
            total_bits=total_bits,
            max_resident_set_kib=distribution(
                [float(value.max_resident_set_kib) for value in values]
            ),
            major_page_faults=distribution(
                [float(value.major_page_faults) for value in values]
            ),
            minor_page_faults=distribution(
                [float(value.minor_page_faults) for value in values]
            ),
            user_seconds=distribution([value.user_seconds for value in values]),
            system_seconds=distribution([value.system_seconds for value in values]),
            elapsed_seconds=distribution([value.elapsed_seconds for value in values]),
        )
        for (operation, total_bits), values in sorted(samples.items())
    ]


def write_summary(rows: list[SummaryRow], output: Path) -> None:
    with output.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            (
                "operation",
                "totalBits",
                "trials",
                "iterations",
                "warmupIterations",
                "coldIterations",
                "minNanosPerOp",
                "p05NanosPerOp",
                "q1NanosPerOp",
                "medianNanosPerOp",
                "meanNanosPerOp",
                "q3NanosPerOp",
                "p95NanosPerOp",
                "maxNanosPerOp",
                "standardDeviationNanosPerOp",
                "medianAbsoluteDeviationNanosPerOp",
                "coefficientOfVariation",
                "medianMegaOpsPerSecond",
                "medianColdNanosPerOp",
                "p05ColdNanosPerOp",
                "p95ColdNanosPerOp",
                "backend",
                "kernelClass",
                "storage",
                "policy",
                "expectedCalls",
            )
        )
        for row in rows:
            timing = row.timing
            cold_timing = row.cold_timing
            mega_ops = 1000.0 / timing.median if timing.median else float("inf")
            writer.writerow(
                (
                    row.operation,
                    row.total_bits,
                    timing.trials,
                    row.run.iterations,
                    row.run.warmup_iterations,
                    row.run.cold_iterations,
                    f"{timing.minimum:.6f}",
                    f"{timing.p05:.6f}",
                    f"{timing.q1:.6f}",
                    f"{timing.median:.6f}",
                    f"{timing.mean:.6f}",
                    f"{timing.q3:.6f}",
                    f"{timing.p95:.6f}",
                    f"{timing.maximum:.6f}",
                    f"{timing.standard_deviation:.6f}",
                    f"{timing.median_absolute_deviation:.6f}",
                    f"{timing.coefficient_of_variation:.6f}",
                    f"{mega_ops:.6f}",
                    f"{cold_timing.median:.6f}",
                    f"{cold_timing.p05:.6f}",
                    f"{cold_timing.p95:.6f}",
                    row.metadata.backend,
                    row.metadata.kernel_class,
                    row.metadata.storage,
                    row.metadata.policy,
                    row.metadata.expected_calls,
                )
            )


def write_process_resource_summary(
    rows: list[ProcessSummary], output: Path
) -> None:
    """Write process-level resource distributions without calling them allocations."""

    with output.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            (
                "operation",
                "totalBits",
                "trials",
                "minPeakRssKiB",
                "p05PeakRssKiB",
                "medianPeakRssKiB",
                "p95PeakRssKiB",
                "maxPeakRssKiB",
                "medianMajorPageFaults",
                "medianMinorPageFaults",
                "medianUserSeconds",
                "medianSystemSeconds",
                "medianElapsedSeconds",
                "scope",
            )
        )
        for row in rows:
            rss = row.max_resident_set_kib
            writer.writerow(
                (
                    row.operation,
                    row.total_bits,
                    rss.trials,
                    f"{rss.minimum:.0f}",
                    f"{rss.p05:.0f}",
                    f"{rss.median:.0f}",
                    f"{rss.p95:.0f}",
                    f"{rss.maximum:.0f}",
                    f"{row.major_page_faults.median:.0f}",
                    f"{row.minor_page_faults.median:.0f}",
                    f"{row.user_seconds.median:.6f}",
                    f"{row.system_seconds.median:.6f}",
                    f"{row.elapsed_seconds.median:.6f}",
                    "fresh whole benchmark process; includes Lean startup and inputs",
                )
            )


def write_selection_matrix(rows: list[SummaryRow], output: Path) -> None:
    lookup = {(row.total_bits, row.operation): row for row in rows}
    widths = sorted({row.total_bits for row in rows})
    with output.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(("totalBits", "operation", "storage", "kernelClass", "backend"))
        for width in widths:
            for operation in OPERATIONS:
                row = lookup.get((width, operation))
                if row is None:
                    continue
                writer.writerow(
                    (
                        width,
                        operation,
                        row.metadata.storage,
                        row.metadata.kernel_class,
                        row.metadata.backend,
                    )
                )


def read_reference_summary(
    path: Path | None,
) -> dict[tuple[str, str, int], ReferencePoint]:
    references: dict[tuple[str, str, int], ReferencePoint] = {}
    if path is None:
        return references
    with path.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            if row["format"] not in CANONICAL_BINARY_FORMATS:
                continue
            label = REFERENCE_LABELS.get(row["series"])
            if label is None:
                continue
            operation = row["operation"]
            if operation not in OPERATIONS:
                continue
            storage_bits = int(row["storageBits"])
            references[(label, operation, storage_bits)] = ReferencePoint(
                storage_bits=storage_bits,
                precision=int(row["precision"]),
                trials=int(row["trials"]),
                nanos_per_op=float(row["medianNanosPerOp"]),
                backend=row["backend"],
            )
    return references


def add_external_reference_summaries(
    references: dict[tuple[str, str, int], ReferencePoint],
    paths: list[Path],
) -> None:
    """Add prior MPFR/Flocq summaries without replacing newer named-format rows."""

    for path in paths:
        with path.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream):
                label = EXTERNAL_REFERENCE_LABELS.get(row["series"])
                if label is None:
                    continue
                operation = row["operation"]
                if operation not in OPERATIONS:
                    continue
                precision = int(row["precision"])
                storage_bits = REFERENCE_PRECISION_TO_WIDTH.get(precision)
                if storage_bits is None:
                    continue
                key = (label, operation, storage_bits)
                references.setdefault(
                    key,
                    ReferencePoint(
                        storage_bits=storage_bits,
                        precision=precision,
                        trials=int(row["trials"]),
                        nanos_per_op=float(row["medianNanosPerOp"]),
                        backend=f"{row['series']} p={precision}",
                    ),
                )


def comparison_basis(total_bits: int, precision: int) -> str:
    if total_bits <= 8 and precision == total_bits:
        return (
            "cost baseline only: fixed significand precision p equals posit total "
            "encoding width; represented precision and range are not equivalent"
        )
    return (
        "equal storage width against the benchmark binary format with "
        f"significand precision p={precision}; posit precision is tapered"
    )


def write_reference_comparison(
    rows: list[SummaryRow],
    references: dict[tuple[str, str, int], ReferencePoint],
    output: Path,
) -> None:
    """Record exact ratios and the non-equivalence of every reference match."""

    with output.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            (
                "operation",
                "totalBits",
                "positTrials",
                "positMedianNanosPerOp",
                "positKernelClass",
                "referenceSeries",
                "referencePrecision",
                "referenceTrials",
                "referenceMedianNanosPerOp",
                "positOverReference",
                "comparisonBasis",
                "referenceBackend",
            )
        )
        for row in rows:
            for label in REFERENCE_STYLES:
                reference = references.get((label, row.operation, row.total_bits))
                if reference is None:
                    continue
                writer.writerow(
                    (
                        row.operation,
                        row.total_bits,
                        row.timing.trials,
                        f"{row.timing.median:.6f}",
                        row.metadata.kernel_class,
                        label,
                        reference.precision,
                        reference.trials,
                        f"{reference.nanos_per_op:.6f}",
                        f"{row.timing.median / reference.nanos_per_op:.6f}",
                        comparison_basis(row.total_bits, reference.precision),
                        reference.backend,
                    )
                )


def render(
    rows: list[SummaryRow],
    references: dict[tuple[str, str, int], ReferencePoint],
    output_dir: Path,
) -> None:
    import matplotlib

    matplotlib.rcParams["svg.hashsalt"] = "floatlib-posit"
    import matplotlib.pyplot as plt
    from matplotlib.ticker import NullFormatter

    widths = sorted({row.total_bits for row in rows})
    measured_operations = [
        operation
        for operation in OPERATIONS
        if any(row.operation == operation for row in rows)
    ]
    if not measured_operations:
        raise ValueError("no posit operations available to render")
    columns = min(3, len(measured_operations))
    row_count = math.ceil(len(measured_operations) / columns)
    figure, axes = plt.subplots(
        row_count,
        columns,
        figsize=(5.25 * columns, 4.7 * row_count),
        squeeze=False,
    )
    for axis, operation in zip(axes.flat, measured_operations):
        operation_rows = sorted(
            (row for row in rows if row.operation == operation),
            key=lambda row: row.total_bits,
        )

        axis.plot(
            [row.total_bits for row in operation_rows],
            [row.timing.median for row in operation_rows],
            color="#64748b",
            linewidth=1.3,
            alpha=0.75,
            zorder=1,
        )
        axis.errorbar(
            [row.total_bits for row in operation_rows],
            [row.timing.median for row in operation_rows],
            yerr=(
                [row.timing.median - row.timing.p05 for row in operation_rows],
                [row.timing.p95 - row.timing.median for row in operation_rows],
            ),
            fmt="none",
            ecolor="#94a3b8",
            elinewidth=1.0,
            capsize=2.0,
            alpha=0.8,
            zorder=2,
        )
        kernel_classes = {row.metadata.kernel_class for row in operation_rows}
        for kernel_class in sorted(kernel_classes):
            style = KERNEL_STYLES.get(kernel_class, DEFAULT_KERNEL_STYLE)
            points = [
                row for row in operation_rows if row.metadata.kernel_class == kernel_class
            ]
            axis.scatter(
                [row.total_bits for row in points],
                [row.timing.median for row in points],
                color=style["color"],
                marker=style["marker"],
                s=37,
                label=style["label"],
                zorder=3,
            )

        for label, style in REFERENCE_STYLES.items():
            points = sorted(
                (
                    point
                    for (point_label, point_operation, _), point in references.items()
                    if point_label == label and point_operation == operation
                ),
                key=lambda point: point.storage_bits,
            )
            if points:
                axis.plot(
                    [point.storage_bits for point in points],
                    [point.nanos_per_op for point in points],
                    label=label,
                    **style,
                )

        axis.set_title(operation.upper())
        axis.set_xscale("log", base=2)
        axis.set_yscale("log")
        axis.set_xticks(widths, labels=[str(width) for width in widths])
        axis.xaxis.set_minor_formatter(NullFormatter())
        axis.tick_params(axis="x", labelsize=7.1, labelrotation=37)
        axis.set_xlabel("total posit encoding width (bits)")
        axis.set_ylabel("median ns/op")
        axis.grid(True, which="both", color="#d8dde3", linewidth=0.7)
    for axis in list(axes.flat)[len(measured_operations) :]:
        axis.set_visible(False)

    handles_by_label = {}
    for axis in axes.flat:
        handles, labels = axis.get_legend_handles_labels()
        for handle, label in zip(handles, labels):
            handles_by_label.setdefault(label, handle)
    legend_order = (
        "Posit: exhaustive encoded-value table",
        "Posit: direct packed-word kernel",
        "Posit: exact-dyadic integer kernel",
        "Posit: exact arbitrary-precision backend",
        "Posit: other selected kernel",
        "ExecFloat IEEE binary (same storage bits)",
        "MPFR fixed-p reference",
        "Rocq/Flocq fixed-p reference",
    )
    labels = [label for label in legend_order if label in handles_by_label]
    figure.legend(
        [handles_by_label[label] for label in labels],
        labels,
        loc="lower center",
        ncol=min(4, len(labels)),
        frameon=False,
        bbox_to_anchor=(0.5, 0.012),
    )
    figure.suptitle(
        "Configured ExecFloat Posit Arithmetic by Total Encoding Width",
        fontsize=16,
        y=0.987,
    )
    figure.text(
        0.5,
        0.105,
        "Every point measures the public type-static ExecFloat API. Marker shape records the "
        "certified backend; vertical bars span the trial p05 to p95 interval.",
        ha="center",
        fontsize=8.5,
        color="#374151",
    )
    figure.text(
        0.5,
        0.086,
        "Posit precision is tapered. References at 2 to 8 bits use p=n only as a cost baseline; "
        "16 to 512 bit references use the equal-storage binary format's p. Neither is accuracy-equivalent.",
        ha="center",
        fontsize=8.5,
        color="#4b5563",
    )
    figure.subplots_adjust(
        left=0.07,
        right=0.985,
        top=0.925,
        bottom=0.21 if row_count > 1 else 0.31,
        wspace=0.24,
        hspace=0.37,
    )
    figure.savefig(output_dir / "posit_speed_by_width.png", dpi=220)
    figure.savefig(
        output_dir / "posit_speed_by_width.svg",
        metadata={"Date": None},
    )
    plt.close(figure)


def render_process_resources(
    rows: list[ProcessSummary], output_dir: Path
) -> None:
    """Plot peak whole-process RSS separately from arithmetic latency."""

    if not rows:
        return
    import matplotlib

    matplotlib.rcParams["svg.hashsalt"] = "floatlib-posit-process-resources"
    import matplotlib.pyplot as plt
    from matplotlib.ticker import NullFormatter

    figure, axis = plt.subplots(figsize=(10.5, 5.8))
    widths = sorted({row.total_bits for row in rows})
    for operation in OPERATIONS:
        points = sorted(
            (row for row in rows if row.operation == operation),
            key=lambda row: row.total_bits,
        )
        if not points:
            continue
        axis.errorbar(
            [row.total_bits for row in points],
            [row.max_resident_set_kib.median / 1024.0 for row in points],
            yerr=(
                [
                    (row.max_resident_set_kib.median - row.max_resident_set_kib.p05)
                    / 1024.0
                    for row in points
                ],
                [
                    (row.max_resident_set_kib.p95 - row.max_resident_set_kib.median)
                    / 1024.0
                    for row in points
                ],
            ),
            marker="o",
            linewidth=1.4,
            capsize=2.0,
            label=operation.upper(),
        )
    axis.set_xscale("log", base=2)
    axis.set_xticks(widths, labels=[str(width) for width in widths])
    axis.xaxis.set_minor_formatter(NullFormatter())
    axis.tick_params(axis="x", labelsize=7.5, labelrotation=37)
    axis.set_xlabel("total posit encoding width (bits)")
    axis.set_ylabel("median peak process RSS (MiB)")
    axis.set_title("ExecFloat Posit Fresh-Process Memory Footprint")
    axis.grid(True, which="both", color="#d8dde3", linewidth=0.7)
    axis.legend(ncol=3, frameon=False)
    figure.text(
        0.5,
        0.012,
        "GNU time peak RSS includes Lean startup, static data, input construction, cold work, "
        "warmup, and timing. It is not per-operation allocation.",
        ha="center",
        fontsize=8.5,
        color="#4b5563",
    )
    figure.subplots_adjust(left=0.09, right=0.985, top=0.91, bottom=0.19)
    figure.savefig(output_dir / "posit_peak_process_rss_by_width.png", dpi=220)
    figure.savefig(
        output_dir / "posit_peak_process_rss_by_width.svg",
        metadata={"Date": None},
    )
    plt.close(figure)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw_dir", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument(
        "--named-format-summary",
        type=Path,
        help=(
            "optional named-format-summary.csv providing same-storage binary and "
            "IEEE-precision MPFR/Flocq reference points"
        ),
    )
    parser.add_argument(
        "--external-summary",
        type=Path,
        action="append",
        default=[],
        help=(
            "optional external-summary.csv with prior MPFR or extracted Flocq "
            "medians; may be repeated"
        ),
    )
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    samples, metadata, configurations = read_trials(args.raw_dir)
    rows = summarize(samples, metadata, configurations)
    write_summary(rows, args.output_dir / "posit-summary.csv")
    write_selection_matrix(rows, args.output_dir / "posit-backend-selection.csv")
    references = read_reference_summary(args.named_format_summary)
    add_external_reference_summaries(references, args.external_summary)
    write_reference_comparison(
        rows,
        references,
        args.output_dir / "posit-reference-comparison.csv",
    )
    render(rows, references, args.output_dir)
    resource_path = args.raw_dir.parent / "resources" / "process.csv"
    if resource_path.is_file():
        resource_rows = summarize_process_resources(
            read_process_resources(resource_path)
        )
        if resource_rows:
            write_process_resource_summary(
                resource_rows,
                args.output_dir / "posit-process-resources.csv",
            )
            render_process_resources(resource_rows, args.output_dir)


if __name__ == "__main__":
    main()
