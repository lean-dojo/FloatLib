#!/usr/bin/env python3

"""Summarize and plot the latency-oriented cross-format benchmark."""

from __future__ import annotations

import argparse
import csv
import math
import re
import statistics
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "floatlib-format-comparison"


OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
MEASUREMENT_METHOD = "result-dependent-fixture-chain"
MINIMUM_PUBLICATION_TRIALS = 7
REQUIRED_RAW_FIELDS = frozenset(
    {
        "implementation",
        "family",
        "format",
        "totalBits",
        "operation",
        "executionClass",
        "backend",
        "measurementMethod",
        "iterations",
        "totalNanos",
        "sink",
        "fixtureTraceDigest",
        "agreementIterations",
        "agreementSink",
        "agreementFixtureTraceDigest",
    }
)
SERIES_ORDER = (
    "ExecFloat Posit proved software",
    "Stillwater Universal Posit (software)",
    "Stillwater Universal Posit (hardware-assisted)",
    "ExecFloat binary proved software",
    "Berkeley SoftFloat IEEE software",
    "MPFR (binary) software reference",
    "Flocq binary reference (precision model)",
    "Native C IEEE FPU",
    "CPython float64 runtime",
)
SERIES_LABEL = {
    "ExecFloat Posit proved software": "FloatLib posit",
    "Stillwater Universal Posit (software)": "Stillwater Universal posit",
    "Stillwater Universal Posit (hardware-assisted)":
        "Stillwater posit (host sqrt)",
    "ExecFloat binary proved software": "FloatLib binary",
    "Berkeley SoftFloat IEEE software": "Berkeley SoftFloat",
    "MPFR (binary) software reference": "MPFR (binary)",
    "Flocq binary reference (precision model)": "extracted Flocq",
    "Native C IEEE FPU": "native C FPU",
    "CPython float64 runtime": "CPython float64",
}
EXECFLOAT_SERIES = frozenset(
    {
        "ExecFloat Posit proved software",
        "ExecFloat binary proved software",
    }
)
OPERATION_LABEL = {
    "add": "Addition",
    "sub": "Subtraction",
    "mul": "Multiplication",
    "div": "Division",
    "sqrt": "Square root",
    "fma": "Fused multiply-add",
}
SERIES_STYLE = {
    "ExecFloat Posit proved software": {
        "color": "#6d28d9",
        "marker": "o",
        "linestyle": "-",
    },
    "Stillwater Universal Posit (software)": {
        "color": "#db2777",
        "marker": "P",
        "linestyle": "--",
    },
    "Stillwater Universal Posit (hardware-assisted)": {
        "color": "#be185d",
        "marker": "P",
        "linestyle": ":",
        "markerfacecolor": "none",
    },
    "ExecFloat binary proved software": {
        "color": "#1d4ed8",
        "marker": "s",
        "linestyle": "--",
    },
    "Berkeley SoftFloat IEEE software": {
        "color": "#7c3aed",
        "marker": "v",
        "linestyle": "-.",
    },
    "MPFR (binary) software reference": {
        "color": "#c05a12",
        "marker": "^",
        "linestyle": ":",
    },
    "Flocq binary reference (precision model)": {
        "color": "#2f7d32",
        "marker": "D",
        "linestyle": ":",
    },
    "Native C IEEE FPU": {
        "color": "#111827",
        "marker": "D",
        "linestyle": "-.",
    },
    "CPython float64 runtime": {
        "color": "#0891b2",
        "marker": "X",
        "linestyle": "None",
    },
}


@dataclass(frozen=True)
class Key:
    series: str
    implementation: str
    family: str
    format_name: str
    total_bits: int
    operation: str
    execution_class: str


@dataclass(frozen=True)
class Metadata:
    backend: str
    measurement_method: str
    iterations: int
    sink: int
    fixture_trace_digest: int
    agreement_iterations: int
    agreement_sink: int
    agreement_fixture_trace_digest: int


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


@dataclass(frozen=True)
class Summary:
    key: Key
    metadata: Metadata
    timing: Distribution


def series_for(
    implementation: str, family: str, execution_class: str
) -> str:
    mapping = {
        ("posit", "proved-software"): "ExecFloat Posit proved software",
        ("binary-interchange", "proved-software"):
            "ExecFloat binary proved software",
        ("binary-interchange", "native-fpu"): "Native C IEEE FPU",
        ("posit-external", "external-software"):
            "Stillwater Universal Posit (software)",
        ("posit-external", "hardware-assisted-external"):
            "Stillwater Universal Posit (hardware-assisted)",
        ("python-runtime", "dynamic-runtime"): "CPython float64 runtime",
    }
    if (family, execution_class) == ("binary-reference", "software-reference"):
        if implementation == "MPFR":
            return "MPFR (binary) software reference"
        if implementation == "Flocq":
            return "Flocq binary reference (precision model)"
    if (
        implementation == "Berkeley SoftFloat"
        and (family, execution_class)
        == ("binary-interchange", "external-software")
    ):
        return "Berkeley SoftFloat IEEE software"
    try:
        return mapping[(family, execution_class)]
    except KeyError as error:
        raise ValueError(
            f"unknown family/execution class: {family}/{execution_class}"
        ) from error


def percentile(values: list[float], probability: float) -> float:
    if not values:
        raise ValueError("a percentile requires at least one value")
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = probability * (len(ordered) - 1)
    lower = math.floor(position)
    upper = math.ceil(position)
    if lower == upper:
        return ordered[lower]
    fraction = position - lower
    return ordered[lower] * (1.0 - fraction) + ordered[upper] * fraction


def distribution(values: list[float]) -> Distribution:
    median = statistics.median(values)
    deviations = [abs(value - median) for value in values]
    return Distribution(
        trials=len(values),
        minimum=min(values),
        p05=percentile(values, 0.05),
        q1=percentile(values, 0.25),
        median=median,
        mean=statistics.fmean(values),
        q3=percentile(values, 0.75),
        p95=percentile(values, 0.95),
        maximum=max(values),
        standard_deviation=statistics.stdev(values) if len(values) > 1 else 0.0,
        median_absolute_deviation=statistics.median(deviations),
    )


def validate_header(path: Path, fieldnames: list[str] | None) -> None:
    """Reject retired raw files before any summary or plot is produced."""
    if fieldnames is None:
        raise ValueError(f"missing CSV header in {path}")
    duplicate_fields = {
        field for field in fieldnames if fieldnames.count(field) != 1
    }
    if duplicate_fields:
        raise ValueError(
            f"duplicate CSV fields in {path}: {sorted(duplicate_fields)}"
        )
    missing_fields = REQUIRED_RAW_FIELDS.difference(fieldnames)
    if missing_fields:
        raise ValueError(
            f"raw CSV {path} is not a current latency benchmark: "
            f"missing {sorted(missing_fields)}"
        )


def read_trials(
    raw_dir: Path,
) -> tuple[dict[Key, list[float]], dict[Key, Metadata]]:
    samples: dict[Key, list[float]] = defaultdict(list)
    metadata: dict[Key, Metadata] = {}
    expected_keys: set[Key] | None = None
    trial_paths = sorted(raw_dir.glob("trial-*.csv"))
    if not trial_paths:
        raise ValueError(f"no trial CSV files found under {raw_dir}")

    for path in trial_paths:
        seen: set[Key] = set()
        with path.open(newline="", encoding="utf-8") as stream:
            reader = csv.DictReader(stream)
            validate_header(path, reader.fieldnames)
            for row in reader:
                operation = row["operation"]
                if operation not in OPERATIONS:
                    raise ValueError(f"unknown operation in {path}: {operation}")
                measurement_method = row["measurementMethod"]
                if measurement_method != MEASUREMENT_METHOD:
                    raise ValueError(
                        f"unsupported measurement method in {path}: "
                        f"{measurement_method!r}; expected "
                        f"{MEASUREMENT_METHOD!r}"
                    )
                total_bits = int(row["totalBits"])
                iterations = int(row["iterations"])
                total_nanos = int(row["totalNanos"])
                fixture_trace_digest = int(row["fixtureTraceDigest"])
                agreement_iterations = int(row["agreementIterations"])
                agreement_sink = int(row["agreementSink"])
                agreement_fixture_trace_digest = int(
                    row["agreementFixtureTraceDigest"]
                )
                if total_bits <= 0 or iterations <= 0 or total_nanos <= 0:
                    raise ValueError(f"invalid timing row in {path}: {row}")
                if (
                    agreement_iterations < 0
                    or agreement_sink < 0
                    or agreement_fixture_trace_digest < 0
                ):
                    raise ValueError(f"invalid agreement row in {path}: {row}")
                family = row["family"]
                execution_class = row["executionClass"]
                key = Key(
                    series=series_for(
                        row["implementation"], family, execution_class
                    ),
                    implementation=row["implementation"],
                    family=family,
                    format_name=row["format"],
                    total_bits=total_bits,
                    operation=operation,
                    execution_class=execution_class,
                )
                if key in seen:
                    raise ValueError(f"duplicate row in {path}: {key}")
                seen.add(key)
                current_metadata = Metadata(
                    backend=row["backend"],
                    measurement_method=measurement_method,
                    iterations=iterations,
                    sink=int(row["sink"]),
                    fixture_trace_digest=fixture_trace_digest,
                    agreement_iterations=agreement_iterations,
                    agreement_sink=agreement_sink,
                    agreement_fixture_trace_digest=
                        agreement_fixture_trace_digest,
                )
                previous_metadata = metadata.setdefault(key, current_metadata)
                if previous_metadata != current_metadata:
                    raise ValueError(
                        f"metadata, iteration count, or sink changed for {key}: "
                        f"{previous_metadata!r} versus {current_metadata!r}"
                    )
                samples[key].append(total_nanos / iterations)

        if not seen:
            raise ValueError(f"no benchmark rows found in {path}")
        if expected_keys is None:
            expected_keys = seen
        elif seen != expected_keys:
            raise ValueError(
                f"trial key set changed in {path}: "
                f"missing={sorted(expected_keys - seen, key=repr)}, "
                f"extra={sorted(seen - expected_keys, key=repr)}"
            )
    return samples, metadata


def summarize(
    samples: dict[Key, list[float]],
    metadata: dict[Key, Metadata],
) -> list[Summary]:
    return sorted(
        (
            Summary(
                key=key,
                metadata=metadata[key],
                timing=distribution(values),
            )
            for key, values in samples.items()
        ),
        key=lambda row: (
            OPERATIONS.index(row.key.operation),
            row.key.total_bits,
            SERIES_ORDER.index(row.key.series),
        ),
    )


def validate_plot_cells(rows: list[Summary]) -> None:
    """Require one implementation row for each plotted series/width/operation cell."""
    seen: dict[tuple[str, int, str], Key] = {}
    for row in rows:
        cell = (
            row.key.series,
            row.key.total_bits,
            row.key.operation,
        )
        previous = seen.setdefault(cell, row.key)
        if previous != row.key:
            raise ValueError(
                "multiple implementations occupy one plotted cell: "
                f"{previous!r} and {row.key!r}"
            )


def write_summary(path: Path, rows: list[Summary]) -> None:
    fieldnames = [
        "series",
        "implementation",
        "family",
        "format",
        "totalBits",
        "operation",
        "executionClass",
        "backend",
        "measurementMethod",
        "trials",
        "iterations",
        "sink",
        "fixtureTraceDigest",
        "agreementIterations",
        "agreementSink",
        "agreementFixtureTraceDigest",
        "minimumNanosPerOp",
        "p05NanosPerOp",
        "q1NanosPerOp",
        "medianNanosPerOp",
        "meanNanosPerOp",
        "q3NanosPerOp",
        "p95NanosPerOp",
        "maximumNanosPerOp",
        "standardDeviationNanosPerOp",
        "medianAbsoluteDeviationNanosPerOp",
        "medianOperationsPerSecond",
    ]
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            timing = row.timing
            writer.writerow(
                {
                    "series": row.key.series,
                    "implementation": row.key.implementation,
                    "family": row.key.family,
                    "format": row.key.format_name,
                    "totalBits": row.key.total_bits,
                    "operation": row.key.operation,
                    "executionClass": row.key.execution_class,
                    "backend": row.metadata.backend,
                    "measurementMethod": row.metadata.measurement_method,
                    "trials": timing.trials,
                    "iterations": row.metadata.iterations,
                    "sink": row.metadata.sink,
                    "fixtureTraceDigest": row.metadata.fixture_trace_digest,
                    "agreementIterations":
                        row.metadata.agreement_iterations,
                    "agreementSink": row.metadata.agreement_sink,
                    "agreementFixtureTraceDigest":
                        row.metadata.agreement_fixture_trace_digest,
                    "minimumNanosPerOp": f"{timing.minimum:.9f}",
                    "p05NanosPerOp": f"{timing.p05:.9f}",
                    "q1NanosPerOp": f"{timing.q1:.9f}",
                    "medianNanosPerOp": f"{timing.median:.9f}",
                    "meanNanosPerOp": f"{timing.mean:.9f}",
                    "q3NanosPerOp": f"{timing.q3:.9f}",
                    "p95NanosPerOp": f"{timing.p95:.9f}",
                    "maximumNanosPerOp": f"{timing.maximum:.9f}",
                    "standardDeviationNanosPerOp":
                        f"{timing.standard_deviation:.9f}",
                    "medianAbsoluteDeviationNanosPerOp":
                        f"{timing.median_absolute_deviation:.9f}",
                    "medianOperationsPerSecond":
                        f"{1_000_000_000.0 / timing.median:.6f}",
                }
            )


def ratio(numerator: float | None, denominator: float | None) -> str:
    if numerator is None or denominator is None:
        return ""
    return f"{numerator / denominator:.9f}"


def companion_precision(format_name: str) -> str:
    """Extract the explicitly selected MPFR precision when one is present."""

    match = re.fullmatch(r"mpfr-binary\d+-p(\d+)-e\d+", format_name)
    return match.group(1) if match else ""


def write_ratios(path: Path, rows: list[Summary]) -> None:
    medians = {
        (row.key.operation, row.key.total_bits, row.key.series):
            row.timing.median
        for row in rows
    }
    widths = sorted({row.key.total_bits for row in rows})
    fieldnames = [
        "operation",
        "totalBits",
        "comparisonBasis",
        "pairingPolicy",
        "binaryCompanionFormat",
        "binaryCompanionPrecision",
        "execPositOverUniversalSoftware",
        "execPositOverUniversalHardwareAssisted",
        "universalSoftwareOverBinarySoftware",
        "universalSoftwareOverMPFRBinaryCompanion",
        "universalHardwareAssistedOverBinarySoftware",
        "universalHardwareAssistedOverMPFRBinaryCompanion",
        "positOverBinarySoftware",
        "positOverMPFRBinaryCompanion",
        "positOverFlocq",
        "binarySoftwareOverMPFRBinaryCompanion",
        "binarySoftwareOverSoftFloat",
        "softFloatOverMPFR",
        "binarySoftwareOverFlocq",
        "flocqOverMPFR",
        "positOverNativeFPU",
        "binarySoftwareOverNativeFPU",
    ]
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for operation in OPERATIONS:
            for width in widths:
                def get(series: str) -> float | None:
                    return medians.get((operation, width, series))

                posit = get("ExecFloat Posit proved software")
                universal_software = get(
                    "Stillwater Universal Posit (software)"
                )
                universal_hardware = get(
                    "Stillwater Universal Posit (hardware-assisted)"
                )
                binary = get("ExecFloat binary proved software")
                softfloat = get("Berkeley SoftFloat IEEE software")
                mpfr = get("MPFR (binary) software reference")
                flocq = get("Flocq binary reference (precision model)")
                native = get("Native C IEEE FPU")
                binary_companion = next(
                    (
                        row.key.format_name
                        for row in rows
                        if row.key.operation == operation
                        and row.key.total_bits == width
                        and row.key.series
                        == "MPFR (binary) software reference"
                    ),
                    "",
                )
                if (
                    posit is None
                    and binary is None
                    and universal_software is None
                    and universal_hardware is None
                    and softfloat is None
                    and mpfr is None
                    and flocq is None
                    and native is None
                ):
                    continue
                writer.writerow(
                    {
                        "operation": operation,
                        "totalBits": width,
                        "comparisonBasis":
                            "equal storage width; posit precision varies by value",
                        "pairingPolicy":
                            "MPFR uses the binary companion's configured "
                            "significand precision, not a posit precision claim",
                        "binaryCompanionFormat": binary_companion,
                        "binaryCompanionPrecision":
                            companion_precision(binary_companion),
                        "execPositOverUniversalSoftware":
                            ratio(posit, universal_software),
                        "execPositOverUniversalHardwareAssisted":
                            ratio(posit, universal_hardware),
                        "universalSoftwareOverBinarySoftware":
                            ratio(universal_software, binary),
                        "universalSoftwareOverMPFRBinaryCompanion":
                            ratio(universal_software, mpfr),
                        "universalHardwareAssistedOverBinarySoftware":
                            ratio(universal_hardware, binary),
                        "universalHardwareAssistedOverMPFRBinaryCompanion":
                            ratio(universal_hardware, mpfr),
                        "positOverBinarySoftware": ratio(posit, binary),
                        "positOverMPFRBinaryCompanion": ratio(posit, mpfr),
                        "positOverFlocq": ratio(posit, flocq),
                        "binarySoftwareOverMPFRBinaryCompanion":
                            ratio(binary, mpfr),
                        "binarySoftwareOverSoftFloat": ratio(binary, softfloat),
                        "softFloatOverMPFR": ratio(softfloat, mpfr),
                        "binarySoftwareOverFlocq": ratio(binary, flocq),
                        "flocqOverMPFR": ratio(flocq, mpfr),
                        "positOverNativeFPU": ratio(posit, native),
                        "binarySoftwareOverNativeFPU": ratio(binary, native),
                    }
                )


def backend_segments(rows: list[Summary]) -> list[list[Summary]]:
    """Keep a plotted line inside one concrete executable kernel."""
    segments: list[list[Summary]] = []
    current: list[Summary] = []
    current_backend: str | None = None
    for row in rows:
        if current and row.metadata.backend != current_backend:
            segments.append(current)
            current = []
        current.append(row)
        current_backend = row.metadata.backend
    if current:
        segments.append(current)
    return segments


def backend_regime_key(segment: list[Summary]) -> tuple[str, str, int, int, str]:
    """Give one disconnected series segment a stable, human-readable identity."""

    return (
        segment[0].key.series,
        segment[0].key.operation,
        segment[0].key.total_bits,
        segment[-1].key.total_bits,
        segment[0].metadata.backend,
    )


def backend_regime_markers(
    rows: list[Summary],
) -> dict[tuple[str, str, int, int, str], str]:
    """Assign compact plot markers to every concrete executable regime."""

    markers: dict[tuple[str, str, int, int, str], str] = {}
    index = 1
    for operation in OPERATIONS:
        for series in SERIES_ORDER:
            series_rows = sorted(
                (
                    row
                    for row in rows
                    if row.key.operation == operation
                    and row.key.series == series
                ),
                key=lambda row: row.key.total_bits,
            )
            for segment in backend_segments(series_rows):
                markers[backend_regime_key(segment)] = f"R{index:03d}"
                index += 1
    return markers


def write_backend_regimes(path: Path, rows: list[Summary]) -> None:
    """Record the executable backend behind every disconnected plot segment."""
    fieldnames = [
        "series",
        "operation",
        "regimeMarker",
        "firstTotalBits",
        "lastTotalBits",
        "backend",
        "formats",
        "trials",
    ]
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        markers = backend_regime_markers(rows)
        for operation in OPERATIONS:
            for series in SERIES_ORDER:
                series_rows = sorted(
                    (
                        row
                        for row in rows
                        if row.key.operation == operation
                        and row.key.series == series
                    ),
                    key=lambda row: row.key.total_bits,
                )
                for segment in backend_segments(series_rows):
                    writer.writerow(
                        {
                            "series": series,
                            "operation": operation,
                            "regimeMarker":
                                markers[backend_regime_key(segment)],
                            "firstTotalBits": segment[0].key.total_bits,
                            "lastTotalBits": segment[-1].key.total_bits,
                            "backend": segment[0].metadata.backend,
                            "formats": ";".join(
                                row.key.format_name for row in segment
                            ),
                            "trials": segment[0].timing.trials,
                        }
                    )


def render_plot(output_dir: Path, rows: list[Summary]) -> None:
    import matplotlib.pyplot as plt

    matplotlib.rcParams["svg.hashsalt"] = "floatlib-format-comparison"
    series_labels = SERIES_LABEL
    figure, axes = plt.subplots(2, 3, figsize=(15.5, 8.8), sharex=True)
    for axis, operation in zip(axes.flat, OPERATIONS):
        operation_rows = [row for row in rows if row.key.operation == operation]
        for series in SERIES_ORDER:
            series_rows = [
                row for row in operation_rows if row.key.series == series
            ]
            if not series_rows:
                continue
            series_rows.sort(key=lambda row: row.key.total_bits)
            style = SERIES_STYLE[series]
            is_execfloat = series in EXECFLOAT_SERIES
            xs = [row.key.total_bits for row in series_rows]
            medians = [row.timing.median for row in series_rows]
            p05 = [row.timing.p05 for row in series_rows]
            p95 = [row.timing.p95 for row in series_rows]
            axis.plot(
                xs,
                medians,
                label=series_labels[series],
                linewidth=3.4 if is_execfloat else 1.8,
                markersize=6.5 if is_execfloat else 5,
                zorder=4 if is_execfloat else 2,
                **style,
            )
            if any(low != high for low, high in zip(p05, p95)):
                axis.fill_between(
                    xs,
                    p05,
                    p95,
                    color=style["color"],
                    alpha=0.12,
                    linewidth=0,
                )
        axis.set_title(OPERATION_LABEL[operation], fontsize=12)
        axis.set_xscale("log", base=2)
        axis.set_yscale("log")
        widths = {row.key.total_bits for row in operation_rows}
        major_widths = [
            width
            for width in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)
            if width in widths
        ]
        axis.set_xticks(
            major_widths,
            labels=[
                f"{width // 1024}k" if width >= 1024 else str(width)
                for width in major_widths
            ],
        )
        axis.minorticks_off()
        axis.grid(True, which="both", alpha=0.25)

    for axis in axes[:, 0]:
        axis.set_ylabel("Median latency (ns/operation, log scale)")
    for axis in axes[-1, :]:
        axis.set_xlabel("Encoded width (bits, log₂ scale)")

    handles, labels = axes.flat[0].get_legend_handles_labels()
    by_label = dict(zip(labels, handles))
    legend = figure.legend(
        [
            by_label[series_labels[name]]
            for name in SERIES_ORDER
            if series_labels[name] in by_label
        ],
        [
            series_labels[name]
            for name in SERIES_ORDER
            if series_labels[name] in by_label
        ],
        loc="upper center",
        bbox_to_anchor=(0.5, 0.91),
        ncol=4,
        frameon=False,
    )
    for label in legend.get_texts():
        if label.get_text() in {
            series_labels[name] for name in EXECFLOAT_SERIES
        }:
            label.set_fontweight("bold")
    trial_counts = sorted({row.timing.trials for row in rows})
    trial_summary = (
        f"{trial_counts[0]} trials"
        if len(trial_counts) == 1
        else f"{trial_counts[0]}–{trial_counts[-1]} trials"
    )
    title = "FloatLib arithmetic performance from 2 to 4,096 bits"
    subtitle = (
        "Median end-to-end latency across "
        f"{trial_summary}. Lower values are faster."
    )
    if trial_counts[0] < MINIMUM_PUBLICATION_TRIALS:
        subtitle += (
            f" DEVELOPMENT ONLY: public reporting requires "
            f"at least {MINIMUM_PUBLICATION_TRIALS}."
        )
    figure.suptitle(title, y=0.985, fontsize=16, fontweight="bold")
    figure.text(0.5, 0.945, subtitle, ha="center", va="top", fontsize=11)
    figure.text(
        0.5,
        0.015,
        "Markers are measured widths. Lines connect those measurements; "
        "backend changes are recorded separately in backend-regimes.csv.",
        ha="center",
        va="bottom",
        fontsize=9,
        color="#4b5563",
    )
    figure.tight_layout(rect=(0, 0.045, 1, 0.79))
    for suffix in ("png", "svg", "pdf"):
        output_path = output_dir / f"format-comparison.{suffix}"
        metadata = (
            {"Date": None}
            if suffix == "svg"
            else {"CreationDate": None}
            if suffix == "pdf"
            else None
        )
        figure.savefig(
            output_path,
            dpi=180 if suffix == "png" else None,
            metadata=metadata,
        )
        if suffix == "svg":
            lines = output_path.read_text(encoding="utf-8").splitlines()
            output_path.write_text(
                "\n".join(line.rstrip() for line in lines) + "\n",
                encoding="utf-8",
            )
    plt.close(figure)


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Summarize and plot one complete raw format-comparison run."
        )
    )
    parser.add_argument("raw_dir", type=Path)
    parser.add_argument("output_dir", type=Path)
    arguments = parser.parse_args()

    arguments.output_dir.mkdir(parents=True, exist_ok=True)
    samples, metadata = read_trials(arguments.raw_dir)
    rows = summarize(samples, metadata)
    validate_plot_cells(rows)
    write_summary(arguments.output_dir / "summary.csv", rows)
    write_ratios(arguments.output_dir / "ratios.csv", rows)
    write_backend_regimes(arguments.output_dir / "backend-regimes.csv", rows)
    render_plot(arguments.output_dir, rows)


if __name__ == "__main__":
    main()
