#!/usr/bin/env python3

"""Verify that a retained benchmark is the complete public release matrix."""

from __future__ import annotations

import argparse
import csv
import hashlib
import math
import re
from pathlib import Path

WIDTHS = (2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)
OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
LANES = (
    "posit-software",
    "binary-software",
    "binary-native-c",
    "mpfr-reference",
    "softfloat-reference",
    "cpython-float64",
    "universal-posit",
    "flocq-reference",
)
MEASUREMENT_METHOD = "result-dependent-fixture-chain"
TRIALS = 9
AGREEMENT_ITERATIONS = 256

RAW_HEADER = [
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
]
CALIBRATION_HEADER = [
    "lane",
    "totalBits",
    "operation",
    "pilotIterations",
    "pilotNanos",
    "targetNanos",
    "selectedIterations",
    "pilotSink",
]
PREFLIGHT_HEADER = [
    "library",
    "totalBits",
    "operation",
    "status",
    "diagnosticFile",
]
RESOURCE_HEADER = [
    "trial",
    "lane",
    "totalBits",
    "operation",
    "maxResidentSetKiB",
    "majorPageFaults",
    "minorPageFaults",
    "userSeconds",
    "systemSeconds",
    "elapsedSeconds",
    "exitStatus",
]
TRIAL_ORDER_HEADER = [
    "trial",
    "orderIndex",
    "lane",
    "totalBits",
    "operation",
]
BACKEND_SELECTION_HEADER = [
    "family",
    "format",
    "storageBits",
    "maximumSignificandBits",
    "operation",
    "candidateCount",
    "selected",
    "kernelClass",
    "residentBytes",
    "policy",
    "expectedCalls",
    "maxResidentBytes",
    "warmCost",
    "coldCost",
    "score",
]
EXPECTED_UNIVERSAL_REJECTIONS = {
    (width, "sqrt") for width in (64, 128, 256, 512, 1024, 2048, 4096)
}
DIRECT_BINARY_WORD_WIDTHS = {32, 64}
SELECTION_MATRIX_BINARY_WIDTHS = {4, 5, 6, 7, 8, 16, 128, 256, 512}
AGREEMENT_LANES = {
    "binary-software",
    "binary-native-c",
    "mpfr-reference",
    "softfloat-reference",
    "cpython-float64",
}


def read_metadata(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        if key in values:
            raise ValueError(f"duplicate metadata key at {path}:{line_number}: {key}")
        values[key] = value
    return values


def require(metadata: dict[str, str], key: str, expected: str) -> None:
    actual = metadata.get(key)
    if actual != expected:
        raise ValueError(
            f"benchmark metadata {key!r} differs: expected {expected!r}, got {actual!r}"
        )


def read_rows(path: Path, header: list[str]) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != header:
            raise ValueError(
                f"unexpected CSV header in {path}: {reader.fieldnames!r}"
            )
        return list(reader)


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def parse_nonnegative(
    row: dict[str, str],
    field: str,
    path: Path,
) -> int:
    try:
        value = int(row[field])
    except ValueError as error:
        raise ValueError(
            f"non-integer {field} in {path}: {row[field]!r}"
        ) from error
    if value < 0:
        raise ValueError(f"negative {field} in {path}: {value}")
    return value


def parse_positive(row: dict[str, str], field: str, path: Path) -> int:
    value = parse_nonnegative(row, field, path)
    if value <= 0:
        raise ValueError(f"non-positive {field} in {path}: {value}")
    return value


def lane_for(row: dict[str, str], path: Path) -> str:
    identity = (
        row["implementation"],
        row["family"],
        row["executionClass"],
    )
    lanes = {
        ("ExecFloat", "posit", "proved-software"): "posit-software",
        (
            "ExecFloat",
            "binary-interchange",
            "proved-software",
        ): "binary-software",
        ("Native C", "binary-interchange", "native-fpu"): "binary-native-c",
        ("MPFR", "binary-reference", "software-reference"): "mpfr-reference",
        (
            "Berkeley SoftFloat",
            "binary-interchange",
            "external-software",
        ): "softfloat-reference",
        ("CPython", "python-runtime", "dynamic-runtime"): "cpython-float64",
        (
            "Stillwater Universal",
            "posit-external",
            "external-software",
        ): "universal-posit",
        (
            "Stillwater Universal",
            "posit-external",
            "hardware-assisted-external",
        ): "universal-posit",
        ("Flocq", "binary-reference", "software-reference"): "flocq-reference",
    }
    try:
        return lanes[identity]
    except KeyError as error:
        raise ValueError(f"unknown benchmark lane in {path}: {identity!r}") from error


def read_universal_preflight(
    benchmark: Path,
) -> dict[tuple[int, str], str]:
    path = benchmark / "environment" / "external-posit-conformance.csv"
    rows = read_rows(path, PREFLIGHT_HEADER)
    expected = {
        (width, operation)
        for width in WIDTHS
        if width >= 5
        for operation in OPERATIONS
    }
    statuses: dict[tuple[int, str], str] = {}
    for row in rows:
        if row["library"] != "Stillwater Universal":
            raise ValueError(f"unexpected preflight library in {path}: {row!r}")
        key = (parse_positive(row, "totalBits", path), row["operation"])
        if key in statuses:
            raise ValueError(f"duplicate Universal preflight cell in {path}: {key}")
        if row["status"] not in {"pass", "reject"}:
            raise ValueError(f"unknown Universal preflight status in {path}: {row!r}")
        diagnostic = row["diagnosticFile"]
        if (
            not diagnostic
            or Path(diagnostic).name != diagnostic
            or not (path.parent / diagnostic).is_file()
        ):
            raise ValueError(
                f"missing or unsafe Universal diagnostic in {path}: {diagnostic!r}"
            )
        statuses[key] = row["status"]
    if set(statuses) != expected:
        raise ValueError(
            "Universal preflight grid differs: "
            f"missing={sorted(expected - set(statuses))}, "
            f"extra={sorted(set(statuses) - expected)}"
        )
    rejected = {key for key, status in statuses.items() if status == "reject"}
    if rejected != EXPECTED_UNIVERSAL_REJECTIONS:
        raise ValueError(
            "Universal rejection set differs: "
            f"expected={sorted(EXPECTED_UNIVERSAL_REJECTIONS)}, "
            f"actual={sorted(rejected)}"
        )
    for key, status in statuses.items():
        width, operation = key
        diagnostic = (
            path.parent / f"universal-{width}-{operation}.txt"
        ).read_text(encoding="utf-8")
        if status == "pass" and diagnostic:
            raise ValueError(
                f"passing Universal preflight emitted a diagnostic at {key}"
            )
        if status == "reject" and not diagnostic.startswith(
            (
                "Stillwater Universal disagrees with FloatLib for posit",
                # Retained campaign diagnostics are immutable evidence.
                "Stillwater Universal disagrees with LeanFloat for posit",
            )
        ):
            raise ValueError(
                f"Universal rejection lacks the expected disagreement at {key}"
            )
    return statuses


def expected_cells(
    python_has_fma: bool,
    universal: dict[tuple[int, str], str],
) -> set[tuple[str, int, str]]:
    cells: set[tuple[str, int, str]] = set()
    for width in WIDTHS:
        for operation in OPERATIONS:
            cells.add(("posit-software", width, operation))
            if width >= 4:
                cells.add(("binary-software", width, operation))
                cells.add(("mpfr-reference", width, operation))
                cells.add(("flocq-reference", width, operation))
            if width in {32, 64}:
                cells.add(("binary-native-c", width, operation))
                cells.add(("softfloat-reference", width, operation))
            if width == 64 and (operation != "fma" or python_has_fma):
                cells.add(("cpython-float64", width, operation))
            if universal.get((width, operation)) == "pass":
                cells.add(("universal-posit", width, operation))
    return cells


def verify_agreement_fields(
    row: dict[str, str],
    lane: str,
    expected_iterations: int,
    path: Path,
) -> tuple[int, int, int]:
    values = (
        parse_nonnegative(row, "agreementIterations", path),
        parse_nonnegative(row, "agreementSink", path),
        parse_nonnegative(row, "agreementFixtureTraceDigest", path),
    )
    if lane in AGREEMENT_LANES:
        if values[0] != expected_iterations:
            raise ValueError(
                f"agreement prefix length differs in {path} for {lane}: "
                f"{values[0]} != {expected_iterations}"
            )
    elif values != (0, 0, 0):
        raise ValueError(
            f"non-comparable lane reports binary agreement data in {path} "
            f"for {lane}: {values!r}"
        )
    return values


def verify_binary_agreement_matrix(
    values: dict[
        tuple[int, str],
        dict[str, tuple[int, int, int]],
    ],
    context: str,
) -> None:
    expected_cells = {
        (width, operation)
        for width in WIDTHS
        if width >= 4
        for operation in OPERATIONS
    }
    if set(values) != expected_cells:
        raise ValueError(
            f"binary agreement grid differs in {context}: "
            f"missing={sorted(expected_cells - set(values))}, "
            f"extra={sorted(set(values) - expected_cells)}"
        )
    for cell, lane_values in values.items():
        required = {"binary-software", "mpfr-reference"}
        if not required.issubset(lane_values):
            raise ValueError(
                f"binary agreement lacks core adapters in {context} at {cell}: "
                f"{sorted(lane_values)}"
            )
        if len(set(lane_values.values())) != 1:
            raise ValueError(
                f"binary agreement differs in {context} at {cell}: "
                f"{lane_values!r}"
            )


def verify_calibration(
    benchmark: Path,
    expected: set[tuple[str, int, str]],
    minimum_nanos: int,
    target_nanos: int,
    agreement_iterations: int,
) -> dict[tuple[str, int, str], int]:
    path = benchmark / "calibration" / "selected-iterations.csv"
    rows = read_rows(path, CALIBRATION_HEADER)
    selected: dict[tuple[str, int, str], int] = {}
    agreement: dict[
        tuple[int, str],
        dict[str, tuple[int, int, int]],
    ] = {}
    for row in rows:
        key = (
            row["lane"],
            parse_positive(row, "totalBits", path),
            row["operation"],
        )
        if key in selected:
            raise ValueError(f"duplicate calibration cell in {path}: {key}")
        if row["lane"] not in LANES or row["operation"] not in OPERATIONS:
            raise ValueError(f"unknown calibration cell in {path}: {key}")
        pilot_iterations = parse_positive(row, "pilotIterations", path)
        pilot_nanos = parse_positive(row, "pilotNanos", path)
        target = parse_positive(row, "targetNanos", path)
        if target != target_nanos:
            raise ValueError(
                f"calibration target differs from metadata at {key}: "
                f"{target} != {target_nanos}"
            )
        if target < minimum_nanos:
            raise ValueError(
                f"calibration target is below the publication floor at {key}: "
                f"{target} < {minimum_nanos}"
            )
        try:
            int(row["pilotSink"])
        except ValueError as error:
            raise ValueError(
                f"non-integer pilotSink in {path}: {row['pilotSink']!r}"
            ) from error
        selected_iterations = parse_positive(row, "selectedIterations", path)
        calculated = max(
            1,
            min(
                math.ceil(target * pilot_iterations / pilot_nanos),
                50_000_000,
            ),
        )
        if selected_iterations != calculated:
            raise ValueError(
                f"selected iteration formula differs at {key}: "
                f"{selected_iterations} != {calculated}"
            )
        pilot_path = (
            benchmark
            / "calibration"
            / f"pilot-{key[0]}-{key[1]}-{key[2]}.csv"
        )
        pilot_rows = read_rows(pilot_path, RAW_HEADER)
        if len(pilot_rows) != 1:
            raise ValueError(f"expected one pilot row in {pilot_path}")
        pilot_row = pilot_rows[0]
        pilot_key = (
            lane_for(pilot_row, pilot_path),
            parse_positive(pilot_row, "totalBits", pilot_path),
            pilot_row["operation"],
        )
        if pilot_key != key:
            raise ValueError(
                f"pilot cell differs in {pilot_path}: {pilot_key} != {key}"
            )
        if pilot_row["measurementMethod"] != MEASUREMENT_METHOD:
            raise ValueError(
                f"wrong pilot measurement method in {pilot_path}"
            )
        if parse_positive(pilot_row, "iterations", pilot_path) != pilot_iterations:
            raise ValueError(f"pilot iteration count differs in {pilot_path}")
        if parse_positive(pilot_row, "totalNanos", pilot_path) != pilot_nanos:
            raise ValueError(f"pilot elapsed time differs in {pilot_path}")
        if int(pilot_row["sink"]) != int(row["pilotSink"]):
            raise ValueError(f"pilot sink differs in {pilot_path}")
        int(pilot_row["fixtureTraceDigest"])
        lane_agreement = verify_agreement_fields(
            pilot_row,
            key[0],
            agreement_iterations,
            pilot_path,
        )
        if key[0] in AGREEMENT_LANES:
            agreement.setdefault((key[1], key[2]), {})[key[0]] = lane_agreement
        selected[key] = selected_iterations
    if set(selected) != expected:
        raise ValueError(
            "calibration matrix differs: "
            f"missing={sorted(expected - set(selected))}, "
            f"extra={sorted(set(selected) - expected)}"
        )
    expected_pilots = {
        f"pilot-{lane}-{width}-{operation}.csv"
        for lane, width, operation in expected
    }
    actual_pilots = {
        candidate.name
        for candidate in (benchmark / "calibration").glob("pilot-*.csv")
    }
    if actual_pilots != expected_pilots:
        raise ValueError(
            "calibration pilot files differ: "
            f"missing={sorted(expected_pilots - actual_pilots)}, "
            f"extra={sorted(actual_pilots - expected_pilots)}"
        )
    verify_binary_agreement_matrix(agreement, "calibration pilots")
    return selected


def verify_row_identity(
    row: dict[str, str],
    lane: str,
    width: int,
    operation: str,
    path: Path,
) -> None:
    if operation not in OPERATIONS:
        raise ValueError(f"unknown operation in {path}: {operation!r}")
    if width not in WIDTHS:
        raise ValueError(f"unknown width in {path}: {width}")
    if not row["format"] or not row["backend"]:
        raise ValueError(f"empty format or backend in {path}")
    expected_formats = {
        "posit-software": rf"posit{width}",
        "binary-software": rf"binary{width}(?:-[a-z0-9-]+)?",
        "binary-native-c": rf"binary{width}",
        "mpfr-reference": rf"mpfr-binary{width}-p[0-9]+-e[0-9]+",
        "softfloat-reference": rf"binary{width}",
        "cpython-float64": r"python-float64",
        "universal-posit": rf"posit{width}-es2",
        "flocq-reference": r"flocq-p[0-9]+",
    }
    if re.fullmatch(expected_formats[lane], row["format"]) is None:
        raise ValueError(
            f"unexpected format for {lane} in {path}: {row['format']!r}"
        )
    backend_fragments = {
        "binary-native-c": "host",
        "mpfr-reference": "MPFR",
        "softfloat-reference": "SoftFloat",
        "cpython-float64": "CPython",
        "universal-posit": "Universal",
        "flocq-reference": "Flocq",
    }
    fragment = backend_fragments.get(lane)
    if fragment is not None and fragment.lower() not in row["backend"].lower():
        raise ValueError(
            f"backend does not identify {lane} in {path}: {row['backend']!r}"
        )


def read_trial_order(
    benchmark: Path,
    expected: set[tuple[str, int, str]],
) -> dict[str, list[tuple[str, int, str]]]:
    path = benchmark / "environment" / "trial-order.csv"
    rows = read_rows(path, TRIAL_ORDER_HEADER)
    result: dict[str, list[tuple[str, int, str]]] = {}
    for row in rows:
        trial = row["trial"]
        if trial not in {f"{number:02d}" for number in range(1, TRIALS + 1)}:
            raise ValueError(f"unknown trial in {path}: {trial!r}")
        order = result.setdefault(trial, [])
        order_index = parse_nonnegative(row, "orderIndex", path)
        if order_index != len(order):
            raise ValueError(
                f"non-contiguous trial order in {path} for trial {trial}: "
                f"{order_index} != {len(order)}"
            )
        key = (
            row["lane"],
            parse_positive(row, "totalBits", path),
            row["operation"],
        )
        if key not in expected:
            raise ValueError(f"unknown trial-order cell in {path}: {key}")
        if key in order:
            raise ValueError(
                f"duplicate trial-order cell in {path} for trial {trial}: {key}"
            )
        order.append(key)

    expected_trials = {f"{number:02d}" for number in range(1, TRIALS + 1)}
    if set(result) != expected_trials:
        raise ValueError(
            f"trial-order trials differ in {path}: "
            f"missing={sorted(expected_trials - set(result))}, "
            f"extra={sorted(set(result) - expected_trials)}"
        )
    for trial, order in result.items():
        if set(order) != expected or len(order) != len(expected):
            raise ValueError(
                f"trial-order matrix differs in {path} for trial {trial}: "
                f"missing={sorted(expected - set(order))}, "
                f"extra={sorted(set(order) - expected)}"
            )
    base_order = result["01"]
    row_count = len(base_order)
    for number in range(1, TRIALS + 1):
        trial = f"{number:02d}"
        start = (number - 1) * row_count // TRIALS
        expected_order = base_order[start:] + base_order[:start]
        if result[trial] != expected_order:
            raise ValueError(
                f"trial {trial} is not the documented cyclic schedule in {path}"
            )
    return result


def verify_trials(
    benchmark: Path,
    expected: set[tuple[str, int, str]],
    selected: dict[tuple[str, int, str], int],
    minimum_nanos: int,
    agreement_iterations: int,
    trial_order: dict[str, list[tuple[str, int, str]]],
) -> dict[tuple[str, int, str], tuple[str, str]]:
    raw = benchmark / "raw"
    paths = sorted(raw.glob("trial-*.csv"))
    expected_names = [f"trial-{trial:02d}.csv" for trial in range(1, TRIALS + 1)]
    if [path.name for path in paths] != expected_names:
        raise ValueError(
            f"raw trial files differ: expected={expected_names!r}, "
            f"actual={[path.name for path in paths]!r}"
        )

    expected_resource_keys = {
        (f"{trial:02d}", lane, width, operation)
        for trial in range(1, TRIALS + 1)
        for lane, width, operation in expected
    }
    timed_rows: dict[tuple[str, int, str], tuple[str, str]] = {}
    for path in paths:
        trial_number = path.stem.removeprefix("trial-")
        rows = read_rows(path, RAW_HEADER)
        actual: set[tuple[str, int, str]] = set()
        actual_order: list[tuple[str, int, str]] = []
        agreement: dict[
            tuple[int, str],
            dict[str, tuple[int, int, int]],
        ] = {}
        for row in rows:
            width = parse_positive(row, "totalBits", path)
            operation = row["operation"]
            key = (lane_for(row, path), width, operation)
            if key in actual:
                raise ValueError(f"duplicate timed cell in {path}: {key}")
            actual.add(key)
            actual_order.append(key)
            verify_row_identity(row, *key, path)
            identity = (row["backend"], row["format"])
            previous_identity = timed_rows.setdefault(key, identity)
            if identity != previous_identity:
                raise ValueError(
                    f"timed backend identity changed between trials at {key}: "
                    f"{identity!r} != {previous_identity!r}"
                )
            if row["measurementMethod"] != MEASUREMENT_METHOD:
                raise ValueError(
                    f"wrong measurement method in {path} at {key}: "
                    f"{row['measurementMethod']!r}"
                )
            iterations = parse_positive(row, "iterations", path)
            if iterations != selected.get(key):
                raise ValueError(
                    f"iteration count differs from calibration in {path} at {key}: "
                    f"{iterations} != {selected.get(key)}"
                )
            total_nanos = parse_positive(row, "totalNanos", path)
            if total_nanos < minimum_nanos:
                raise ValueError(
                    f"timed cell is shorter than the publication floor in {path} "
                    f"at {key}: {total_nanos} < {minimum_nanos}"
                )
            int(row["sink"])
            int(row["fixtureTraceDigest"])
            lane_agreement = verify_agreement_fields(
                row,
                key[0],
                agreement_iterations,
                path,
            )
            if key[0] in AGREEMENT_LANES:
                agreement.setdefault((key[1], key[2]), {})[
                    key[0]
                ] = lane_agreement
            cell_path = (
                raw
                / "rows"
                / f"trial-{trial_number}-{key[0]}-{key[1]}-{key[2]}.csv"
            )
            cell_rows = read_rows(cell_path, RAW_HEADER)
            if cell_rows != [row]:
                raise ValueError(
                    f"per-cell row does not match aggregate trial in {cell_path}"
                )
        if actual != expected:
            raise ValueError(
                f"timed matrix differs in {path}: "
                f"missing={sorted(expected - actual)}, "
                f"extra={sorted(actual - expected)}"
            )
        if actual_order != trial_order[trial_number]:
            raise ValueError(
                f"aggregate row order differs from retained schedule in {path}"
            )
        verify_binary_agreement_matrix(
            agreement,
            f"timed trial {trial_number}",
        )
    expected_cell_files = {
        f"trial-{trial:02d}-{lane}-{width}-{operation}.csv"
        for trial in range(1, TRIALS + 1)
        for lane, width, operation in expected
    }
    actual_cell_files = {
        candidate.name for candidate in (raw / "rows").glob("trial-*.csv")
    }
    if actual_cell_files != expected_cell_files:
        raise ValueError(
            "per-cell raw files differ: "
            f"missing={sorted(expected_cell_files - actual_cell_files)}, "
            f"extra={sorted(actual_cell_files - expected_cell_files)}"
        )

    resource_path = benchmark / "resources" / "process.csv"
    resource_rows = read_rows(resource_path, RESOURCE_HEADER)
    resource_keys: set[tuple[str, str, int, str]] = set()
    for row in resource_rows:
        key = (
            row["trial"],
            row["lane"],
            parse_positive(row, "totalBits", resource_path),
            row["operation"],
        )
        if key in resource_keys:
            raise ValueError(f"duplicate resource row in {resource_path}: {key}")
        resource_keys.add(key)
        if row["exitStatus"] != "0":
            raise ValueError(f"failed benchmark process in {resource_path}: {key}")
        for field in (
            "maxResidentSetKiB",
            "majorPageFaults",
            "minorPageFaults",
        ):
            if int(row[field]) < 0:
                raise ValueError(f"negative {field} in {resource_path}: {key}")
        for field in ("userSeconds", "systemSeconds", "elapsedSeconds"):
            if float(row[field]) < 0:
                raise ValueError(f"negative {field} in {resource_path}: {key}")
    if resource_keys != expected_resource_keys:
        raise ValueError(
            "resource process grid differs: "
            f"missing={sorted(expected_resource_keys - resource_keys)}, "
            f"extra={sorted(resource_keys - expected_resource_keys)}"
        )
    return timed_rows


def binary_precision(format_name: str) -> int | None:
    layouts = {
        "binary4-e2m1": 2,
        "binary5-e2m2": 3,
        "binary6-e3m2": 3,
        "binary7-e3m3": 4,
        "binary8-e4m3": 4,
        "binary16": 11,
        "binary32": 24,
        "binary64": 53,
        "binary128": 113,
    }
    if format_name in layouts:
        return layouts[format_name]
    match = re.fullmatch(r"binary[0-9]+-custom-e[0-9]+m([0-9]+)", format_name)
    return int(match.group(1)) + 1 if match is not None else None


def verify_backend_selection(
    benchmark: Path,
    timed_rows: dict[tuple[str, int, str], tuple[str, str]],
) -> None:
    path = benchmark / "environment" / "backend-selection.csv"
    rows = read_rows(path, BACKEND_SELECTION_HEADER)
    if not rows:
        raise ValueError(f"empty backend-selection matrix: {path}")
    selections: dict[tuple[str, str, int, int, str], str] = {}
    for row in rows:
        storage_bits = parse_positive(row, "storageBits", path)
        precision = parse_positive(row, "maximumSignificandBits", path)
        identity = (
            row["family"],
            row["format"],
            storage_bits,
            precision,
            row["operation"],
        )
        if identity in selections:
            raise ValueError(f"duplicate backend-selection row in {path}: {identity}")
        selections[identity] = row["selected"]
        if row["operation"] not in OPERATIONS:
            raise ValueError(
                f"unknown backend-selection operation in {path}: {identity}"
            )
        for field in ("candidateCount", "expectedCalls", "maxResidentBytes", "score"):
            parse_positive(row, field, path)
        for field in ("residentBytes", "warmCost", "coldCost"):
            parse_nonnegative(row, field, path)
        for field in ("selected", "kernelClass", "policy"):
            if not row[field]:
                raise ValueError(
                    f"empty {field} in backend-selection row in {path}: {identity}"
                )

    comparable: set[tuple[str, int, str]] = set()
    for key, (timed_backend, timed_format) in timed_rows.items():
        lane, width, operation = key
        if lane == "posit-software":
            candidates = [
                selected
                for (
                    family,
                    format_name,
                    storage_bits,
                    _precision,
                    selected_operation,
                ), selected in selections.items()
                if family == "configured posit"
                and format_name == f"posit{width}"
                and storage_bits == width
                and selected_operation == operation
            ]
        elif lane == "binary-software" and width not in DIRECT_BINARY_WORD_WIDTHS:
            precision = binary_precision(timed_format)
            exact_candidates = [
                selected
                for (
                    family,
                    format_name,
                    storage_bits,
                    maximum_significand_bits,
                    selected_operation,
                ), selected in selections.items()
                if family == "configured binary"
                and format_name == timed_format
                and storage_bits == width
                and maximum_significand_bits == precision
                and selected_operation == operation
            ]
            candidates = exact_candidates or [
                selected
                for (
                    family,
                    _format_name,
                    storage_bits,
                    maximum_significand_bits,
                    selected_operation,
                ), selected in selections.items()
                if family == "configured binary"
                and storage_bits == width
                and maximum_significand_bits == precision
                and selected_operation == operation
            ]
        else:
            continue

        if not candidates:
            continue
        if len(candidates) != 1:
            raise ValueError(
                f"backend-selection cell is ambiguous for timed row {key}: "
                f"{candidates!r}"
            )
        if candidates[0] != timed_backend:
            raise ValueError(
                f"timed ExecFloat backend differs from selection matrix at {key}: "
                f"{timed_backend!r} != {candidates[0]!r}"
            )
        comparable.add(key)

    expected_comparable = {
        ("posit-software", width, operation)
        for width in WIDTHS
        for operation in OPERATIONS
    } | {
        ("binary-software", width, operation)
        for width in SELECTION_MATRIX_BINARY_WIDTHS
        for operation in OPERATIONS
    }
    if comparable != expected_comparable:
        raise ValueError(
            "backend-selection comparison grid differs: "
            f"missing={sorted(expected_comparable - comparable)}, "
            f"extra={sorted(comparable - expected_comparable)}"
        )


def read_source_hashes(path: Path) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(),
        start=1,
    ):
        if len(line) < 67 or line[64:66] != "  ":
            raise ValueError(f"invalid source hash at {path}:{line_number}")
        digest, source_path = line[:64], line[66:]
        if (
            re.fullmatch(r"[0-9a-f]{64}", digest) is None
            or not source_path
            or source_path.startswith("/")
            or "\\" in source_path
            or source_path != Path(source_path).as_posix()
            or "." in Path(source_path).parts
            or ".." in Path(source_path).parts
            or source_path in hashes
        ):
            raise ValueError(f"invalid source hash at {path}:{line_number}")
        hashes[source_path] = digest
    return hashes


def find_source_provenance(benchmark: Path) -> Path | None:
    # A development run may keep provenance inside the benchmark directory.
    # Published campaign bundles keep it beside `benchmark/` so the source and
    # cluster records describe the whole release. Accept both layouts, but
    # never guess when two complete copies are present.
    required_names = {
        "source-snapshot.txt",
        "source-files.sha256",
        "worktree-status.txt",
        "worktree.patch",
    }
    candidates = (benchmark / "provenance", benchmark.parent / "provenance")
    complete = [
        candidate
        for candidate in candidates
        if all((candidate / name).is_file() for name in required_names)
    ]
    if len(complete) > 1:
        raise ValueError(
            "benchmark has two complete source-provenance directories: "
            f"{complete!r}"
        )
    return complete[0] if complete else None


def verify_source_metadata(benchmark: Path, metadata: dict[str, str]) -> None:
    provenance = find_source_provenance(benchmark)
    if provenance is None:
        return
    required = {
        "source-snapshot.txt": provenance / "source-snapshot.txt",
        "source-files.sha256": provenance / "source-files.sha256",
        "worktree-status.txt": provenance / "worktree-status.txt",
        "worktree.patch": provenance / "worktree.patch",
    }

    snapshot = read_metadata(required["source-snapshot.txt"])
    if metadata.get("gitCommit") != snapshot.get("head_revision"):
        raise ValueError(
            "benchmark gitCommit differs from retained source snapshot: "
            f"{metadata.get('gitCommit')!r} != {snapshot.get('head_revision')!r}"
        )
    for name, snapshot_key in (
        ("source-files.sha256", "source_file_hashes_sha256"),
        ("worktree-status.txt", "worktree_status_sha256"),
        ("worktree.patch", "worktree_patch_sha256"),
    ):
        expected = snapshot.get(snapshot_key)
        actual = sha256(required[name])
        if actual != expected:
            raise ValueError(
                f"retained {name} differs from source snapshot: "
                f"{actual} != {expected}"
            )

    try:
        recorded_dirty = int(metadata["gitDirtyFiles"])
    except (KeyError, ValueError) as error:
        raise ValueError("benchmark metadata has no valid gitDirtyFiles count") from error
    if recorded_dirty < 0:
        raise ValueError(f"negative gitDirtyFiles count: {recorded_dirty}")
    status_lines = required["worktree-status.txt"].read_text(
        encoding="utf-8"
    ).splitlines()
    captured_dirty = sum(
        bool(line) and not line.startswith("## ") for line in status_lines
    )
    if recorded_dirty != captured_dirty:
        raise ValueError(
            "benchmark dirty-file count differs from retained worktree status: "
            f"{recorded_dirty} != {captured_dirty}"
        )

    source_hashes = read_source_hashes(required["source-files.sha256"])
    # Paths are part of the digest input. Select the recorded source root without
    # translating historical names or changing any retained hashes.
    source_roots = {
        prefix
        for prefix in ("FloatLib/", "LeanFloat/")
        if any(path.startswith(prefix) for path in source_hashes)
    }
    if len(source_roots) != 1:
        raise ValueError(
            "source ledger must contain exactly one library source root: "
            f"{sorted(source_roots)}"
        )
    source_root = next(iter(source_roots))
    build_configs = {"lakefile.lean", "lean-toolchain", "lake-manifest.json"}
    selected_paths = sorted(
        source_path
        for source_path in source_hashes
        if source_path.startswith(source_root) or source_path in build_configs
    )
    missing_configs = sorted(build_configs - set(selected_paths))
    if missing_configs or not any(
        source_path.startswith(source_root) for source_path in selected_paths
    ):
        raise ValueError(
            "source ledger cannot reproduce Lean source hash: "
            f"missing build files={missing_configs}"
        )
    source_digest_input = "".join(
        f"{source_hashes[source_path]}  {source_path}\n"
        for source_path in selected_paths
    ).encode("utf-8")
    captured_source_hash = hashlib.sha256(source_digest_input).hexdigest()
    recorded_source_hash = metadata.get("leanSourceAndBuildConfigHash")
    if captured_source_hash != recorded_source_hash:
        raise ValueError(
            "benchmark Lean source hash differs from retained source ledger: "
            f"{recorded_source_hash} != {captured_source_hash}"
        )


def verify(benchmark: Path) -> None:
    metadata = read_metadata(benchmark / "metadata.txt")
    require(metadata, "runs", str(TRIALS))
    require(metadata, "measurementMethod", MEASUREMENT_METHOD)
    require(metadata, "publicationReadiness", "eligible")
    require(metadata, "developmentOnly", "0")
    require(metadata, "widths", " ".join(map(str, WIDTHS)))
    require(metadata, "operations", " ".join(OPERATIONS))
    require(metadata, "iterationsOverride", "adaptive")
    require(metadata, "calibratedRows", "1")
    require(metadata, "agreementIterations", str(AGREEMENT_ITERATIONS))
    for key in (
        "includeSoftFloat",
        "includePython",
        "includeFlocq",
        "includeUniversal",
    ):
        require(metadata, key, "1")
    benchmark_cpu = metadata.get("benchmarkCPU")
    if benchmark_cpu is None or re.fullmatch(r"[0-9]+", benchmark_cpu) is None:
        raise ValueError(
            "publication benchmark must record one pinned CPU, got "
            f"{benchmark_cpu!r}"
        )

    if "lanes" in metadata:
        require(metadata, "lanes", " ".join(LANES))
    minimum_trials = int(metadata.get("minimumPublicationTrials", "0"))
    minimum_nanos = int(metadata.get("minimumPublicationNanos", "0"))
    target_nanos = int(metadata.get("targetMeasuredNanos", "0"))
    if minimum_trials > TRIALS or minimum_trials < 7:
        raise ValueError(
            f"unexpected publication trial floor: {minimum_trials} for {TRIALS} trials"
        )
    if minimum_nanos < 50_000_000:
        raise ValueError(
            f"publication timing floor is too short: {minimum_nanos} ns"
        )
    if target_nanos < minimum_nanos:
        raise ValueError(
            f"target timing is below the publication floor: "
            f"{target_nanos} < {minimum_nanos}"
        )
    python_has_fma_raw = metadata.get("pythonHasMathFma")
    if python_has_fma_raw not in {"0", "1"}:
        raise ValueError(
            f"invalid or missing pythonHasMathFma: {python_has_fma_raw!r}"
        )

    universal = read_universal_preflight(benchmark)
    expected = expected_cells(python_has_fma_raw == "1", universal)
    trial_order = read_trial_order(benchmark, expected)
    selected = verify_calibration(
        benchmark,
        expected,
        minimum_nanos,
        target_nanos,
        AGREEMENT_ITERATIONS,
    )
    timed_rows = verify_trials(
        benchmark,
        expected,
        selected,
        minimum_nanos,
        AGREEMENT_ITERATIONS,
        trial_order,
    )
    verify_backend_selection(benchmark, timed_rows)
    verify_source_metadata(benchmark, metadata)
    print(
        f"verified {len(expected)} timed cells in each of {TRIALS} trials "
        f"({len(expected) * TRIALS} rows)"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("benchmark", type=Path)
    arguments = parser.parse_args()
    try:
        verify(arguments.benchmark.resolve())
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
