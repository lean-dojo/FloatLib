#!/usr/bin/env python3

"""Check fixture-chain workload agreement across binary benchmark adapters."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
# BinarySingleNaN.Prec_lt_emax requires prec < emax; widths 4, 5 and 7 fail it.
FLOCQ_WIDTHS = {"6", "8", "16", "32", "64", "128", "256", "512", "1024", "2048", "4096"}
LANE_ADAPTERS = {
    "binary-software": "FloatLib",
    "binary-native-c": "Native C",
    "mpfr-reference": "MPFR",
    "softfloat-reference": "Berkeley SoftFloat",
    "cpython-float64": "CPython",
    "flocq-reference": "Flocq",
    "posit-software": None,
    "universal-posit": None,
}


def read_requested_matrix(path: Path) -> dict[str, set[tuple[str, str]]]:
    requested = {label: set() for label in LANE_ADAPTERS.values() if label is not None}
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ["lane", "totalBits", "operation"]:
            raise ValueError(f"invalid requested matrix header in {path}")
        for row in reader:
            if row["lane"] not in LANE_ADAPTERS:
                raise ValueError(f"unknown requested lane: {row['lane']!r}")
            key = (row["totalBits"], row["operation"])
            if int(key[0]) <= 0 or key[1] not in OPERATIONS:
                raise ValueError(f"invalid requested cell in {path}: {key}")
            label = LANE_ADAPTERS[row["lane"]]
            if label is not None:
                if key in requested[label]:
                    raise ValueError(f"duplicate requested {label} cell in {path}: {key}")
                requested[label].add(key)
    return requested


def parse_bool(value: str) -> bool:
    if value not in {"0", "1"}:
        raise argparse.ArgumentTypeError("expected 0 or 1")
    return value == "1"


def normalize_digest(value: int) -> int:
    """Compare signed OCaml and unsigned adapter output as 64-bit patterns."""
    if not -(1 << 63) <= value < (1 << 64):
        raise ValueError(f"digest outside signed/unsigned 64-bit range: {value}")
    return value & ((1 << 64) - 1)


def add_unique(
    rows: dict[tuple[str, str], tuple[int, int, int]],
    key: tuple[str, str],
    value: tuple[int, int, int],
    label: str,
    trial: Path,
) -> None:
    if key in rows:
        raise ValueError(f"duplicate {label} row in {trial.name} at {key}")
    rows[key] = value


def verify_trial(
    trial: Path,
    require_softfloat: bool,
    require_python: bool,
    python_has_fma: bool,
    require_flocq: bool,
    expected_keys: set[tuple[str, str]] | None,
    agreement_iterations: int,
    requested: dict[str, set[tuple[str, str]]] | None = None,
) -> int:
    adapters: dict[str, dict[tuple[str, str], tuple[int, int, int]]] = {
        "FloatLib": {},
        "Native C": {},
        "MPFR": {},
        "Berkeley SoftFloat": {},
        "CPython": {},
        "Flocq": {},
    }
    with trial.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            key = (row["totalBits"], row["operation"])
            label: str | None = None
            if (
                row["implementation"] == "ExecFloat"
                and row["family"] == "binary-interchange"
            ):
                label = "FloatLib"
            elif (
                row["implementation"] == "Native C"
                and row["format"] in {"binary32", "binary64"}
            ):
                label = "Native C"
            elif row["implementation"] == "MPFR":
                label = "MPFR"
            elif (
                row["implementation"] == "Berkeley SoftFloat"
                and row["format"] in {"binary32", "binary64"}
            ):
                label = "Berkeley SoftFloat"
            elif row["implementation"] == "CPython":
                label = "CPython"
            elif row["implementation"] == "Flocq":
                label = "Flocq"
            if label is not None:
                count = int(row["agreementIterations"])
                if count < 0:
                    raise ValueError(
                        f"negative {label} agreement count in {trial.name} at {key}: {count}"
                    )
                value = (
                    count,
                    normalize_digest(int(row["agreementSink"])),
                    normalize_digest(int(row["agreementFixtureTraceDigest"])),
                )
                add_unique(adapters[label], key, value, label, trial)

    floatlib = adapters["FloatLib"]
    mpfr = adapters["MPFR"]
    actual_keys = set(floatlib) | set(mpfr)
    if requested is not None:
        for label, expected in requested.items():
            actual = set(adapters[label])
            if actual != expected:
                raise ValueError(
                    f"requested {label} grid differs in {trial.name}: "
                    f"missing={sorted(expected - actual)}, "
                    f"extra={sorted(actual - expected)}"
                )
            for key, value in adapters[label].items():
                if value[0] != agreement_iterations:
                    raise ValueError(
                        f"wrong {label} agreement prefix length in {trial.name} at {key}: "
                        f"{value[0]} != {agreement_iterations}"
                    )
        actual_keys = requested["FloatLib"] & requested["MPFR"]
    if expected_keys is not None and actual_keys != expected_keys:
        raise ValueError(
            f"binary fixture-chain grid differs in {trial.name}: "
            f"missing={sorted(expected_keys - actual_keys)}, "
            f"extra={sorted(actual_keys - expected_keys)}"
        )
    check_flocq = require_flocq or bool(adapters["Flocq"])
    if check_flocq:
        flocq_keys = set(adapters["Flocq"])
        expected_flocq = {key for key in actual_keys if key[0] in FLOCQ_WIDTHS}
        if flocq_keys != expected_flocq:
            raise ValueError(
                f"Flocq agreement grid differs in {trial.name}: "
                f"missing={sorted(expected_flocq - flocq_keys)}, "
                f"extra={sorted(flocq_keys - expected_flocq)}"
            )

    checked = 0
    for key in sorted(actual_keys, key=lambda item: (int(item[0]), item[1])):
        if key not in floatlib or key not in mpfr:
            raise ValueError(
                f"missing FloatLib or MPFR row in {trial.name} at {key}"
            )
        values = [floatlib[key], mpfr[key]]
        labels = ["FloatLib", "MPFR"]
        if floatlib[key][0] != agreement_iterations:
            raise ValueError(
                f"wrong agreement prefix length in {trial.name} at {key}: "
                f"{floatlib[key][0]} != {agreement_iterations}"
            )
        width, operation = key
        if width in {"32", "64"} and (
            requested is None or key in requested["Native C"]
        ):
            native = adapters["Native C"]
            if key not in native:
                raise ValueError(f"missing Native C row in {trial.name} at {key}")
            values.append(native[key])
            labels.append("Native C")
        if width in {"32", "64"} and (
            require_softfloat if requested is None else key in requested["Berkeley SoftFloat"]
        ):
            softfloat = adapters["Berkeley SoftFloat"]
            if key not in softfloat:
                raise ValueError(
                    f"missing Berkeley SoftFloat row in {trial.name} at {key}"
                )
            values.append(softfloat[key])
            labels.append("Berkeley SoftFloat")
        if width == "64" and (
            require_python if requested is None else key in requested["CPython"]
        ):
            cpython = adapters["CPython"]
            expects_cpython = operation != "fma" or python_has_fma
            if expects_cpython and key not in cpython:
                raise ValueError(f"missing CPython row in {trial.name} at {key}")
            if key in cpython:
                values.append(cpython[key])
                labels.append("CPython")
        if check_flocq and key[0] in FLOCQ_WIDTHS:
            values.append(adapters["Flocq"][key])
            labels.append("Flocq")
        if len(set(values)) != 1:
            raise ValueError(
                f"binary fixture-chain workload differs in {trial.name} at {key}: "
                f"{dict(zip(labels, values, strict=True))!r}"
            )
        checked += 1
    return checked


def verify(
    raw: Path,
    report: Path,
    require_softfloat: bool,
    require_python: bool,
    python_has_fma: bool,
    require_flocq: bool,
    trials: int | None,
    widths: tuple[int, ...] | None,
    operations: tuple[str, ...],
    agreement_iterations: int,
    requested_matrix: Path | None = None,
) -> int:
    trial_paths = sorted(raw.glob("trial-*.csv"))
    if trials is not None:
        expected_names = [
            f"trial-{trial:02d}.csv" for trial in range(1, trials + 1)
        ]
        if [path.name for path in trial_paths] != expected_names:
            raise ValueError(
                f"binary trial files differ: expected={expected_names!r}, "
                f"actual={[path.name for path in trial_paths]!r}"
            )
    if not trial_paths:
        raise ValueError(f"no benchmark trials found under {raw}")

    requested = read_requested_matrix(requested_matrix) if requested_matrix is not None else None
    expected_keys = None
    if widths is not None:
        expected_keys = {
            (str(width), operation)
            for width in widths
            for operation in operations
        }
    elif requested is not None:
        expected_keys = requested["FloatLib"] & requested["MPFR"]

    checked = sum(
        verify_trial(
            trial,
            require_softfloat,
            require_python,
            python_has_fma,
            require_flocq,
            expected_keys,
            agreement_iterations,
            requested,
        )
        for trial in trial_paths
    )
    if expected_keys is not None and trials is not None:
        expected_checked = len(expected_keys) * trials
        if checked != expected_checked:
            raise ValueError(
                "binary fixture-chain workload count differs: "
                f"{checked} != {expected_checked}"
            )

    native_note = (
        "Native C and Berkeley SoftFloat join the binary32/binary64 checks, "
        if requested is None or requested["Native C"]
        else "Only the requested adapters join each paired check, "
    )
    summary = (
        f"Binary fixture-chain workload cells checked: {checked}\n"
        f"Each comparable adapter reports the same untimed {agreement_iterations}-step "
        "agreement prefix. Flocq may reuse its prefix within the campaign for the same "
        "compiled executable and format/operation. The check compares that prefix's dependency sink and "
        "fixture-trace digest; independently calibrated timed loops may use different "
        "iteration counts. It checks one retained workload, not a "
        f"floating-point conformance claim. {native_note}"
        "and CPython joins binary64 operations it "
        "provides. When present or required, Flocq covers the supported FloatLib/MPFR "
        "grid and its agreement prefix length, dependency sink and fixture-trace "
        "digest must match. Widths 4, 5 and 7 are outside BinarySingleNaN's prec < emax "
        "domain and have no Flocq rows. "
        f"SoftFloat required: {require_softfloat}; "
        f"CPython enabled: {require_python}; "
        f"Flocq agreement required: {require_flocq}.\n"
    )
    if requested is not None:
        if checked == 0:
            summary = (
                "Binary fixture-chain workload cells checked: 0\n"
                "Requested adapter rows and agreement prefix lengths were checked. "
                "No FloatLib/MPFR pairs were requested; no cross-adapter agreement was checked.\n"
            )
        standalone = len(requested["FloatLib"] - requested["MPFR"]) * len(trial_paths)
        if standalone:
            summary += (
                f"Standalone FloatLib binary workload cells: {standalone}. "
                "Their presence and prefix lengths were checked; "
                "they have no requested MPFR partner.\n"
            )
    report.write_text(summary, encoding="utf-8")
    return checked


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw", type=Path)
    parser.add_argument("report", type=Path)
    parser.add_argument("--softfloat", type=parse_bool, required=True)
    parser.add_argument("--python", type=parse_bool, required=True)
    parser.add_argument("--python-has-fma", type=parse_bool, required=True)
    parser.add_argument("--flocq", type=parse_bool, required=True)
    parser.add_argument("--trials", type=int)
    parser.add_argument("--agreement-iterations", type=int, required=True)
    parser.add_argument("--widths", nargs="+", type=int)
    parser.add_argument("--requested-matrix", type=Path)
    parser.add_argument(
        "--operations",
        nargs="+",
        choices=OPERATIONS,
        default=OPERATIONS,
    )
    arguments = parser.parse_args()
    if arguments.agreement_iterations <= 0:
        raise SystemExit("--agreement-iterations must be positive")
    try:
        checked = verify(
            arguments.raw.resolve(),
            arguments.report.resolve(),
            arguments.softfloat,
            arguments.python,
            arguments.python_has_fma,
            arguments.flocq,
            arguments.trials,
            tuple(arguments.widths) if arguments.widths is not None else None,
            tuple(arguments.operations),
            arguments.agreement_iterations,
            arguments.requested_matrix,
        )
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    print(f"verified {checked} binary fixture-chain workload cells")


if __name__ == "__main__":
    main()
