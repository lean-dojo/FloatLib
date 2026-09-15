#!/usr/bin/env python3

"""Check fixture-chain workload agreement across binary benchmark adapters."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")


def parse_bool(value: str) -> bool:
    if value not in {"0", "1"}:
        raise argparse.ArgumentTypeError("expected 0 or 1")
    return value == "1"


def add_unique(
    rows: dict[tuple[str, str], tuple[str, str, str]],
    key: tuple[str, str],
    value: tuple[str, str, str],
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
) -> int:
    adapters: dict[str, dict[tuple[str, str], tuple[str, str, str]]] = {
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
            value = (
                row["agreementIterations"],
                row["agreementSink"],
                row["agreementFixtureTraceDigest"],
            )
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
                add_unique(adapters[label], key, value, label, trial)

    floatlib = adapters["FloatLib"]
    mpfr = adapters["MPFR"]
    actual_keys = set(floatlib) | set(mpfr)
    if expected_keys is not None and actual_keys != expected_keys:
        raise ValueError(
            f"binary fixture-chain grid differs in {trial.name}: "
            f"missing={sorted(expected_keys - actual_keys)}, "
            f"extra={sorted(actual_keys - expected_keys)}"
        )
    if require_flocq:
        flocq_keys = set(adapters["Flocq"])
        if flocq_keys != actual_keys:
            raise ValueError(
                f"Flocq precision-reference grid differs in {trial.name}: "
                f"missing={sorted(actual_keys - flocq_keys)}, "
                f"extra={sorted(flocq_keys - actual_keys)}"
            )

    checked = 0
    for key in sorted(actual_keys, key=lambda item: (int(item[0]), item[1])):
        if key not in floatlib or key not in mpfr:
            raise ValueError(
                f"missing FloatLib or MPFR row in {trial.name} at {key}"
            )
        values = [floatlib[key], mpfr[key]]
        labels = ["FloatLib", "MPFR"]
        if int(floatlib[key][0]) != agreement_iterations:
            raise ValueError(
                f"wrong agreement prefix length in {trial.name} at {key}: "
                f"{floatlib[key][0]} != {agreement_iterations}"
            )
        width, operation = key
        if width in {"32", "64"}:
            native = adapters["Native C"]
            if key not in native:
                raise ValueError(f"missing Native C row in {trial.name} at {key}")
            values.append(native[key])
            labels.append("Native C")
            if require_softfloat:
                softfloat = adapters["Berkeley SoftFloat"]
                if key not in softfloat:
                    raise ValueError(
                        f"missing Berkeley SoftFloat row in {trial.name} at {key}"
                    )
                values.append(softfloat[key])
                labels.append("Berkeley SoftFloat")
        if width == "64" and require_python:
            cpython = adapters["CPython"]
            expects_cpython = operation != "fma" or python_has_fma
            if expects_cpython and key not in cpython:
                raise ValueError(f"missing CPython row in {trial.name} at {key}")
            if key in cpython:
                values.append(cpython[key])
                labels.append("CPython")
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

    expected_keys = None
    if widths is not None:
        expected_keys = {
            (str(width), operation)
            for width in widths
            for operation in operations
        }

    checked = sum(
        verify_trial(
            trial,
            require_softfloat,
            require_python,
            python_has_fma,
            require_flocq,
            expected_keys,
            agreement_iterations,
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

    report.write_text(
        f"Binary fixture-chain workload cells checked: {checked}\n"
        f"Each comparable adapter ran the same untimed {agreement_iterations}-step "
        "agreement prefix. The check compares that prefix's dependency sink and "
        "fixture-trace digest; independently calibrated timed loops may use different "
        "iteration counts. It checks one retained workload, not a "
        "floating-point conformance claim. Native C and Berkeley SoftFloat join "
        "the binary32/binary64 checks, and CPython joins binary64 operations it "
        "provides. When enabled, Flocq must cover the same grid, but it remains "
        "a precision-only reference: its extracted model does not reproduce "
        "each custom binary exponent range, so its dependency trace is not "
        "claimed to agree. "
        f"SoftFloat required: {require_softfloat}; "
        f"CPython enabled: {require_python}; "
        f"Flocq grid required: {require_flocq}.\n",
        encoding="utf-8",
    )
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
        )
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    print(f"verified {checked} binary fixture-chain workload cells")


if __name__ == "__main__":
    main()
