#!/usr/bin/env python3
"""Summarize bounded FloatLib transcendental comparisons.

MPFR is the correctly rounded reference. Optional shared libraries add observational
CORE-MATH, OpenLibm, and RLIBM columns. A numerical difference is recorded, never treated as a
conformance failure: FloatLib's current transcendental kernels are deterministic
approximations without a correct-rounding claim.
"""

from __future__ import annotations

import argparse
import ctypes
import ctypes.util
import csv
import hashlib
import json
import math
import struct
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Iterable

OPERATIONS = ("exp", "log", "sin", "cos", "sinh", "cosh", "tanh")
FORMATS = ("binary32", "binary64")
EDGE_CASE_COUNTS = {"binary32": 37, "binary64": 38}


@dataclass(frozen=True)
class Format:
    width: int
    exponent_bits: int
    fraction_bits: int

    @property
    def sign_mask(self) -> int:
        return 1 << (self.width - 1)

    @property
    def fraction_mask(self) -> int:
        return (1 << self.fraction_bits) - 1

    @property
    def exponent_mask(self) -> int:
        return ((1 << self.exponent_bits) - 1) << self.fraction_bits

    @property
    def width_mask(self) -> int:
        return (1 << self.width) - 1


FORMAT_INFO = {
    "binary32": Format(32, 8, 23),
    "binary64": Format(64, 11, 52),
}


@dataclass(frozen=True)
class Case:
    name: str
    format_name: str
    operation: str
    input_bits: int
    floatlib_bits: int
    mpfr_bits: int


@dataclass(frozen=True)
class Summary:
    candidate: str
    format_name: str
    operation: str
    cases: int
    value_exact: int
    bit_exact: int
    finite_pairs: int
    nonfinite_mismatch: int
    ulp_0: int
    ulp_1: int
    ulp_2_3: int
    ulp_4_15: int
    ulp_16_255: int
    ulp_256_plus: int
    ulp_max: int | None
    ulp_p50: int | None
    ulp_p90: int | None
    ulp_p99: int | None


def is_nan(bits: int, fmt: Format) -> bool:
    return (bits & fmt.exponent_mask) == fmt.exponent_mask and (
        bits & fmt.fraction_mask
    ) != 0


def is_infinite(bits: int, fmt: Format) -> bool:
    return (bits & fmt.exponent_mask) == fmt.exponent_mask and (
        bits & fmt.fraction_mask
    ) == 0


def is_finite(bits: int, fmt: Format) -> bool:
    return (bits & fmt.exponent_mask) != fmt.exponent_mask


def value_matches(candidate: int, reference: int, fmt: Format) -> bool:
    if is_nan(reference, fmt):
        return is_nan(candidate, fmt)
    return candidate == reference


def ordered_encoding(bits: int, fmt: Format) -> int:
    """Map finite IEEE encodings to an order where adjacent values differ by one."""
    bits &= fmt.width_mask
    magnitude = bits & (fmt.sign_mask - 1)
    if bits & fmt.sign_mask:
        return fmt.sign_mask - magnitude
    return fmt.sign_mask + magnitude


def ulp_distance(left: int, right: int, fmt: Format) -> int:
    if not is_finite(left, fmt) or not is_finite(right, fmt):
        raise ValueError("ULP distance is defined here only for finite values")
    return abs(ordered_encoding(left, fmt) - ordered_encoding(right, fmt))


def percentile(sorted_values: list[int], probability: float) -> int | None:
    if not sorted_values:
        return None
    index = max(0, math.ceil(probability * len(sorted_values)) - 1)
    return sorted_values[index]


def parse_cases(path: Path, random_count: int) -> list[Case]:
    if not 0 <= random_count <= 256:
        raise ValueError(f"random count outside the supported range: {random_count}")
    cases: list[Case] = []
    keys: set[tuple[str, str, str]] = set()
    names_by_group: dict[tuple[str, str], set[str]] = defaultdict(set)
    with path.open(encoding="utf-8", newline="") as stream:
        rows = (line for line in stream if not line.startswith("#"))
        reader = csv.reader(rows, delimiter="\t")
        for line_number, row in enumerate(reader, start=1):
            if len(row) != 6:
                raise ValueError(
                    f"{path}: data row {line_number} has {len(row)} fields, expected 6"
                )
            name, format_name, operation, input_text, floatlib_text, mpfr_text = row
            if format_name not in FORMAT_INFO:
                raise ValueError(f"{path}: unknown format {format_name!r}")
            if operation not in OPERATIONS:
                raise ValueError(f"{path}: unknown operation {operation!r}")
            fmt = FORMAT_INFO[format_name]
            values = tuple(int(text) for text in (input_text, floatlib_text, mpfr_text))
            if any(value < 0 or value > fmt.width_mask for value in values):
                raise ValueError(f"{path}: encoding outside {format_name} at {name}")
            key = (format_name, operation, name)
            if key in keys:
                raise ValueError(f"{path}: duplicate comparison case {key!r}")
            keys.add(key)
            names_by_group[(format_name, operation)].add(name)
            cases.append(Case(name, format_name, operation, *values))
    if not cases:
        raise ValueError(f"{path}: no comparison cases")

    expected_total = 0
    for format_name in FORMATS:
        expected_group_size = EDGE_CASE_COUNTS[format_name] + random_count
        expected_total += len(OPERATIONS) * expected_group_size
        canonical_names: set[str] | None = None
        for operation in OPERATIONS:
            names = names_by_group.get((format_name, operation), set())
            if len(names) != expected_group_size:
                raise ValueError(
                    f"{path}: {format_name}/{operation} has {len(names)} cases, "
                    f"expected {expected_group_size}"
                )
            if canonical_names is None:
                canonical_names = names
            elif names != canonical_names:
                missing = sorted(canonical_names - names)
                extra = sorted(names - canonical_names)
                raise ValueError(
                    f"{path}: inconsistent case names for {format_name}/{operation}; "
                    f"missing={missing[:3]!r}, extra={extra[:3]!r}"
                )
    if len(cases) != expected_total:
        raise ValueError(
            f"{path}: parsed {len(cases)} cases, expected {expected_total}"
        )
    return cases


def bits_to_argument(bits: int, format_name: str) -> float:
    if format_name == "binary32":
        return struct.unpack("<f", struct.pack("<I", bits))[0]
    return struct.unpack("<d", struct.pack("<Q", bits))[0]


def result_to_bits(value: float, format_name: str) -> int:
    if format_name == "binary32":
        return struct.unpack("<I", struct.pack("<f", value))[0]
    return struct.unpack("<Q", struct.pack("<d", value))[0]


class SharedLibraryProvider:
    def __init__(
        self,
        name: str,
        path: Path,
        symbols: dict[tuple[str, str], str],
    ) -> None:
        self.name = name
        self.path = path
        self._library = ctypes.CDLL(str(path), mode=ctypes.RTLD_LOCAL)
        self._functions: dict[tuple[str, str], Callable[[float], float]] = {}
        missing: list[str] = []
        for key, symbol in symbols.items():
            try:
                function = getattr(self._library, symbol)
            except AttributeError:
                missing.append(f"{key[0]}/{key[1]}:{symbol}")
                continue
            scalar = ctypes.c_float if key[0] == "binary32" else ctypes.c_double
            function.argtypes = [scalar]
            function.restype = scalar
            self._functions[key] = function
        if missing:
            raise ValueError(
                f"{name}: missing {len(missing)} required symbol(s) in {path}: "
                + ", ".join(missing)
            )

    @property
    def supported_keys(self) -> frozenset[tuple[str, str]]:
        return frozenset(self._functions)

    def evaluate(self, case: Case) -> int | None:
        function = self._functions.get((case.format_name, case.operation))
        if function is None:
            return None
        argument = bits_to_argument(case.input_bits, case.format_name)
        return result_to_bits(function(argument), case.format_name)


def set_round_to_nearest() -> str:
    library_name = ctypes.util.find_library("m")
    library = ctypes.CDLL(library_name or None)
    try:
        set_round = library.fesetround
        get_round = library.fegetround
    except AttributeError as error:
        raise ValueError("the C runtime does not expose fenv rounding controls") from error
    set_round.argtypes = [ctypes.c_int]
    set_round.restype = ctypes.c_int
    get_round.argtypes = []
    get_round.restype = ctypes.c_int
    # FE_TONEAREST is zero on the supported glibc targets.
    if set_round(0) != 0 or get_round() != 0:
        raise ValueError("failed to establish FE_TONEAREST for external providers")
    return "FE_TONEAREST"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_provenance(path: Path | None) -> dict[str, str]:
    if path is None:
        return {}
    result: dict[str, str] = {}
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            fields = line.split("\t")
            if len(fields) != 2 or not fields[0]:
                raise ValueError(
                    f"{path}: malformed provenance row {line_number}: {line!r}"
                )
            key, value = fields
            if key in result:
                raise ValueError(f"{path}: duplicate provenance key {key!r}")
            result[key] = value
    return result


def core_math_symbols() -> dict[tuple[str, str], str]:
    result: dict[tuple[str, str], str] = {}
    for operation in OPERATIONS:
        result[("binary32", operation)] = f"cr_{operation}f"
        result[("binary64", operation)] = f"cr_{operation}"
    return result


def openlibm_symbols() -> dict[tuple[str, str], str]:
    result: dict[tuple[str, str], str] = {}
    for operation in OPERATIONS:
        result[("binary32", operation)] = f"{operation}f"
        result[("binary64", operation)] = operation
    return result


def rlibm_symbols() -> dict[tuple[str, str], str]:
    return {
        ("binary32", operation): f"floatlib_rlibm_{operation}"
        for operation in ("exp", "log", "sinh", "cosh")
    }


def make_summary(
    candidate_name: str,
    format_name: str,
    operation: str,
    pairs: Iterable[tuple[int, int]],
) -> Summary:
    fmt = FORMAT_INFO[format_name]
    materialized = list(pairs)
    distances = sorted(
        ulp_distance(candidate, reference, fmt)
        for candidate, reference in materialized
        if is_finite(candidate, fmt) and is_finite(reference, fmt)
    )

    def in_range(lower: int, upper: int | None = None) -> int:
        if upper is None:
            return sum(distance >= lower for distance in distances)
        return sum(lower <= distance <= upper for distance in distances)

    return Summary(
        candidate=candidate_name,
        format_name=format_name,
        operation=operation,
        cases=len(materialized),
        value_exact=sum(
            value_matches(candidate, reference, fmt)
            for candidate, reference in materialized
        ),
        bit_exact=sum(candidate == reference for candidate, reference in materialized),
        finite_pairs=len(distances),
        nonfinite_mismatch=sum(
            not (is_finite(candidate, fmt) and is_finite(reference, fmt))
            and not value_matches(candidate, reference, fmt)
            for candidate, reference in materialized
        ),
        ulp_0=in_range(0, 0),
        ulp_1=in_range(1, 1),
        ulp_2_3=in_range(2, 3),
        ulp_4_15=in_range(4, 15),
        ulp_16_255=in_range(16, 255),
        ulp_256_plus=in_range(256),
        ulp_max=distances[-1] if distances else None,
        ulp_p50=percentile(distances, 0.50),
        ulp_p90=percentile(distances, 0.90),
        ulp_p99=percentile(distances, 0.99),
    )


def percent(count: int, total: int) -> str:
    if total == 0:
        return "n/a"
    return f"{100.0 * count / total:.2f}%"


def optional_integer(value: int | None) -> str:
    return "n/a" if value is None else str(value)


def write_details(
    path: Path,
    cases: list[Case],
    results: dict[str, list[int | None]],
) -> None:
    candidates = list(results)
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(
            ["case", "format", "operation", "input_bits", "mpfr_bits"]
            + [f"{name}_bits" for name in candidates]
            + [f"{name}_ulp" for name in candidates]
        )
        for index, case in enumerate(cases):
            fmt = FORMAT_INFO[case.format_name]
            outputs = [results[name][index] for name in candidates]
            distances = [
                (
                    ulp_distance(output, case.mpfr_bits, fmt)
                    if output is not None
                    and is_finite(output, fmt)
                    and is_finite(case.mpfr_bits, fmt)
                    else ""
                )
                for output in outputs
            ]
            writer.writerow(
                [
                    case.name,
                    case.format_name,
                    case.operation,
                    f"0x{case.input_bits:0{fmt.width // 4}x}",
                    f"0x{case.mpfr_bits:0{fmt.width // 4}x}",
                ]
                + [
                    "" if output is None else f"0x{output:0{fmt.width // 4}x}"
                    for output in outputs
                ]
                + distances
            )


def write_markdown(
    path: Path,
    input_path: Path,
    summaries: list[Summary],
    providers: list[SharedLibraryProvider],
) -> None:
    provider_text = ", ".join(provider.name for provider in providers) or "none"
    lines = [
        "# Bounded transcendental comparison",
        "",
        "Status: **observational comparison complete; this is not a conformance pass**.",
        "",
        f"Input: `{input_path.name}`",
        f"Optional external providers: {provider_text}",
        "",
        (
            "MPFR is the correctly rounded nearest-even reference. FloatLib's current "
            "transcendental kernels are deterministic approximations: differences below are "
            "measurements, not conformance failures."
        ),
        "",
        (
            "`Value exact` treats any NaN result as a NaN match because MPFR does not preserve "
            "IEEE NaN payloads. `Bit exact` is literal encoding equality. ULP columns include "
            "only pairs where both outputs are finite; signed zero has distance zero. "
            "`Nonfinite mismatch` counts differing infinities, NaNs, or finite/nonfinite pairs."
        ),
        "",
        "| Candidate | Format | Operation | Cases | Value exact | Bit exact | Finite | "
        "Nonfinite mismatch | 0 ULP | 1 ULP | 2–3 | 4–15 | 16–255 | ≥256 | Max | P50 | "
        "P90 | P99 |",
        "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | "
        "---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in summaries:
        lines.append(
            f"| {row.candidate} | {row.format_name} | {row.operation} | {row.cases} | "
            f"{row.value_exact} ({percent(row.value_exact, row.cases)}) | "
            f"{row.bit_exact} ({percent(row.bit_exact, row.cases)}) | "
            f"{row.finite_pairs} | {row.nonfinite_mismatch} | {row.ulp_0} | {row.ulp_1} | "
            f"{row.ulp_2_3} | {row.ulp_4_15} | {row.ulp_16_255} | {row.ulp_256_plus} | "
            f"{optional_integer(row.ulp_max)} | {optional_integer(row.ulp_p50)} | "
            f"{optional_integer(row.ulp_p90)} | {optional_integer(row.ulp_p99)} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="MPFR-annotated TSV")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--expected-random-count", type=int, required=True)
    parser.add_argument("--provenance", type=Path)
    parser.add_argument("--core-math-lib", type=Path)
    parser.add_argument("--openlibm-lib", type=Path)
    parser.add_argument("--rlibm-lib", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    cases = parse_cases(args.input, args.expected_random_count)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    provenance = read_provenance(args.provenance)

    providers: list[SharedLibraryProvider] = []
    specifications = [
        ("CORE-MATH", args.core_math_lib, core_math_symbols()),
        ("OpenLibm", args.openlibm_lib, openlibm_symbols()),
        ("RLIBM", args.rlibm_lib, rlibm_symbols()),
    ]
    for name, path, symbols in specifications:
        if path is not None:
            providers.append(SharedLibraryProvider(name, path, symbols))

    rounding_environment = set_round_to_nearest() if providers else "not applicable"
    results: dict[str, list[int | None]] = {
        "FloatLib": [case.floatlib_bits for case in cases]
    }
    for provider in providers:
        results[provider.name] = [provider.evaluate(case) for case in cases]

    provider_coverage: list[dict[str, object]] = []
    for provider in providers:
        expected = sum(
            1
            for case in cases
            if (case.format_name, case.operation) in provider.supported_keys
        )
        actual = sum(output is not None for output in results[provider.name])
        if actual != expected:
            raise ValueError(
                f"{provider.name}: evaluated {actual} cases, expected {expected}"
            )
        provider_coverage.append(
            {
                "name": provider.name,
                "supported_groups": [
                    {"format": format_name, "operation": operation}
                    for format_name, operation in sorted(provider.supported_keys)
                ],
                "expected_evaluations": expected,
                "actual_evaluations": actual,
            }
        )

    summaries: list[Summary] = []
    for candidate_name, outputs in results.items():
        grouped: dict[tuple[str, str], list[tuple[int, int]]] = defaultdict(list)
        for case, output in zip(cases, outputs, strict=True):
            if output is not None:
                grouped[(case.format_name, case.operation)].append(
                    (output, case.mpfr_bits)
                )
        for format_name in FORMATS:
            for operation in OPERATIONS:
                pairs = grouped.get((format_name, operation))
                if pairs:
                    summaries.append(
                        make_summary(candidate_name, format_name, operation, pairs)
                    )

    write_details(args.output_dir / "details.tsv", cases, results)
    write_markdown(args.output_dir / "summary.md", args.input, summaries, providers)
    payload = {
        "adapter": "transcendental_compare",
        "status": "observational_complete",
        "comparison_kind": "observational",
        "conformance": False,
        "input": args.input.name,
        "cases": len(cases),
        "expected_random_count": args.expected_random_count,
        "rounding_environment": rounding_environment,
        "provenance": provenance,
        "providers": [
            {
                "name": provider.name,
                "library": provider.path.name,
                "sha256": sha256(provider.path),
            }
            for provider in providers
        ],
        "provider_coverage": provider_coverage,
        "summaries": [asdict(summary) for summary in summaries],
    }
    (args.output_dir / "summary.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(args.output_dir / "summary.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
