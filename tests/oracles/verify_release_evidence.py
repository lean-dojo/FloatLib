#!/usr/bin/env python3

"""Verify the semantic claims supported by retained external result artifacts."""

from __future__ import annotations

import argparse
import csv
import json
import re
import sqlite3
import sys
from collections import Counter
from dataclasses import asdict
from pathlib import Path, PurePosixPath
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

import transcendental_report


RELEASE_STATUSES = {
    "00-adapter-unit-tests": "pass",
    "01-testfloat": "pass",
    "02-format-standards": "pass",
    "03-mpfr-primitives": "pass",
    "04-mpfr-reductions": "pass",
    "05-arb": "pass",
    "06-native-fpu": "pass",
    "07-binary16-mpfr-rows": "pass",
    "08-testfloat-level2-smoke": "pass",
    "09-ibm-fpgen": "pass",
    "10-smt-qf-fp": "pass",
    "11-softposit": "external-limitation",
}

# The status of 12-transcendentals follows the kind of its retained summary: the saved
# campaign recorded differences without a gate. A run of the known-failure gate fails on
# any difference from MPFR that the known-failure list does not name, on a listed case
# that changes or now matches, and on any difference in a correctly rounded domain. The
# list is empty, so a passing run has no listed differences; it is a qualified pass
# because the CORE-MATH, OpenLibm, and RLIBM comparisons beside the gate stay observational.
TRANSCENDENTAL_RELEASE_STATUSES = {
    "observational": "observational-complete",
    "known-failure gate": "qualified-pass",
}

# Gate counts that must be zero in a passing known-failure gate summary.
TRANSCENDENTAL_GATE_FAILURES = (
    "new_mismatches",
    "changed_known_failures",
    "correctly_rounded_mismatches",
    "stale_known_failures",
)

# The external providers every retained transcendental comparison evaluates.
TRANSCENDENTAL_PROVIDERS = set(transcendental_report.PROVIDER_SYMBOLS)

# The census entry of the retained runs' invocation: `--random-count 256`, default tier.
# A retained gate run must embed this entry of the checked-in census, so recording the
# census again requires retaining a new release campaign.
TRANSCENDENTAL_CENSUS = "release"
TRANSCENDENTAL_CENSUS_FILE = (
    Path(__file__).resolve().parent / "data" / "transcendental-census.json"
)

ECOSYSTEM_CLASSIFICATIONS = {
    "daisy": ("upstream-qualification", "pass"),
    "fptaylor": ("upstream-qualification", "pass"),
    "herbie": ("upstream-qualification", "observational-complete"),
    "openlibm": ("upstream-qualification", "pass"),
    "rlibm-all": ("upstream-qualification", "qualified-pass"),
    "reproblas": ("upstream-qualification", "qualified-pass"),
    "exblas": ("upstream-qualification", "qualified-pass"),
    "smt-qf-fp": ("direct-differential", "pass"),
    "transcendental-direct": (
        "direct-observational",
        "observational-complete",
    ),
    "fpbench": ("upstream-qualification", "qualified-pass"),
    "verificarlo": ("upstream-qualification", "pass"),
    "core-math": ("upstream-qualification", "qualified-pass"),
}

FLIT_SUITES = {"flit-base", "flit-openmpi", "flit-mpich"}
FLIT_REVISION = "27b6061b9d2302fa8c3252fe770287bb4d07905b"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def integer(
    raw: object,
    context: str,
    *,
    minimum: int = 0,
) -> int:
    if isinstance(raw, bool):
        raise ValueError(f"{context} is not an integer: {raw!r}")
    try:
        value = int(raw)
    except (TypeError, ValueError) as error:
        raise ValueError(f"{context} is not an integer: {raw!r}") from error
    if str(value) != str(raw):
        raise ValueError(f"{context} is not canonical decimal: {raw!r}")
    if value < minimum:
        raise ValueError(f"{context} is less than {minimum}: {value}")
    return value


def safe_relative(raw: str, context: str) -> PurePosixPath:
    path = PurePosixPath(raw)
    if (
        not raw
        or path.is_absolute()
        or "\\" in raw
        or any(part in {"", ".", ".."} for part in path.parts)
        or path.as_posix() != raw
    ):
        raise ValueError(f"unsafe path in {context}: {raw!r}")
    return path


def table(
    path: Path,
    header: list[str],
    *,
    delimiter: str = ",",
) -> list[dict[str, str]]:
    if not path.is_file():
        raise ValueError(f"missing retained evidence file: {path}")
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.reader(stream, delimiter=delimiter)
        try:
            actual_header = next(reader)
        except StopIteration as error:
            raise ValueError(f"empty retained evidence table: {path}") from error
        if actual_header != header:
            raise ValueError(
                f"unexpected header in {path}: "
                f"{actual_header!r} != {header!r}"
            )
        rows: list[dict[str, str]] = []
        for line_number, values in enumerate(reader, start=2):
            if len(values) != len(header):
                raise ValueError(
                    f"unexpected field count in {path}:{line_number}: "
                    f"{len(values)}"
                )
            rows.append(dict(zip(header, values, strict=True)))
    if not rows:
        raise ValueError(f"empty retained evidence table: {path}")
    return rows


def json_object(path: Path) -> dict[str, Any]:
    if not path.is_file():
        raise ValueError(f"missing retained evidence file: {path}")
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=transcendental_report.unique_keys,
        )
    except ValueError as error:
        raise ValueError(f"invalid JSON in {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object in {path}")
    return value


def assignments(path: Path) -> dict[str, str]:
    if not path.is_file():
        raise ValueError(f"missing retained evidence file: {path}")
    result: dict[str, str] = {}
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line or "=" not in line:
            raise ValueError(f"invalid assignment in {path}:{line_number}")
        key, value = line.split("=", 1)
        if not key or key in result:
            raise ValueError(
                f"duplicate or empty key in {path}:{line_number}"
            )
        result[key] = value
    return result


def summary_rows(
    path: Path,
    header: list[str],
) -> list[dict[str, str]]:
    rows = table(path, header, delimiter="\t")
    suites: set[str] = set()
    for row in rows:
        suite = row["suite"]
        if not suite or suite in suites:
            raise ValueError(f"empty or duplicate suite in {path}: {suite!r}")
        suites.add(suite)
        integer(row["seconds"], f"{path}:{suite}:seconds")
        relative = safe_relative(row["log"], f"{path}:{suite}:log")
        if not (path.parent / relative).is_file():
            raise ValueError(
                f"missing retained log for {suite!r}: {path.parent / relative}"
            )
    return rows


def transcendental_kind(root: Path) -> str:
    path = root / "summary.json"
    kind = json_object(path).get("comparison_kind")
    require(
        kind in TRANSCENDENTAL_RELEASE_STATUSES,
        f"unknown transcendental comparison kind in {path}: {kind!r}",
    )
    return kind


def expected_release_statuses(release: Path) -> dict[str, str]:
    kind = transcendental_kind(release / "12-transcendentals")
    return {
        **RELEASE_STATUSES,
        "12-transcendentals": TRANSCENDENTAL_RELEASE_STATUSES[kind],
    }


def verify_release_summary(release: Path) -> None:
    rows = summary_rows(
        release / "summary.tsv",
        ["suite", "status", "seconds", "log"],
    )
    actual = {row["suite"]: row["status"] for row in rows}
    expected = expected_release_statuses(release)
    if actual != expected:
        raise ValueError(
            "release suite status differs: "
            f"expected={expected!r}, actual={actual!r}"
        )
    rendering = (release / "rendering-status.txt").read_text(encoding="utf-8")
    if rendering != "status=rendered\n":
        raise ValueError(f"release plot rendering did not pass: {rendering!r}")


def verify_release_aggregate_logs(release: Path) -> None:
    """Check the strongest claims available when a suite retained only a log."""

    logs = release / "logs"
    adapter = (logs / "00-adapter-unit-tests.log").read_text(encoding="utf-8")
    require(
        re.findall(r"^Ran ([0-9]+) tests in ", adapter, flags=re.MULTILINE)
        == ["34", "8"],
        "adapter unit-test counts differ from the retained campaign",
    )
    require(
        len(re.findall(r"^OK$", adapter, flags=re.MULTILINE)) == 2,
        "adapter unit-test log does not contain two successful test runs",
    )
    require(
        "Build completed successfully" in adapter,
        "adapter oracle build did not retain its success marker",
    )

    expected_markers = {
        "03-mpfr-primitives.log": [
            "primitive MPFR validation passed: 400 cases",
        ],
        "04-mpfr-reductions.log": [
            "reduction MPFR oracle passed: 672 cases",
        ],
        "05-arb.log": [
            "TOTAL: 0",
        ],
        "06-native-fpu.log": [
            "== aggregate ==\nTOTAL: 0",
        ],
        "07-binary16-mpfr-rows.log": [
            "binary16 add shard 32768/65536 passed: 65536 ordered pairs",
            "binary16 mul shard 32000/65536 passed: 65536 ordered pairs",
        ],
    }
    for name, markers in expected_markers.items():
        path = logs / name
        text = path.read_text(encoding="utf-8")
        for marker in markers:
            require(marker in text, f"missing aggregate evidence in {path}: {marker!r}")


def verify_ecosystem_summary(ecosystem: Path) -> set[str]:
    rows = summary_rows(
        ecosystem / "summary.tsv",
        ["suite", "evidence", "status", "seconds", "log"],
    )
    actual = {
        row["suite"]: (row["evidence"], row["status"])
        for row in rows
    }
    required = set(ECOSYSTEM_CLASSIFICATIONS)
    missing = required - set(actual)
    extra = set(actual) - required - FLIT_SUITES
    if missing or extra:
        raise ValueError(
            "ecosystem suite set differs: "
            f"missing={sorted(missing)!r}, extra={sorted(extra)!r}"
        )
    present_flit = set(actual) & FLIT_SUITES
    if present_flit not in (set(), FLIT_SUITES):
        raise ValueError(
            "FLiT evidence must retain all three variants or none: "
            f"{sorted(present_flit)!r}"
        )
    expected = dict(ECOSYSTEM_CLASSIFICATIONS)
    expected.update(
        {
            suite: ("upstream-qualification", "pass")
            for suite in present_flit
        }
    )
    if actual != expected:
        raise ValueError(
            "ecosystem classifications differ: "
            f"expected={expected!r}, actual={actual!r}"
        )
    return present_flit


def verify_testfloat(
    root: Path,
    *,
    profile: str,
    level: int,
    campaigns: int,
    cases: int,
) -> None:
    columns = [
        "profile",
        "level",
        "seed",
        "campaigns",
        "cases",
        "value_mismatches",
        "flag_mismatches",
        "parse_errors",
    ]
    summary = table(root / "summary.csv", columns)
    require(len(summary) == 1, f"expected one TestFloat summary row in {root}")
    row = summary[0]
    expected_identity = (profile, str(level), "1")
    actual_identity = (row["profile"], row["level"], row["seed"])
    require(
        actual_identity == expected_identity,
        f"TestFloat campaign identity differs in {root}: {actual_identity!r}",
    )
    totals = {
        name: integer(row[name], f"{root}/summary.csv:{name}")
        for name in columns[3:]
    }
    expected_totals = {
        "campaigns": campaigns,
        "cases": cases,
        "value_mismatches": 0,
        "flag_mismatches": 0,
        "parse_errors": 0,
    }
    require(
        totals == expected_totals,
        f"TestFloat retained totals differ in {root}: {totals!r}",
    )

    campaign_columns = [
        "format",
        "operation",
        "rounding",
        "cases",
        "value_mismatches",
        "flag_mismatches",
        "parse_errors",
    ]
    campaign_rows = table(root / "campaigns.csv", campaign_columns)
    require(
        len(campaign_rows) == campaigns,
        f"TestFloat campaign-row count differs in {root}: "
        f"{len(campaign_rows)} != {campaigns}",
    )
    identities: set[tuple[str, str, str]] = set()
    derived = Counter()
    for line_number, campaign in enumerate(campaign_rows, start=2):
        identity = (
            campaign["format"],
            campaign["operation"],
            campaign["rounding"],
        )
        require(
            all(identity) and identity not in identities,
            f"empty or duplicate TestFloat campaign in "
            f"{root}/campaigns.csv:{line_number}: {identity!r}",
        )
        identities.add(identity)
        for name in campaign_columns[3:]:
            derived[name] += integer(
                campaign[name],
                f"{root}/campaigns.csv:{line_number}:{name}",
                minimum=1 if name == "cases" else 0,
            )
    require(
        dict(derived) == {
            "cases": cases,
            "value_mismatches": 0,
            "flag_mismatches": 0,
            "parse_errors": 0,
        },
        f"TestFloat campaign counters do not reproduce the summary in {root}: "
        f"{dict(derived)!r}",
    )


def verify_format_standards(root: Path) -> None:
    columns = ["oracle", "status", "formats", "cases", "mismatches"]
    rows = table(root / "summary.csv", columns)
    by_oracle = {row["oracle"]: row for row in rows}
    expected = {
        "ONNX low-bit decode": (6, 1296),
        "P3109 4.0.3 value tables": (504, 7602160),
    }
    require(
        set(by_oracle) == set(expected),
        f"format-standard oracle set differs: {sorted(by_oracle)!r}",
    )
    for oracle, (formats, cases) in expected.items():
        row = by_oracle[oracle]
        actual = (
            row["status"],
            integer(row["formats"], f"{root}:{oracle}:formats", minimum=1),
            integer(row["cases"], f"{root}:{oracle}:cases", minimum=1),
            integer(row["mismatches"], f"{root}:{oracle}:mismatches"),
        )
        wanted = ("pass", formats, cases, 0)
        require(
            actual == wanted,
            f"format-standard counters differ for {oracle!r}: {actual!r}",
        )

    shard_paths = sorted((root / "p3109-shards").glob("*.csv"))
    require(len(shard_paths) == 14, f"expected 14 P3109 shards in {root}")
    totals = Counter()
    for path in shard_paths:
        with path.open(newline="", encoding="utf-8") as stream:
            shard_rows = list(csv.reader(stream))
        require(len(shard_rows) == 1, f"expected one row in P3109 shard {path}")
        row = shard_rows[0]
        require(len(row) == 5, f"unexpected P3109 shard row in {path}: {row!r}")
        require(
            row[0] == "P3109 4.0.3 value tables" and row[1] == "pass",
            f"unexpected P3109 shard classification in {path}: {row[:2]!r}",
        )
        totals["formats"] += integer(row[2], f"{path}:formats", minimum=1)
        totals["cases"] += integer(row[3], f"{path}:cases", minimum=1)
        totals["mismatches"] += integer(row[4], f"{path}:mismatches")
    require(
        dict(totals)
        == {"formats": 504, "cases": 7602160, "mismatches": 0},
        f"P3109 shard counters do not reproduce the summary: {dict(totals)!r}",
    )


def result_assignments(line: str, context: str) -> dict[str, str]:
    require(line.startswith("RESULT "), f"invalid RESULT line in {context}")
    result: dict[str, str] = {}
    for field in line.removeprefix("RESULT ").split():
        if "=" not in field:
            raise ValueError(f"invalid RESULT field in {context}: {field!r}")
        key, value = field.split("=", 1)
        if not key or key in result:
            raise ValueError(f"duplicate or empty RESULT key in {context}")
        result[key] = value
    return result


def verify_ibm_fpgen(root: Path) -> None:
    summary = json_object(root / "summary.json")
    counters_raw = summary.get("counters")
    groups_raw = summary.get("groups")
    require(isinstance(counters_raw, dict), "IBM FPgen counters are missing")
    require(isinstance(groups_raw, list) and groups_raw, "IBM FPgen groups are missing")
    counters = {
        key: integer(value, f"{root}/summary.json:counters:{key}")
        for key, value in counters_raw.items()
    }
    expected_counters = {
        "case_records": 130471,
        "decimal": 37296,
        "emitted": 81513,
        "files": 33,
        "lines": 130594,
        "no_result": 4314,
        "non_case_lines": 123,
        "trap_produced": 3336,
        "unsupported": 4012,
        "unsupported_nan_precedence": 92,
        "unsupported_nan_sign": 6,
        "unsupported_operation": 0,
        "unsupported_rounding_mode": 0,
        "unsupported_underflow_convention": 3914,
    }
    require(
        counters == expected_counters,
        f"IBM FPgen classification counters differ: {counters!r}",
    )
    require(
        counters["lines"]
        == counters["case_records"] + counters["non_case_lines"],
        "IBM FPgen line classification is inconsistent",
    )
    require(
        counters["case_records"]
        == counters["decimal"]
        + counters["emitted"]
        + counters["no_result"]
        + counters["trap_produced"]
        + counters["unsupported"],
        "IBM FPgen case classification is inconsistent",
    )
    require(
        counters["unsupported"]
        == counters["unsupported_nan_precedence"]
        + counters["unsupported_nan_sign"]
        + counters["unsupported_operation"]
        + counters["unsupported_rounding_mode"]
        + counters["unsupported_underflow_convention"],
        "IBM FPgen unsupported-reason counters are inconsistent",
    )

    require(len(groups_raw) == 40, f"expected 40 IBM FPgen groups in {root}")
    identities: set[tuple[str, str, str]] = set()
    retained_cases = 0
    for group_number, raw_group in enumerate(groups_raw, start=1):
        require(
            isinstance(raw_group, dict),
            f"IBM FPgen group {group_number} is not an object",
        )
        identity = tuple(
            str(raw_group.get(name, ""))
            for name in ("format", "operation", "rounding")
        )
        require(
            all(identity) and identity not in identities,
            f"empty or duplicate IBM FPgen group: {identity!r}",
        )
        identities.add(identity)
        cases = integer(
            raw_group.get("cases"),
            f"{root}/summary.json:group:{identity}:cases",
            minimum=1,
        )
        retained_cases += cases
        log = root / f"{identity[0]}_{identity[1]}_{identity[2]}.oracle.log"
        require(log.is_file(), f"missing IBM FPgen oracle log: {log}")
        result_lines = [
            line
            for line in log.read_text(encoding="utf-8").splitlines()
            if line.startswith("RESULT ")
        ]
        require(len(result_lines) == 1, f"expected one RESULT line in {log}")
        result = result_assignments(result_lines[0], str(log))
        actual_identity = tuple(
            result.get(name, "") for name in ("format", "operation", "rounding")
        )
        require(
            actual_identity == identity,
            f"IBM FPgen log identity differs in {log}: {actual_identity!r}",
        )
        require(
            integer(result.get("cases"), f"{log}:cases", minimum=1) == cases,
            f"IBM FPgen case count differs in {log}",
        )
        for name in ("value_mismatches", "flag_mismatches", "parse_errors"):
            require(
                integer(result.get(name), f"{log}:{name}") == 0,
                f"IBM FPgen reported {name} in {log}",
            )
    require(
        retained_cases == counters["emitted"],
        f"IBM FPgen group cases differ from emitted cases: "
        f"{retained_cases} != {counters['emitted']}",
    )


SMT_COUNT_KEYS = {
    "bit_mismatches",
    "exact_bit_cases",
    "generated",
    "mismatches",
    "missing_floatlib",
    "nan_class_cases",
    "nan_class_mismatches",
    "protocol_errors",
    "tool_failures",
}


def smt_counts(summary: dict[str, Any], context: str) -> dict[str, int]:
    raw_counts = summary.get("counts")
    require(isinstance(raw_counts, dict), f"missing SMT counts in {context}")
    # Normalize historical identifiers in memory; retained evidence stays byte-for-byte intact.
    if "missing_floatlean" in raw_counts and "missing_floatlib" not in raw_counts:
        raw_counts = dict(raw_counts)
        raw_counts["missing_floatlib"] = raw_counts.pop("missing_floatlean")
    require(
        set(raw_counts) == SMT_COUNT_KEYS,
        f"unexpected SMT count keys in {context}: {sorted(raw_counts)!r}",
    )
    counts = {
        key: integer(value, f"{context}:counts:{key}")
        for key, value in raw_counts.items()
    }
    require(
        counts["generated"]
        == counts["exact_bit_cases"] + counts["nan_class_cases"],
        f"SMT generated-case total is inconsistent in {context}",
    )
    require(
        counts["mismatches"]
        == counts["bit_mismatches"] + counts["nan_class_mismatches"],
        f"SMT mismatch total is inconsistent in {context}",
    )
    for key in (
        "bit_mismatches",
        "mismatches",
        "missing_floatlib",
        "nan_class_mismatches",
        "protocol_errors",
        "tool_failures",
    ):
        require(counts[key] == 0, f"SMT {key} is nonzero in {context}")
    require(summary.get("status") == "pass", f"SMT status is not pass in {context}")
    if "mismatch_samples" in summary:
        require(
            summary["mismatch_samples"] == [],
            f"SMT mismatch samples are retained despite pass status in {context}",
        )
    return counts


def verify_smt_results(path: Path, expected_cases: int) -> None:
    columns = [
        "id",
        "operation",
        "source",
        "destination",
        "rounding",
        "operands",
        "solver_kind",
        "solver_bits",
        "floatlib_bits",
        "match",
    ]
    with path.open(newline="", encoding="utf-8") as stream:
        header = next(csv.reader(stream, delimiter="\t"), [])
    historical_columns = [
        "floatlean_bits" if name == "floatlib_bits" else name for name in columns
    ]
    if header == historical_columns:
        columns = historical_columns
    rows = table(path, columns, delimiter="\t")
    require(
        len(rows) == expected_cases,
        f"SMT retained row count differs in {path}: "
        f"{len(rows)} != {expected_cases}",
    )
    identifiers: set[str] = set()
    for line_number, row in enumerate(rows, start=2):
        identifier = row["id"]
        require(
            identifier and identifier not in identifiers,
            f"empty or duplicate SMT row ID in {path}:{line_number}",
        )
        identifiers.add(identifier)
        require(
            row["match"] == "true",
            f"SMT mismatch retained in {path}:{line_number}",
        )


def verify_release_smt(root: Path) -> None:
    summary = json_object(root / "summary.json")
    counts = smt_counts(summary, str(root / "summary.json"))
    require(
        counts["generated"] == 27492,
        f"release SMT case count differs: {counts['generated']} != 27492",
    )
    verify_smt_results(root / "results.tsv", counts["generated"])


def verify_ecosystem_smt(root: Path) -> None:
    aggregate_path = root / "aggregate-summary.json"
    aggregate = json_object(aggregate_path)
    counts = smt_counts(aggregate, str(aggregate_path))
    require(
        counts["generated"] == 147876,
        f"ecosystem SMT case count differs: {counts['generated']} != 147876",
    )
    summaries_raw = aggregate.get("summaries")
    require(
        isinstance(summaries_raw, list) and summaries_raw,
        f"missing SMT run summaries in {aggregate_path}",
    )
    require(
        integer(aggregate.get("runs"), f"{aggregate_path}:runs", minimum=1)
        == len(summaries_raw),
        f"SMT run count differs in {aggregate_path}",
    )
    require(
        integer(
            aggregate.get("sampled_runs"),
            f"{aggregate_path}:sampled_runs",
        )
        + 1
        == len(summaries_raw),
        f"SMT sampled-run count differs in {aggregate_path}",
    )

    seen: set[str] = set()
    derived = Counter()
    for raw_relative in summaries_raw:
        require(
            isinstance(raw_relative, str),
            f"non-string SMT summary path in {aggregate_path}",
        )
        relative = safe_relative(raw_relative, str(aggregate_path))
        require(
            raw_relative not in seen,
            f"duplicate SMT summary path in {aggregate_path}: {raw_relative}",
        )
        seen.add(raw_relative)
        summary_path = root / relative
        run_counts = smt_counts(
            json_object(summary_path),
            str(summary_path),
        )
        derived.update(run_counts)
        verify_smt_results(summary_path.parent / "results.tsv", run_counts["generated"])
    require(
        dict(derived) == counts,
        f"SMT per-run counters do not reproduce {aggregate_path}: "
        f"{dict(derived)!r}",
    )


def verify_softposit(root: Path) -> None:
    columns = [
        "family",
        "bits",
        "operation",
        "mode",
        "status",
        "cases",
        "mismatches",
        "log",
    ]
    rows = table(root / "summary.csv", columns)
    require(len(rows) == 100, f"expected 100 SoftPosit rows in {root}")
    expected_status_files: set[str] = set()
    total_cases = 0
    total_mismatches = 0
    identities: set[tuple[str, str, str, str]] = set()
    for line_number, row in enumerate(rows, start=2):
        identity = tuple(
            row[name] for name in ("family", "bits", "operation", "mode")
        )
        require(
            all(identity) and identity not in identities,
            f"empty or duplicate SoftPosit row in "
            f"{root}/summary.csv:{line_number}: {identity!r}",
        )
        identities.add(identity)
        cases = integer(
            row["cases"],
            f"{root}/summary.csv:{line_number}:cases",
            minimum=1,
        )
        mismatches = integer(
            row["mismatches"],
            f"{root}/summary.csv:{line_number}:mismatches",
        )
        expected_status = "pass" if mismatches == 0 else "fail"
        require(
            row["status"] == expected_status,
            f"SoftPosit status contradicts its mismatch count in "
            f"{root}/summary.csv:{line_number}",
        )
        log = safe_relative(
            row["log"],
            f"{root}/summary.csv:{line_number}:log",
        )
        require((root / log).is_file(), f"missing SoftPosit log: {root / log}")
        status_name = "-".join(identity) + ".tsv"
        expected_status_files.add(status_name)
        status_path = root / "status" / status_name
        require(status_path.is_file(), f"missing SoftPosit status row: {status_path}")
        status_values = status_path.read_text(encoding="utf-8").splitlines()
        require(
            status_values == ["\t".join(row[name] for name in columns)],
            f"SoftPosit status row differs from summary: {status_path}",
        )
        total_cases += cases
        total_mismatches += mismatches
    actual_status_files = {
        path.name for path in (root / "status").glob("*.tsv") if path.is_file()
    }
    require(
        actual_status_files == expected_status_files,
        "SoftPosit status-file set differs from summary rows",
    )
    require(
        (total_cases, total_mismatches) == (23718760, 7562),
        f"SoftPosit retained totals differ: "
        f"cases={total_cases}, mismatches={total_mismatches}",
    )
    require(
        (root / "ADJUDICATION.md").is_file(),
        "SoftPosit external limitation is missing its adjudication record",
    )


def verify_transcendental_providers(
    summary: dict[str, Any],
    path: Path,
    rows: list[dict[str, Any]],
) -> None:
    """Each provider evaluated what it supports, and its rows count those cases."""

    evaluated: Counter[str] = Counter()
    for row in rows:
        evaluated[str(row.get("candidate"))] += int(row["cases"])
    coverage = summary.get("provider_coverage")
    require(isinstance(coverage, list) and coverage, f"missing provider coverage in {path}")
    providers: set[str] = set()
    for entry_number, entry in enumerate(coverage, start=1):
        require(
            isinstance(entry, dict),
            f"invalid provider coverage entry {entry_number} in {path}",
        )
        name = entry.get("name")
        require(
            isinstance(name, str) and name and name not in providers,
            f"empty or duplicate provider coverage in {path}: {name!r}",
        )
        providers.add(name)
        actual = integer(
            entry.get("actual_evaluations"),
            f"{path}:provider:{name}:actual",
            minimum=1,
        )
        expected = integer(
            entry.get("expected_evaluations"),
            f"{path}:provider:{name}:expected",
            minimum=1,
        )
        require(
            actual == expected,
            f"provider coverage is incomplete for {name!r} in {path}: "
            f"{actual} != {expected}",
        )
        require(
            evaluated[name] == actual,
            f"summary rows of {name!r} cover {evaluated[name]} cases, not its "
            f"{actual} evaluations, in {path}",
        )
    require(
        providers == TRANSCENDENTAL_PROVIDERS,
        f"transcendental providers differ in {path}: {sorted(providers)!r}",
    )


def verify_transcendental_rows(
    summary: dict[str, Any],
    path: Path,
    keys: tuple[str, ...],
) -> list[dict[str, Any]]:
    """Check each summary row and that `keys` identify the rows uniquely."""

    summaries = summary.get("summaries")
    require(
        isinstance(summaries, list) and summaries,
        f"missing transcendental summary rows in {path}",
    )
    identities: set[tuple[str, ...]] = set()
    buckets = [
        "ulp_0",
        "ulp_1",
        "ulp_2_3",
        "ulp_4_15",
        "ulp_16_255",
        "ulp_256_plus",
    ]
    for row_number, row in enumerate(summaries, start=1):
        require(
            isinstance(row, dict),
            f"invalid transcendental summary row {row_number} in {path}",
        )
        identity = tuple(str(row.get(name, "")) for name in keys)
        require(
            all(identity) and identity not in identities,
            f"empty or duplicate transcendental summary identity in {path}: "
            f"{identity!r}",
        )
        identities.add(identity)
        cases = integer(
            row.get("cases"),
            f"{path}:summary:{identity}:cases",
            minimum=1,
        )
        finite = integer(
            row.get("finite_pairs"),
            f"{path}:summary:{identity}:finite_pairs",
        )
        require(finite <= cases, f"finite-pair count exceeds cases in {path}")
        for name in ("value_exact", "bit_exact"):
            value = integer(row.get(name), f"{path}:summary:{identity}:{name}")
            require(value <= cases, f"{name} exceeds cases in {path}: {identity!r}")
        nonfinite = integer(
            row.get("nonfinite_mismatch"),
            f"{path}:summary:{identity}:nonfinite_mismatch",
        )
        require(
            nonfinite <= cases - finite,
            f"nonfinite mismatch count is inconsistent in {path}: {identity!r}",
        )
        bucket_total = sum(
            integer(row.get(name), f"{path}:summary:{identity}:{name}")
            for name in buckets
        )
        require(
            bucket_total == finite,
            f"ULP buckets do not cover finite pairs in {path}: {identity!r}",
        )
    return summaries


def verify_observational_transcendental(
    summary: dict[str, Any],
    path: Path,
) -> list[dict[str, Any]]:
    """The retained campaign, which predates the gate."""

    require(
        summary.get("status") == "observational_complete",
        f"transcendental observation is incomplete in {path}",
    )
    require(
        integer(summary.get("cases"), f"{path}:cases", minimum=1) == 4109,
        f"transcendental retained input count differs in {path}",
    )
    rows = verify_transcendental_rows(
        summary,
        path,
        ("candidate", "format_name", "operation"),
    )
    require(len(rows) == 46, f"expected 46 transcendental summary rows in {path}")
    return rows


def json_count(value: object, context: str) -> int:
    """A nonnegative JSON integer, not a string, float or Boolean."""
    require(
        type(value) is int and value >= 0,
        f"{context} is not a nonnegative integer: {value!r}",
    )
    return value


def canonical(value: object) -> str:
    """JSON text that tells 7 from 7.0 and "7", for exact comparisons."""
    return json.dumps(value, sort_keys=True)


def verify_gated_transcendental(
    summary: dict[str, Any],
    root: Path,
    census: Path,
) -> list[dict[str, Any]]:
    """A known-failure gate run: the gate passed, its coverage matched the release entry
    of `census`, and its summary rows and provider coverage are what the report computes
    from the retained `details.tsv`, whose case ids reproduce that entry.

    The details cannot replay the gate itself: they hold no FloatLib ternary and the
    run's known-failures list is not retained, so the gate's classification and its
    counts of matched and unexercised known failures are trusted beyond the bounds
    checked here, as are the MPFR results, the provider libraries and the run itself.
    """

    path = root / "summary.json"
    require(
        summary.get("status") == "gate_pass",
        f"transcendental gate did not pass in {path}",
    )
    gate = summary.get("gate")
    require(isinstance(gate, dict), f"missing transcendental gate counts in {path}")
    for name in TRANSCENDENTAL_GATE_FAILURES:
        require(
            json_count(gate.get(name), f"{path}:gate:{name}") == 0,
            f"transcendental gate records {name} in {path}",
        )
    matched = json_count(gate.get("known_failures_matched"), f"{path}:gate:matched")
    json_count(gate.get("known_failures_not_exercised"), f"{path}:gate:not_exercised")

    coverage = summary.get("coverage")
    require(
        isinstance(coverage, dict)
        and coverage.get("status") == "checked"
        and coverage.get("census") == TRANSCENDENTAL_CENSUS
        and coverage.get("differences") == [],
        f"transcendental coverage did not match census entry "
        f"{TRANSCENDENTAL_CENSUS!r} in {path}",
    )
    recorded = transcendental_report.read_census(census)
    require(
        TRANSCENDENTAL_CENSUS in recorded,
        f"{census} has no entry {TRANSCENDENTAL_CENSUS!r}",
    )
    entry = asdict(recorded[TRANSCENDENTAL_CENSUS])
    require(
        canonical(coverage.get("entry")) == canonical(entry),
        f"the census entry in {path} is not the {TRANSCENDENTAL_CENSUS!r} entry "
        f"of {census}",
    )
    manifest = summary.get("manifest")
    require(
        isinstance(manifest, dict)
        and all(
            isinstance(values, list) and all(isinstance(value, str) for value in values)
            for values in manifest.values()
        ),
        f"invalid transcendental manifest in {path}",
    )
    recorded_manifest = transcendental_report.manifest_entries(list(entry["manifest"]))
    require(
        {key: sorted(values) for key, values in manifest.items()}
        == {key: sorted(values) for key, values in recorded_manifest.items()},
        f"transcendental manifest differs from its census entry in {path}",
    )

    details = root / "details.tsv"
    require(details.is_file(), f"missing retained transcendental details: {details}")
    cases, results = transcendental_report.read_details(details)
    require(
        list(results) == ["FloatLib", *transcendental_report.PROVIDER_SYMBOLS],
        f"transcendental details candidates differ in {details}: {list(results)!r}",
    )
    # A provider has a result exactly for the cases it supports, as the report runs it.
    for name, symbols in transcendental_report.PROVIDER_SYMBOLS.items():
        groups = set(symbols())
        for case, output in zip(cases, results[name], strict=True):
            supported = transcendental_report.supported_by(groups, case)
            require(
                (output is not None) == supported,
                f"{name} has a result for {case.case_id} in {details} exactly when it "
                "does not support it",
            )
    requests, counts, digest = transcendental_report.census_counts(cases)
    recorded_counts = (
        entry["requests"],
        entry["requests_by_operation"],
        entry["case_ids_sha256"],
    )
    require(
        (requests, counts, digest) == recorded_counts,
        f"the case ids in {details} do not reproduce the census entry",
    )
    require(
        json_count(summary.get("cases"), f"{path}:cases") == requests,
        f"transcendental case count differs from {details} in {path}",
    )
    rows = summary.get("summaries")
    expected_rows = [
        asdict(row) for row in transcendental_report.summarize(cases, results)
    ]
    require(
        canonical(rows) == canonical(expected_rows),
        f"transcendental summary rows differ from those computed from {details}",
    )
    expected_coverage = [
        transcendental_report.provider_coverage(
            name, set(symbols()), cases, results[name]
        )
        for name, symbols in transcendental_report.PROVIDER_SYMBOLS.items()
    ]
    require(
        canonical(summary.get("provider_coverage")) == canonical(expected_coverage),
        f"transcendental provider coverage differs from {details} in {path}",
    )
    providers = summary.get("providers")
    require(
        isinstance(providers, list)
        and [
            provider.get("name") if isinstance(provider, dict) else None
            for provider in providers
        ]
        == list(transcendental_report.PROVIDER_SYMBOLS)
        and summary.get("rounding_environment") == "FE_TONEAREST",
        f"transcendental provider metadata differs in {path}",
    )
    # Every value mismatch of a passing gate is a matched known failure; a ternary-only
    # difference is one too, so the count may exceed the value mismatches.
    mismatches = sum(
        not transcendental_report.value_matches(case.floatlib, case.mpfr, case.fmt)
        for case in cases
    )
    require(
        mismatches <= matched <= requests,
        f"{matched} matched known failures cannot cover {mismatches} FloatLib value "
        f"mismatches in {requests} cases in {path}",
    )
    return rows


def verify_transcendental(
    root: Path,
    census: Path = TRANSCENDENTAL_CENSUS_FILE,
) -> None:
    path = root / "summary.json"
    summary = json_object(path)
    kind = transcendental_kind(root)
    require(
        summary.get("conformance") is False,
        f"transcendental comparison is mislabeled as conformance in {path}",
    )
    if kind == "observational":
        rows = verify_observational_transcendental(summary, path)
    else:
        rows = verify_gated_transcendental(summary, root, census)
    verify_transcendental_providers(summary, path, rows)


def verify_zero_exit(raw: Path, suite: str) -> None:
    status = assignments(raw / suite / "status.env")
    require(
        status.get("status") == "0",
        f"{suite} did not retain a successful upstream exit: {status!r}",
    )


def verify_core_math(raw: Path) -> None:
    root = raw / "core-math"
    status = assignments(root / "status.env")
    expected_status = {
        "status": "qualified-pass",
        "functions": "169",
        "passed": "166",
        "failed": "3",
    }
    for key, value in expected_status.items():
        require(
            status.get(key) == value,
            f"CORE-MATH status {key} differs: {status.get(key)!r} != {value!r}",
        )
    rows = table(
        root / "functions.tsv",
        ["family", "function", "status"],
        delimiter="\t",
    )
    require(len(rows) == 169, f"expected 169 CORE-MATH rows, found {len(rows)}")
    keys = {(row["family"], row["function"]) for row in rows}
    require(len(keys) == len(rows), "CORE-MATH contains duplicate function rows")
    family_counts = Counter(row["family"] for row in rows)
    expected_families = {
        "binary16": 43,
        "binaryb16": 43,
        "binary32": 42,
        "binary64": 41,
    }
    require(
        family_counts == expected_families,
        f"CORE-MATH family counts differ: {dict(family_counts)!r}",
    )
    failures = {
        (row["family"], row["function"], row["status"])
        for row in rows
        if row["status"] != "PASS"
    }
    expected_failures = {
        ("binary16", "compoundf16", "FAIL(2)"),
        ("binaryb16", "compound_bf16", "FAIL(2)"),
        ("binary32", "compoundf", "FAIL(2)"),
    }
    require(
        failures == expected_failures,
        f"CORE-MATH retained failures differ: {failures!r}",
    )


def verify_exblas(raw: Path) -> None:
    root = raw / "exblas"
    verify_zero_exit(raw, "exblas")
    require(
        assignments(root / "summary.env")
        == {
            "exact_cases": "4",
            "exact_failures": "0",
            "composite_passes": "3",
        },
        "ExBLAS summary counters differ",
    )
    rows = table(
        root / "exsum-summary.tsv",
        ["case", "exit_status", "exact_superacc_mpfr", "all_expansions"],
        delimiter="\t",
    )
    require(len(rows) == 4, f"expected four retained ExBLAS cases in {root}")
    require(
        all(row["exit_status"] == "0" for row in rows),
        "an ExBLAS retained case has a nonzero exit status",
    )
    require(
        all(row["exact_superacc_mpfr"] == "pass" for row in rows),
        "an ExBLAS exact-superaccumulator case did not pass",
    )
    require(
        Counter(row["all_expansions"] for row in rows)
        == {"pass": 3, "fail": 1},
        "ExBLAS expansion qualification differs",
    )


def verify_qualified_ecosystem_rows(raw: Path) -> None:
    verify_exblas(raw)

    verify_zero_exit(raw, "reproblas")
    require(
        assignments(raw / "reproblas" / "component-status.env")
        == {"accuracy_target_status": "2"},
        "ReproBLAS qualification reason differs",
    )

    verify_zero_exit(raw, "fpbench")
    require(
        assignments(raw / "fpbench" / "outcome.env")
        == {
            "upstream_ci_targets": "pass",
            "standalone_filter_status": "1",
        },
        "FPBench qualification counters differ",
    )

    verify_zero_exit(raw, "verificarlo")
    require(
        assignments(raw / "verificarlo" / "outcome.env")
        == {"installcheck_status": "0"},
        "Verificarlo install-check status differs",
    )

    verify_zero_exit(raw, "rlibm-all")
    rlibm_rows = table(
        raw / "rlibm-all" / "mainstream-summary.tsv",
        ["format", "library", "function", "modes"],
        delimiter="\t",
    )
    require(len(rlibm_rows) == 46, "RLIBM mainstream summary row count differs")
    require(
        all(re.fullmatch(r"[ox]{5}", row["modes"]) for row in rlibm_rows),
        "RLIBM mode summaries use an unexpected encoding",
    )
    require(
        any("x" in row["modes"] for row in rlibm_rows),
        "RLIBM qualification no longer records unavailable modes",
    )

    verify_core_math(raw)


def verify_flit(raw: Path, suites: set[str]) -> None:
    for suite in sorted(suites):
        variant = suite.removeprefix("flit-")
        root = raw / suite
        verify_zero_exit(raw, suite)
        require(
            assignments(root / "versions.env")
            == {
                "flit_revision": FLIT_REVISION,
                "variant": variant,
            },
            f"{suite} version record differs",
        )
        require(
            assignments(root / "summary.env")
            == {
                "configurations": "140",
                "comparison_csvs": "140",
                "imported_database": "1",
            },
            f"{suite} retained counters differ",
        )
        comparisons = list((root / "results").glob("*-out-comparison.csv"))
        require(
            len(comparisons) == 140,
            f"{suite} retained {len(comparisons)} comparison CSVs",
        )
        require(
            all(path.stat().st_size > 0 for path in comparisons),
            f"{suite} retained an empty comparison CSV",
        )
        config = (root / "flit-config.toml").read_text(encoding="utf-8")
        require("timing = false" in config, f"{suite} did not disable timing")
        expected_mpi = "false" if variant == "base" else "true"
        require(
            f"enable_mpi = {expected_mpi}" in config,
            f"{suite} has the wrong MPI setting",
        )
        database_path = root / "results.sqlite"
        require(database_path.is_file(), f"{suite} is missing results.sqlite")
        database = sqlite3.connect(f"file:{database_path}?mode=ro", uri=True)
        try:
            integrity = database.execute("PRAGMA integrity_check").fetchone()
            tables = {
                row[0]
                for row in database.execute(
                    "SELECT name FROM sqlite_master WHERE type = 'table'"
                )
            }
        finally:
            database.close()
        require(integrity == ("ok",), f"{suite} SQLite integrity check failed")
        require(
            {"runs", "tests"} <= tables,
            f"{suite} SQLite tables differ: {sorted(tables)!r}",
        )


def verify_ecosystem_raw(ecosystem: Path, flit_suites: set[str]) -> None:
    raw = ecosystem / "raw"
    for suite in ("daisy", "fptaylor", "herbie", "openlibm"):
        verify_zero_exit(raw, suite)
    verify_qualified_ecosystem_rows(raw)
    verify_ecosystem_smt(raw / "smt-qf-fp")
    verify_zero_exit(raw, "smt-qf-fp")
    verify_transcendental(raw / "transcendental-direct" / "comparison")
    verify_zero_exit(raw, "transcendental-direct")
    verify_flit(raw, flit_suites)


def verify(release: Path, ecosystem: Path) -> None:
    release = release.resolve()
    ecosystem = ecosystem.resolve()
    verify_release_summary(release)
    verify_release_aggregate_logs(release)
    flit_suites = verify_ecosystem_summary(ecosystem)

    verify_testfloat(
        release / "01-testfloat",
        profile="full",
        level=1,
        campaigns=175,
        cases=102454320,
    )
    verify_format_standards(release / "02-format-standards")
    verify_testfloat(
        release / "08-testfloat-level2-smoke",
        profile="smoke",
        level=2,
        campaigns=3,
        cases=1272128,
    )
    verify_ibm_fpgen(release / "09-ibm-fpgen")
    verify_release_smt(release / "10-smt-qf-fp")
    verify_softposit(release / "11-softposit")
    verify_transcendental(release / "12-transcendentals")
    verify_ecosystem_raw(ecosystem, flit_suites)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path)
    parser.add_argument("ecosystem", type=Path)
    arguments = parser.parse_args()
    try:
        verify(arguments.release, arguments.ecosystem)
    except (OSError, sqlite3.Error, ValueError) as error:
        raise SystemExit(str(error)) from error
    print("verified retained release and ecosystem evidence")


if __name__ == "__main__":
    main()
