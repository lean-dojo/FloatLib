#!/usr/bin/env python3
"""Convert IBM FPgen vectors into streams accepted by FloatLib's TestFloat checker.

The public ieee754-test-suite stores floating-point values semantically rather
than as packed bits.  This adapter validates those semantic fields, encodes
them exactly, and keeps a source map for every emitted checker row.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from collections import Counter
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from pathlib import Path

PINNED_REVISION = "12e883a0c7b826976a8f1243318ac4b7626a0ffc"
PINNED_URL = "https://github.com/sergev/ieee754-test-suite.git"


@dataclass(frozen=True)
class BinaryFormat:
    name: str
    exponent_bits: int
    fraction_bits: int

    @property
    def bias(self) -> int:
        return (1 << (self.exponent_bits - 1)) - 1

    @property
    def minimum_normal_exponent(self) -> int:
        return 1 - self.bias

    @property
    def maximum_normal_exponent(self) -> int:
        return ((1 << self.exponent_bits) - 2) - self.bias

    @property
    def width(self) -> int:
        return 1 + self.exponent_bits + self.fraction_bits

    @property
    def hex_digits(self) -> int:
        return (self.width + 3) // 4


F32 = BinaryFormat("f32", 8, 23)
F64 = BinaryFormat("f64", 11, 52)
F128 = BinaryFormat("f128", 15, 112)


@dataclass(frozen=True)
class Operation:
    checker_name: str
    operands: int
    input_format: BinaryFormat
    output_format: BinaryFormat
    boolean_result: bool = False


OPERATIONS = {
    "b32+": Operation("add", 2, F32, F32),
    "b32-": Operation("sub", 2, F32, F32),
    "b32*": Operation("mul", 2, F32, F32),
    "b32/": Operation("div", 2, F32, F32),
    "b32*+": Operation("mulAdd", 3, F32, F32),
    "b32V": Operation("sqrt", 1, F32, F32),
    "b32<C": Operation("minNum", 2, F32, F32),
    "b32>C": Operation("maxNum", 2, F32, F32),
    "b32>A": Operation("maxNumMag", 2, F32, F32),
    "b32cp": Operation("copy", 1, F32, F32),
    "b32~": Operation("neg", 1, F32, F32),
    "b32A": Operation("abs", 1, F32, F32),
    "b32?sN": Operation("isSNaN", 1, F32, F32, boolean_result=True),
    "b32?s": Operation("isSubnormal", 1, F32, F32, boolean_result=True),
    "b32?n": Operation("isNormal", 1, F32, F32, boolean_result=True),
    "b32?i": Operation("isInf", 1, F32, F32, boolean_result=True),
    "b32?f": Operation("isFinite", 1, F32, F32, boolean_result=True),
    "b32?N": Operation("isNaN", 1, F32, F32, boolean_result=True),
    "b32?0": Operation("isZero", 1, F32, F32, boolean_result=True),
    "b32?-": Operation("signBit", 1, F32, F32, boolean_result=True),
    "b32b64cff": Operation("to_f64", 1, F32, F64),
    "b32b128cff": Operation("to_f128", 1, F32, F128),
}

ROUNDING_MODES = {
    "=0": "near_even",
    "0": "minMag",
    "<": "min",
    ">": "max",
}
SUITE_ROUNDING_MODES = frozenset((*ROUNDING_MODES, "=^"))

CASE_OPERATION = re.compile(r"^[bd]\d+")
FINITE_VALUE = re.compile(
    r"^(?P<sign>[+-])(?P<leading>[01])\."
    r"(?P<fraction>[0-9A-Fa-f]+)P(?P<exponent>[+-]?\d+)$"
)
TRAP_FLAGS = frozenset("xuozi")
RAISED_FLAGS = frozenset("xuvwozi")


class AdapterError(ValueError):
    """A malformed suite row or semantic value."""


@dataclass(frozen=True)
class Source:
    path: Path
    relative_path: str
    line_number: int
    text: str

    def error(self, message: str) -> AdapterError:
        return AdapterError(f"{self.path}:{self.line_number}: {message}")


@dataclass(frozen=True)
class ParsedCase:
    operation: Operation
    rounding: str
    traps: frozenset[str]
    operands: tuple[str, ...]
    result: str
    raised: frozenset[str]


@dataclass(frozen=True, order=True)
class Group:
    format_name: str
    operation: str
    rounding: str

    @property
    def stem(self) -> str:
        return f"{self.format_name}_{self.operation}_{self.rounding}"


@dataclass(frozen=True)
class EmittedCase:
    group: Group
    fields: tuple[str, ...]
    source: Source


def parse_flag_field(
    text: str,
    allowed: frozenset[str],
    name: str,
    source: Source,
) -> frozenset[str]:
    if not text:
        raise source.error(f"empty {name} field")
    invalid = sorted(set(text) - allowed)
    if invalid:
        raise source.error(f"invalid {name} flag(s) in {text!r}: {''.join(invalid)}")
    if len(set(text)) != len(text):
        raise source.error(f"duplicate {name} flag in {text!r}")
    underflow_spellings = set(text) & set("uvw")
    if name == "raised-exception" and len(underflow_spellings) > 1:
        raise source.error(f"multiple underflow conventions in {text!r}")
    return frozenset(text)


def parse_supported_case(
    fields: list[str],
    operation: Operation,
    source: Source,
) -> ParsedCase:
    try:
        arrow = fields.index("->")
    except ValueError as error:
        raise source.error("missing '->' separator") from error
    if fields.count("->") != 1:
        raise source.error("expected exactly one '->' separator")
    if len(fields) < 4:
        raise source.error("incomplete test case")

    rounding_token = fields[1]
    if rounding_token not in ROUNDING_MODES:
        raise source.error(
            f"unsupported rounding mode reached parser: {rounding_token!r}"
        )

    before = fields[2:arrow]
    after = fields[arrow + 1 :]
    if len(before) == operation.operands:
        traps = frozenset()
        operands = before
    elif len(before) == operation.operands + 1:
        traps = parse_flag_field(before[0], TRAP_FLAGS, "trap", source)
        operands = before[1:]
    else:
        raise source.error(
            f"expected {operation.operands} operand(s), with at most one trap field; "
            f"found {len(before)} pre-arrow field(s)"
        )

    if len(after) == 1:
        result = after[0]
        raised = frozenset()
    elif len(after) == 2:
        result = after[0]
        raised = parse_flag_field(after[1], RAISED_FLAGS, "raised-exception", source)
    else:
        raise source.error(
            f"expected a result and optional raised-exception field; found {len(after)} field(s)"
        )

    return ParsedCase(
        operation=operation,
        rounding=ROUNDING_MODES[rounding_token],
        traps=traps,
        operands=tuple(operands),
        result=result,
        raised=raised,
    )


def encode_binary(text: str, fmt: BinaryFormat) -> int:
    sign_mask = 1 << (fmt.width - 1)
    exponent_mask = (1 << fmt.exponent_bits) - 1
    fraction_mask = (1 << fmt.fraction_bits) - 1

    if text == "Q":
        return (exponent_mask << fmt.fraction_bits) | (1 << (fmt.fraction_bits - 1))
    if text == "S":
        return (exponent_mask << fmt.fraction_bits) | 1
    if text in {"+Inf", "-Inf"}:
        sign = sign_mask if text.startswith("-") else 0
        return sign | (exponent_mask << fmt.fraction_bits)
    if text in {"+Zero", "-Zero"}:
        return sign_mask if text.startswith("-") else 0

    match = FINITE_VALUE.fullmatch(text)
    if match is None:
        raise AdapterError(f"invalid {fmt.name} semantic number: {text!r}")

    sign = sign_mask if match.group("sign") == "-" else 0
    leading = int(match.group("leading"))
    fraction_text = match.group("fraction")
    required_digits = (fmt.fraction_bits + 3) // 4
    if len(fraction_text) != required_digits:
        raise AdapterError(
            f"{fmt.name} fraction in {text!r} has {len(fraction_text)} hexadecimal digit(s); "
            f"expected {required_digits}"
        )
    fraction = int(fraction_text, 16)
    if fraction > fraction_mask:
        raise AdapterError(
            f"{fmt.name} fraction exceeds {fmt.fraction_bits} bits in {text!r}"
        )

    exponent = int(match.group("exponent"))
    if leading == 0:
        if exponent != fmt.minimum_normal_exponent:
            raise AdapterError(
                f"{fmt.name} subnormal in {text!r} must use exponent "
                f"{fmt.minimum_normal_exponent}"
            )
        if fraction == 0:
            raise AdapterError(f"{fmt.name} zero must use +Zero or -Zero, not {text!r}")
        encoded_exponent = 0
    else:
        if not fmt.minimum_normal_exponent <= exponent <= fmt.maximum_normal_exponent:
            raise AdapterError(
                f"{fmt.name} normal exponent {exponent} is outside "
                f"[{fmt.minimum_normal_exponent}, {fmt.maximum_normal_exponent}]"
            )
        encoded_exponent = exponent + fmt.bias

    return sign | (encoded_exponent << fmt.fraction_bits) | fraction


def format_bits(bits: int, fmt: BinaryFormat) -> str:
    return f"{bits:0{fmt.hex_digits}x}"


def normalized_exceptions(flags: Iterable[str]) -> frozenset[str]:
    return frozenset("u" if flag in "uvw" else flag for flag in flags)


def trap_was_delivered(parsed: ParsedCase) -> bool:
    return bool(parsed.traps & normalized_exceptions(parsed.raised))


def status_bits(raised: frozenset[str], result_bits: int, fmt: BinaryFormat) -> int:
    inexact = "x" in raised
    return (
        (1 if inexact else 0)
        | (2 if "v" in raised else 0)
        | (4 if "o" in raised else 0)
        | (8 if "z" in raised else 0)
        | (16 if "i" in raised else 0)
    )


def has_unspecified_nan_sign(parsed: ParsedCase) -> bool:
    """Whether the suite discarded information needed by the requested operation."""

    return (
        parsed.operation.checker_name == "signBit"
        and any(operand in {"Q", "S"} for operand in parsed.operands)
    )


def uses_legacy_nan_precedence(parsed: ParsedCase) -> bool:
    """Whether IBM's first-NaN rule suppresses a later signaling-NaN exception."""

    first_nan = next(
        (
            (index, operand)
            for index, operand in enumerate(parsed.operands)
            if operand in {"Q", "S"}
        ),
        None,
    )
    if first_nan is None:
        return False
    index, kind = first_nan
    return (
        kind == "Q"
        and "S" in parsed.operands[index + 1 :]
        and "i" not in parsed.raised
    )


def uses_non_after_rounding_underflow(parsed: ParsedCase) -> bool:
    """Whether the row uses an underflow convention different from FloatLib's."""

    return bool(parsed.raised & frozenset("uw"))


def emit_case(parsed: ParsedCase, source: Source) -> EmittedCase:
    try:
        inputs = tuple(
            format_bits(
                encode_binary(value, parsed.operation.input_format),
                parsed.operation.input_format,
            )
            for value in parsed.operands
        )
        if parsed.operation.boolean_result:
            if parsed.result not in {"0x0", "0x1"}:
                raise AdapterError(
                    f"invalid Boolean result for {parsed.operation.checker_name}: "
                    f"{parsed.result!r}"
                )
            result_bits = int(parsed.result, 16)
        else:
            result_bits = encode_binary(parsed.result, parsed.operation.output_format)
    except AdapterError as error:
        raise source.error(str(error)) from error

    result = (
        str(result_bits)
        if parsed.operation.boolean_result
        else format_bits(result_bits, parsed.operation.output_format)
    )
    flags = (
        f"{status_bits(parsed.raised, result_bits, parsed.operation.output_format):x}"
    )
    group = Group(
        parsed.operation.input_format.name,
        parsed.operation.checker_name,
        parsed.rounding,
    )
    return EmittedCase(group, inputs + (result, flags), source)


def suite_sources(suite: Path) -> Iterator[Source]:
    files = sorted(suite.rglob("*.fptest"))
    if not files:
        raise AdapterError(f"no .fptest files found under {suite}")
    for path in files:
        relative = path.relative_to(suite).as_posix()
        with path.open("r", encoding="utf-8-sig", newline="") as stream:
            for line_number, line in enumerate(stream, 1):
                yield Source(path, relative, line_number, line.rstrip("\r\n"))


def classify_suite(suite: Path) -> tuple[Counter[str], list[EmittedCase]]:
    counters: Counter[str] = Counter()
    emitted: list[EmittedCase] = []
    seen_files: set[str] = set()

    for source in suite_sources(suite):
        counters["lines"] += 1
        seen_files.add(source.relative_path)
        fields = source.text.strip().split()
        if not fields or CASE_OPERATION.match(fields[0]) is None:
            counters["non_case_lines"] += 1
            continue

        counters["case_records"] += 1
        operation_token = fields[0]
        if operation_token.startswith("d"):
            counters["decimal"] += 1
            continue

        operation = OPERATIONS.get(operation_token)
        if operation is None:
            counters["unsupported"] += 1
            counters["unsupported_operation"] += 1
            continue
        if len(fields) < 2:
            raise source.error("missing rounding-mode field")
        if fields[1] not in SUITE_ROUNDING_MODES:
            raise source.error(f"invalid rounding mode: {fields[1]!r}")
        if fields[1] not in ROUNDING_MODES:
            counters["unsupported"] += 1
            counters["unsupported_rounding_mode"] += 1
            continue

        parsed = parse_supported_case(fields, operation, source)
        if parsed.result == "#":
            counters["no_result"] += 1
            continue
        if trap_was_delivered(parsed):
            counters["trap_produced"] += 1
            continue
        if has_unspecified_nan_sign(parsed):
            counters["unsupported"] += 1
            counters["unsupported_nan_sign"] += 1
            continue
        if uses_legacy_nan_precedence(parsed):
            counters["unsupported"] += 1
            counters["unsupported_nan_precedence"] += 1
            continue
        if uses_non_after_rounding_underflow(parsed):
            counters["unsupported"] += 1
            counters["unsupported_underflow_convention"] += 1
            continue

        emitted.append(emit_case(parsed, source))
        counters["emitted"] += 1

    counters["files"] = len(seen_files)
    classified = sum(
        counters[name]
        for name in ("decimal", "unsupported", "no_result", "trap_produced", "emitted")
    )
    if classified != counters["case_records"]:
        raise AdapterError(
            f"internal classification error: {classified} classified records, "
            f"{counters['case_records']} total"
        )
    unsupported_reasons = sum(
        counters[name]
        for name in (
            "unsupported_operation",
            "unsupported_rounding_mode",
            "unsupported_nan_sign",
            "unsupported_nan_precedence",
            "unsupported_underflow_convention",
        )
    )
    if unsupported_reasons != counters["unsupported"]:
        raise AdapterError(
            f"internal unsupported-case error: {unsupported_reasons} reasoned records, "
            f"{counters['unsupported']} total"
        )
    if not emitted:
        raise AdapterError("suite contains no cases in the supported semantic overlap")
    return counters, emitted


def summary_dict(counters: Counter[str], groups: Counter[Group]) -> dict[str, object]:
    counter_names = (
        "files",
        "lines",
        "non_case_lines",
        "case_records",
        "decimal",
        "unsupported",
        "unsupported_operation",
        "unsupported_rounding_mode",
        "unsupported_nan_sign",
        "unsupported_nan_precedence",
        "unsupported_underflow_convention",
        "no_result",
        "trap_produced",
        "emitted",
    )
    return {
        "pinned_revision": PINNED_REVISION,
        "semantic_overlap": {
            "nan_sign": "Q and S rows are omitted when the operation observes an unspecified sign",
            "nan_precedence": (
                "rows using IBM's quiet-NaN-first exception precedence are omitted"
            ),
            "underflow": (
                "only v (tininess after rounding) is comparable; u and w rows are omitted"
            ),
        },
        "counters": {name: counters[name] for name in counter_names},
        "groups": [
            {
                "format": group.format_name,
                "operation": group.operation,
                "rounding": group.rounding,
                "cases": groups[group],
            }
            for group in sorted(groups)
        ],
    }


def write_outputs(
    output: Path,
    counters: Counter[str],
    cases: list[EmittedCase],
) -> dict[str, object]:
    if output.exists() and any(output.iterdir()):
        raise AdapterError(f"output directory is not empty: {output}")
    output.mkdir(parents=True, exist_ok=True)

    grouped: dict[Group, list[EmittedCase]] = {}
    for case in cases:
        grouped.setdefault(case.group, []).append(case)

    for group in sorted(grouped):
        stream_path = output / f"{group.stem}.stream"
        map_path = output / f"{group.stem}.map.tsv"
        with (
            stream_path.open("w", encoding="utf-8", newline="\n") as stream,
            map_path.open("w", encoding="utf-8", newline="") as map_stream,
        ):
            writer = csv.writer(map_stream, delimiter="\t", lineterminator="\n")
            writer.writerow(("case", "file", "line", "source"))
            for case_number, case in enumerate(grouped[group], 1):
                stream.write(" ".join(case.fields) + "\n")
                writer.writerow(
                    (
                        case_number,
                        case.source.relative_path,
                        case.source.line_number,
                        case.source.text,
                    )
                )

    group_counts = Counter({group: len(grouped[group]) for group in grouped})
    summary = summary_dict(counters, group_counts)
    with (output / "groups.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(
            ("group", "format", "operation", "rounding", "cases", "stream", "map")
        )
        for group in sorted(grouped):
            writer.writerow(
                (
                    group.stem,
                    group.format_name,
                    group.operation,
                    group.rounding,
                    group_counts[group],
                    f"{group.stem}.stream",
                    f"{group.stem}.map.tsv",
                )
            )
    with (output / "summary.json").open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(summary, stream, indent=2, sort_keys=True)
        stream.write("\n")
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Convert the pinned IBM FPgen ieee754-test-suite into FloatLib "
            "TestFloat-checker streams."
        )
    )
    parser.add_argument(
        "--suite", required=True, type=Path, help="ieee754-test-suite checkout"
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="new or empty output directory for streams, maps, and summaries",
    )
    parser.add_argument(
        "--count-only",
        "--dry-run",
        action="store_true",
        dest="count_only",
        help="validate and count the suite without writing files",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if not args.count_only and args.output is None:
        parser.error("--output is required unless --count-only is used")
    if not args.suite.is_dir():
        parser.error(f"suite directory does not exist: {args.suite}")

    try:
        counters, cases = classify_suite(args.suite)
        group_counts = Counter(case.group for case in cases)
        if args.count_only:
            summary = summary_dict(counters, group_counts)
        else:
            summary = write_outputs(args.output, counters, cases)
    except (AdapterError, OSError) as error:
        print(f"ibm_fpgen: {error}", file=sys.stderr)
        return 2

    json.dump(summary, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
