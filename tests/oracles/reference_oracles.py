#!/usr/bin/env python3
"""Compare FloatLib format vectors with independent public references."""

from __future__ import annotations

import argparse
import csv
import math
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, TextIO


@dataclass(frozen=True)
class ExactValue:
    kind: str
    negative: bool = False
    significand: int = 0
    exponent: int = 0
    subnormal: bool = False


def normalized_dyadic(negative: bool, significand: int, exponent: int) -> ExactValue:
    if significand == 0:
        return ExactValue("finite", negative, 0, 0)
    trailing = (significand & -significand).bit_length() - 1
    return ExactValue(
        "finite",
        negative,
        significand >> trailing,
        exponent + trailing,
    )


def parse_lean_row(row: dict[str, str]) -> tuple[str, str, int, ExactValue]:
    kind = row["kind"]
    negative = row["negative"] == "true"
    if kind == "finite":
        value = normalized_dyadic(
            negative,
            int(row["significand"]),
            int(row["exponent"]),
        )
        value = ExactValue(
            value.kind,
            value.negative,
            value.significand,
            value.exponent,
            row["subnormal"] == "true",
        )
    else:
        value = ExactValue(kind, negative)
    return row["family"], row["format"], int(row["code"]), value


def lean_rows(command: list[str]) -> Iterator[tuple[str, str, int, ExactValue]]:
    process = subprocess.Popen(
        command,
        stdout=subprocess.PIPE,
        text=True,
        encoding="utf-8",
    )
    assert process.stdout is not None
    try:
        for row in csv.DictReader(process.stdout):
            yield parse_lean_row(row)
    except BaseException:
        process.stdout.close()
        process.terminate()
        process.wait()
        raise
    process.stdout.close()
    status = process.wait()
    if status != 0:
        raise RuntimeError(f"Lean vector emitter failed with status {status}")


def exact_from_host_float(value: object) -> ExactValue:
    converted = float(value)
    if math.isnan(converted):
        return ExactValue("nan")
    if math.isinf(converted):
        return ExactValue("infinity", math.copysign(1.0, converted) < 0)
    negative = math.copysign(1.0, converted) < 0
    numerator, denominator = converted.as_integer_ratio()
    numerator = abs(numerator)
    exponent = -(denominator.bit_length() - 1)
    return normalized_dyadic(negative, numerator, exponent)


def onnx_values(name: str) -> list[ExactValue]:
    import numpy as np
    from onnx import TensorProto, numpy_helper

    data_types = {
        "e2m1": TensorProto.FLOAT4E2M1,
        "e4m3fn": TensorProto.FLOAT8E4M3FN,
        "e4m3fnuz": TensorProto.FLOAT8E4M3FNUZ,
        "e5m2": TensorProto.FLOAT8E5M2,
        "e5m2fnuz": TensorProto.FLOAT8E5M2FNUZ,
        "e8m0": TensorProto.FLOAT8E8M0,
    }
    if name == "e2m1":
        count = 16
        raw_data = bytes([(2 * index) | ((2 * index + 1) << 4) for index in range(8)])
    else:
        count = 256
        raw_data = bytes(range(256))
    tensor = TensorProto(
        name=name,
        data_type=data_types[name],
        dims=[count],
        raw_data=raw_data,
    )
    values = numpy_helper.to_array(tensor).astype(np.float32)
    return [exact_from_host_float(value) for value in values]


def compare_onnx(emitter: Path) -> tuple[int, int, int]:
    formats = {
        name: onnx_values(name)
        for name in ("e2m1", "e4m3fn", "e4m3fnuz", "e5m2", "e5m2fnuz", "e8m0")
    }
    cases = 0
    mismatches = 0
    seen: dict[str, set[int]] = {name: set() for name in formats}
    for family, name, code, actual in lean_rows([str(emitter), "formats", "onnx"]):
        if family != "onnx" or name not in formats:
            raise RuntimeError(f"unexpected ONNX vector family/format: {family}/{name}")
        if code < 0 or code >= len(formats[name]):
            raise RuntimeError(f"ONNX code out of range: {name} code={code}")
        if code in seen[name]:
            raise RuntimeError(f"duplicate ONNX code: {name} code={code}")
        expected = formats[name][code]
        if actual.kind == "finite":
            actual = ExactValue(
                actual.kind,
                actual.negative,
                actual.significand,
                actual.exponent,
            )
        if actual != expected:
            if mismatches < 20:
                print(
                    f"ONNX mismatch {name} code={code}: "
                    f"FloatLib={actual} ONNX={expected}",
                    file=sys.stderr,
                )
            mismatches += 1
        cases += 1
        seen[name].add(code)
    missing = sum(len(formats[name]) - len(codes) for name, codes in seen.items())
    return len(formats), cases, mismatches + missing


HEX_FLOAT = re.compile(
    r"^(?P<negative>-)?0x(?P<whole>[0-9a-f]+)"
    r"(?:\.(?P<fraction>[0-9a-f]+))?p(?P<exponent>[+-]?\d+)$",
    re.IGNORECASE,
)
FORMAT_NAME = re.compile(
    r"^Binary(?P<width>\d+)p(?P<precision>\d+)(?P<signedness>[su])(?P<domain>[fe])$"
)


def parse_p3109_value(text: str, subnormal: bool) -> ExactValue:
    if text == "NaN":
        return ExactValue("nan")
    if text == "Inf":
        return ExactValue("infinity", False)
    if text == "-Inf":
        return ExactValue("infinity", True)
    match = HEX_FLOAT.fullmatch(text)
    if match is None:
        raise ValueError(f"invalid P3109 hexadecimal value: {text}")
    fraction = match.group("fraction") or ""
    significand = int(match.group("whole") + fraction, 16)
    exponent = int(match.group("exponent")) - 4 * len(fraction)
    value = normalized_dyadic(bool(match.group("negative")), significand, exponent)
    return ExactValue(
        value.kind,
        value.negative,
        value.significand,
        value.exponent,
        subnormal,
    )


def p3109_table_path(root: Path, name: str) -> Path:
    match = FORMAT_NAME.fullmatch(name)
    if match is None:
        raise ValueError(f"invalid P3109 format name: {name}")
    signedness = "signed" if match.group("signedness") == "s" else "unsigned"
    return (
        root
        / "Value Tables"
        / "Hexadecimal"
        / f"K{match.group('width')}"
        / f"P{match.group('precision')}"
        / signedness
        / f"{name}.csv"
    )


def table_rows(stream: TextIO) -> Iterator[tuple[int, ExactValue]]:
    for row in csv.DictReader(stream):
        yield (
            int(row["codepoint"], 16),
            parse_p3109_value(row["value"], row["subnormal"].strip() == "*"),
        )


def p3109_format_names(minimum_width: int, maximum_width: int) -> list[str]:
    names: list[str] = []
    for width in range(minimum_width, maximum_width + 1):
        for precision in range(1, width + 1):
            if precision < width:
                names.extend(
                    (
                        f"Binary{width}p{precision}sf",
                        f"Binary{width}p{precision}se",
                    )
                )
            names.extend(
                (
                    f"Binary{width}p{precision}uf",
                    f"Binary{width}p{precision}ue",
                )
            )
    return names


def compare_p3109(
    emitter: Path,
    source: Path,
    minimum_width: int,
    maximum_width: int,
) -> tuple[int, int, int]:
    formats = 0
    cases = 0
    mismatches = 0
    current_name: str | None = None
    expected_rows: Iterator[tuple[int, ExactValue]] | None = None
    expected_stream: TextIO | None = None
    expected_names = p3109_format_names(minimum_width, maximum_width)

    try:
        for family, name, code, actual in lean_rows(
            [str(emitter), "formats", "p3109", str(minimum_width), str(maximum_width)]
        ):
            if family != "p3109":
                raise RuntimeError(f"unexpected P3109 vector family: {family}")
            if name != current_name:
                if expected_rows is not None:
                    try:
                        next(expected_rows)
                    except StopIteration:
                        pass
                    else:
                        raise RuntimeError(f"published table has extra rows: {current_name}")
                if expected_stream is not None:
                    expected_stream.close()
                current_name = name
                if formats >= len(expected_names) or name != expected_names[formats]:
                    expected_name = (
                        expected_names[formats]
                        if formats < len(expected_names)
                        else "<end of matrix>"
                    )
                    raise RuntimeError(
                        f"unexpected P3109 format order: found {name}, "
                        f"expected {expected_name}"
                    )
                expected_stream = p3109_table_path(source, name).open(
                    newline="",
                    encoding="utf-8",
                )
                expected_rows = table_rows(expected_stream)
                formats += 1

            assert expected_rows is not None
            try:
                expected_code, expected = next(expected_rows)
            except StopIteration as error:
                raise RuntimeError(f"published table ended early: {name}") from error
            if code != expected_code or actual != expected:
                if mismatches < 20:
                    print(
                        f"P3109 mismatch {name} code={code}: "
                        f"FloatLib={actual} table[{expected_code}]={expected}",
                        file=sys.stderr,
                    )
                mismatches += 1
            cases += 1

        if expected_rows is not None:
            try:
                next(expected_rows)
            except StopIteration:
                pass
            else:
                raise RuntimeError(f"published table has extra rows: {current_name}")
    finally:
        if expected_stream is not None:
            expected_stream.close()
    expected_cases = sum(
        (4 * width - 2) * (2**width)
        for width in range(minimum_width, maximum_width + 1)
    )
    if formats != len(expected_names) or cases != expected_cases:
        raise RuntimeError(
            "incomplete P3109 matrix: "
            f"formats={formats}/{len(expected_names)}, cases={cases}/{expected_cases}"
        )
    return formats, cases, mismatches


def print_result(oracle: str, formats: int, cases: int, mismatches: int) -> None:
    status = "pass" if mismatches == 0 else "fail"
    print(
        f"{oracle},{status},{formats},{cases},{mismatches}",
    )
    if mismatches != 0:
        raise SystemExit(1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emitter", required=True, type=Path)
    subparsers = parser.add_subparsers(dest="oracle", required=True)
    subparsers.add_parser("onnx")
    p3109 = subparsers.add_parser("p3109")
    p3109.add_argument("--source", required=True, type=Path)
    p3109.add_argument("--minimum-width", type=int, default=3)
    p3109.add_argument("--maximum-width", type=int, default=16)
    args = parser.parse_args()

    if args.oracle == "onnx":
        print_result("ONNX low-bit decode", *compare_onnx(args.emitter))
    else:
        print_result(
            "P3109 4.0.3 value tables",
            *compare_p3109(
                args.emitter,
                args.source,
                args.minimum_width,
                args.maximum_width,
            ),
        )


if __name__ == "__main__":
    main()
