#!/usr/bin/env python3
"""Differential-test FloatLib against SMT-LIB's QF_FP theory through Z3.

The adapter generates a bounded deterministic corpus for IEEE binary16,
binary32, and binary64. Z3 evaluates ground QF_FP expressions; a standalone
Lean runner executes the same cases through configured ``ExecFloat.Binary``.
All non-NaN results are compared by their complete interchange word.

SMT-LIB floating-point values have one abstract NaN, so QF_FP cannot expose a
payload or signaling bit. Those cases are still checked for NaN class and are
reported separately from exact-bit comparisons.
"""

from __future__ import annotations

import argparse
import json
import random
import re
import shutil
import subprocess
import sys
from collections import Counter
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import TypeAlias


@dataclass(frozen=True)
class BinaryFormat:
    name: str
    exponent_bits: int
    significand_bits: int

    @property
    def fraction_bits(self) -> int:
        return self.significand_bits - 1

    @property
    def width(self) -> int:
        return 1 + self.exponent_bits + self.fraction_bits

    @property
    def hex_digits(self) -> int:
        return (self.width + 3) // 4

    @property
    def sign_mask(self) -> int:
        return 1 << (self.width - 1)

    @property
    def exponent_mask(self) -> int:
        return (1 << self.exponent_bits) - 1

    @property
    def fraction_mask(self) -> int:
        return (1 << self.fraction_bits) - 1

    @property
    def bias(self) -> int:
        return (1 << (self.exponent_bits - 1)) - 1

    def hex(self, bits: int) -> str:
        return f"{bits & ((1 << self.width) - 1):0{self.hex_digits}x}"

    def is_nan(self, bits: int) -> bool:
        exponent = (bits >> self.fraction_bits) & self.exponent_mask
        fraction = bits & self.fraction_mask
        return exponent == self.exponent_mask and fraction != 0

    def is_finite(self, bits: int) -> bool:
        exponent = (bits >> self.fraction_bits) & self.exponent_mask
        return exponent != self.exponent_mask


F16 = BinaryFormat("f16", 5, 11)
F32 = BinaryFormat("f32", 8, 24)
F64 = BinaryFormat("f64", 11, 53)
FORMATS = (F16, F32, F64)
FORMAT_BY_NAME = {fmt.name: fmt for fmt in FORMATS}


@dataclass(frozen=True)
class Rounding:
    protocol: str
    smt: str


ROUNDINGS = (
    Rounding("rne", "RNE"),
    Rounding("rtz", "RTZ"),
    Rounding("rtp", "RTP"),
    Rounding("rtn", "RTN"),
)


@dataclass(frozen=True)
class Case:
    identifier: str
    operation: str
    source: BinaryFormat
    destination: BinaryFormat
    rounding: Rounding
    operands: tuple[int, ...]

    @property
    def solver_name(self) -> str:
        return f"smt_fp_{self.identifier}"

    def protocol_line(self) -> str:
        fields = [
            self.identifier,
            self.operation,
            self.source.name,
            self.destination.name,
            self.rounding.protocol,
            *(self.source.hex(value) for value in self.operands),
        ]
        return "\t".join(fields)


@dataclass(frozen=True)
class SolverValue:
    bits: int | None
    kind: str


@dataclass(frozen=True)
class Mismatch:
    identifier: str
    operation: str
    source: str
    destination: str
    rounding: str
    operands: tuple[str, ...]
    expected_kind: str
    expected_bits: str | None
    actual_bits: str | None
    reason: str


SExpr: TypeAlias = str | list["SExpr"]


class AdapterError(RuntimeError):
    """A solver, runner, protocol, or report error."""


def unique(values: Iterable[int]) -> tuple[int, ...]:
    return tuple(dict.fromkeys(values))


def edge_values(fmt: BinaryFormat) -> tuple[int, ...]:
    """Representative IEEE classes and boundaries, including both NaN classes."""

    sign = fmt.sign_mask
    exponent_all_ones = fmt.exponent_mask << fmt.fraction_bits
    one = fmt.bias << fmt.fraction_bits
    half = (fmt.bias - 1) << fmt.fraction_bits
    two = (fmt.bias + 1) << fmt.fraction_bits
    minimum_normal = 1 << fmt.fraction_bits
    largest_finite = ((fmt.exponent_mask - 1) << fmt.fraction_bits) | fmt.fraction_mask
    quiet_nan = exponent_all_ones | (1 << (fmt.fraction_bits - 1))
    signaling_nan = exponent_all_ones | 1
    return unique(
        (
            0,
            sign,
            1,
            sign | 1,
            fmt.fraction_mask,
            sign | fmt.fraction_mask,
            minimum_normal,
            sign | minimum_normal,
            half,
            sign | half,
            one - 1,
            one,
            one + 1,
            sign | one,
            two,
            sign | two,
            largest_finite,
            sign | largest_finite,
            exponent_all_ones,
            sign | exponent_all_ones,
            quiet_nan,
            sign | quiet_nan,
            signaling_nan,
            sign | signaling_nan,
        )
    )


def random_finite_values(
    fmt: BinaryFormat,
    rng: random.Random,
    count: int,
    excluded: Iterable[int] = (),
) -> tuple[int, ...]:
    seen = set(excluded)
    values: list[int] = []
    while len(values) < count:
        bits = rng.getrandbits(fmt.width)
        if fmt.is_finite(bits) and bits not in seen:
            seen.add(bits)
            values.append(bits)
    return tuple(values)


def binary_pairs(values: Sequence[int]) -> tuple[tuple[int, int], ...]:
    if not values:
        return ()
    pairs = [
        (values[index], values[(index * 7 + 3) % len(values)])
        for index in range(len(values))
    ]
    pairs.extend(
        (
            (values[0], values[0]),
            (values[0], values[1]),
            (values[1], values[0]),
            (values[11], values[11]),
            (values[11], values[13]),
            (values[16], values[16]),
            (values[16], values[17]),
            (values[18], values[19]),
            (values[18], values[0]),
            (values[0], values[0]),
            (values[20], values[11]),
            (values[22], values[11]),
        )
    )
    return tuple(dict.fromkeys(pairs))


def ternary_inputs(values: Sequence[int]) -> tuple[tuple[int, int, int], ...]:
    if not values:
        return ()
    triples = [
        (
            values[index],
            values[(index * 5 + 1) % len(values)],
            values[(index * 11 + 2) % len(values)],
        )
        for index in range(len(values))
    ]
    triples.extend(
        (
            (values[11], values[11], values[11]),
            (values[11], values[11], values[13]),
            (values[16], values[14], values[17]),
            (values[18], values[0], values[11]),
            (values[18], values[11], values[19]),
            (values[20], values[11], values[14]),
            (values[22], values[11], values[14]),
        )
    )
    return tuple(dict.fromkeys(triples))


def generate_cases(seed: int, random_per_format: int) -> list[Case]:
    if random_per_format < 0:
        raise AdapterError("random-per-format must be nonnegative")

    rng = random.Random(seed)
    pending: list[
        tuple[str, BinaryFormat, BinaryFormat, Rounding, tuple[int, ...]]
    ] = []
    values_by_format: dict[BinaryFormat, tuple[int, ...]] = {}

    for fmt in FORMATS:
        edges = edge_values(fmt)
        values = (
            *edges,
            *random_finite_values(
                fmt,
                rng,
                random_per_format,
                excluded=edges,
            ),
        )
        values_by_format[fmt] = values
        pairs = binary_pairs(values)
        triples = ternary_inputs(values)
        for rounding in ROUNDINGS:
            for operation in ("add", "sub", "mul", "div"):
                for operands in pairs:
                    pending.append((operation, fmt, fmt, rounding, operands))
            for value in values:
                pending.append(("sqrt", fmt, fmt, rounding, (value,)))
            for operands in triples:
                pending.append(("fma", fmt, fmt, rounding, operands))

    for source in FORMATS:
        for destination in FORMATS:
            if source == destination:
                continue
            for rounding in ROUNDINGS:
                for value in values_by_format[source]:
                    pending.append(("cast", source, destination, rounding, (value,)))

    width = max(6, len(str(max(0, len(pending) - 1))))
    return [
        Case(
            identifier=f"{index:0{width}d}",
            operation=operation,
            source=source,
            destination=destination,
            rounding=rounding,
            operands=operands,
        )
        for index, (operation, source, destination, rounding, operands) in enumerate(
            pending
        )
    ]


def fp_literal(fmt: BinaryFormat, bits: int) -> str:
    return f"((_ to_fp {fmt.exponent_bits} {fmt.significand_bits}) #x{fmt.hex(bits)})"


def case_expression(case: Case) -> str:
    operands = [fp_literal(case.source, value) for value in case.operands]
    rounding = case.rounding.smt
    if case.operation == "cast":
        return (
            f"((_ to_fp {case.destination.exponent_bits} "
            f"{case.destination.significand_bits}) {rounding} {operands[0]})"
        )
    if case.operation == "sqrt":
        return f"(fp.sqrt {rounding} {operands[0]})"
    if case.operation == "fma":
        return f"(fp.fma {rounding} {operands[0]} {operands[1]} {operands[2]})"
    if case.operation in {"add", "sub", "mul", "div"}:
        return f"(fp.{case.operation} {rounding} {operands[0]} {operands[1]})"
    raise AdapterError(f"unsupported operation: {case.operation}")


def chunks(values: Sequence[str], size: int) -> Iterator[Sequence[str]]:
    for index in range(0, len(values), size):
        yield values[index : index + size]


def build_smtlib(cases: Sequence[Case], batch_size: int = 128) -> str:
    if batch_size <= 0:
        raise AdapterError("SMT batch size must be positive")
    lines = [
        "(set-logic QF_FP)",
        "(set-option :produce-models true)",
    ]
    for case in cases:
        destination = case.destination
        lines.append(
            f"(define-fun {case.solver_name} () "
            f"(_ FloatingPoint {destination.exponent_bits} "
            f"{destination.significand_bits}) {case_expression(case)})"
        )
    lines.append("(check-sat)")
    names = [case.solver_name for case in cases]
    for batch in chunks(names, batch_size):
        lines.append(f"(get-value ({' '.join(batch)}))")
    lines.append("(exit)")
    return "\n".join(lines) + "\n"


TOKEN = re.compile(r'\s*(?:(\()|(\))|("(?:[^"\\]|\\.)*")|([^\s()]+))')


def tokenize_sexpressions(text: str) -> list[str]:
    tokens: list[str] = []
    position = 0
    while position < len(text):
        match = TOKEN.match(text, position)
        if match is None:
            if text[position:].strip():
                raise AdapterError(f"cannot parse solver output near byte {position}")
            break
        token = next(group for group in match.groups() if group is not None)
        tokens.append(token)
        position = match.end()
    return tokens


def parse_sexpressions(text: str) -> list[SExpr]:
    tokens = tokenize_sexpressions(text)
    position = 0

    def parse_one() -> SExpr:
        nonlocal position
        if position >= len(tokens):
            raise AdapterError("unexpected end of solver output")
        token = tokens[position]
        position += 1
        if token == "(":
            result: list[SExpr] = []
            while True:
                if position >= len(tokens):
                    raise AdapterError("unterminated solver expression")
                if tokens[position] == ")":
                    position += 1
                    return result
                result.append(parse_one())
        if token == ")":
            raise AdapterError("unexpected ')' in solver output")
        return token

    expressions: list[SExpr] = []
    while position < len(tokens):
        expressions.append(parse_one())
    return expressions


def atom(value: SExpr, context: str) -> str:
    if not isinstance(value, str):
        raise AdapterError(f"expected atom for {context}: {value!r}")
    return value


def decode_bitvector(field: str, width: int, fmt: BinaryFormat) -> int:
    binary = field.startswith("#b") and len(field) == width + 2
    hexadecimal = (
        width % 4 == 0 and field.startswith("#x") and len(field) == width // 4 + 2
    )
    if binary or hexadecimal:
        return int("0" + field[1:], 0)
    raise AdapterError(f"wrong QF_FP field width for {fmt.name}: {field!r}")


def decode_solver_value(value: SExpr, fmt: BinaryFormat) -> SolverValue:
    if not isinstance(value, list) or not value:
        raise AdapterError(f"unexpected floating-point value: {value!r}")
    head = atom(value[0], "floating-point constructor")
    if head == "fp":
        if len(value) != 4:
            raise AdapterError(f"malformed fp constructor: {value!r}")
        sign = atom(value[1], "sign")
        exponent = atom(value[2], "exponent")
        fraction = atom(value[3], "fraction")
        expected_lengths = (1, fmt.exponent_bits, fmt.fraction_bits)
        fields = (sign, exponent, fraction)
        decoded = [
            decode_bitvector(field, expected, fmt)
            for field, expected in zip(fields, expected_lengths, strict=True)
        ]
        bits = (
            (decoded[0] << (fmt.exponent_bits + fmt.fraction_bits))
            | (decoded[1] << fmt.fraction_bits)
            | decoded[2]
        )
        if decoded[1] == fmt.exponent_mask:
            if decoded[2] == 0:
                return SolverValue(bits, "infinity")
            return SolverValue(None, "nan")
        if decoded[1] == 0 and decoded[2] == 0:
            return SolverValue(bits, "zero")
        return SolverValue(bits, "finite")
    if head != "_" or len(value) != 4:
        raise AdapterError(f"unsupported floating-point value: {value!r}")

    kind = atom(value[1], "special floating-point value")
    exponent_bits = int(atom(value[2], "special exponent width"))
    significand_bits = int(atom(value[3], "special significand width"))
    if (exponent_bits, significand_bits) != (
        fmt.exponent_bits,
        fmt.significand_bits,
    ):
        raise AdapterError(
            f"solver returned {exponent_bits}/{significand_bits} for {fmt.name}"
        )
    exponent = fmt.exponent_mask << fmt.fraction_bits
    if kind == "+zero":
        return SolverValue(0, "zero")
    if kind == "-zero":
        return SolverValue(fmt.sign_mask, "zero")
    if kind == "+oo":
        return SolverValue(exponent, "infinity")
    if kind == "-oo":
        return SolverValue(fmt.sign_mask | exponent, "infinity")
    if kind == "NaN":
        return SolverValue(None, "nan")
    raise AdapterError(f"unknown QF_FP special value: {kind}")


def parse_solver_output(
    output: str,
    cases: Sequence[Case],
) -> dict[str, SolverValue]:
    expressions = parse_sexpressions(output)
    if not expressions or expressions[0] != "sat":
        raise AdapterError(f"Z3 did not return sat: {expressions[:1]!r}")

    case_by_solver_name = {case.solver_name: case for case in cases}
    values: dict[str, SolverValue] = {}
    for expression in expressions[1:]:
        if not isinstance(expression, list):
            raise AdapterError(f"unexpected top-level solver output: {expression!r}")
        for binding in expression:
            if not isinstance(binding, list) or len(binding) != 2:
                raise AdapterError(f"malformed get-value binding: {binding!r}")
            name = atom(binding[0], "solver result name")
            case = case_by_solver_name.get(name)
            if case is None:
                raise AdapterError(f"solver returned unknown case: {name}")
            if case.identifier in values:
                raise AdapterError(f"solver returned duplicate case: {name}")
            values[case.identifier] = decode_solver_value(binding[1], case.destination)

    missing = sorted({case.identifier for case in cases} - values.keys())
    if missing:
        raise AdapterError(f"solver omitted {len(missing)} case(s): {missing[:3]}")
    return values


def run_z3(
    solver: str,
    script: str,
    timeout: float,
) -> tuple[dict[str, str], str, str]:
    executable = shutil.which(solver)
    if executable is None:
        raise AdapterError(f"SMT solver not found: {solver}")
    try:
        version = subprocess.run(
            [executable, "--version"],
            check=True,
            capture_output=True,
            text=True,
            timeout=timeout,
        ).stdout.strip()
        completed = subprocess.run(
            [executable, "-in", "-smt2"],
            input=script,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise AdapterError(f"Z3 timed out after {timeout:g} seconds") from error
    if completed.returncode != 0:
        raise AdapterError(
            f"Z3 exited with {completed.returncode}: {completed.stderr.strip()}"
        )
    metadata = {
        "name": "Z3",
        "version": version,
        "path": executable,
        "logic": "QF_FP",
    }
    return metadata, completed.stdout, completed.stderr


def parse_lean_output(
    output: str,
    cases: Sequence[Case],
) -> tuple[dict[str, int], int]:
    expected = {case.identifier: case for case in cases}
    seen: set[str] = set()
    values: dict[str, int] = {}
    protocol_errors = 0
    for line in output.splitlines():
        fields = line.split("\t")
        if len(fields) < 2:
            protocol_errors += 1
            continue
        identifier, status = fields[:2]
        case = expected.get(identifier)
        if case is None or identifier in seen:
            protocol_errors += 1
            continue
        seen.add(identifier)
        if status != "ok" or len(fields) != 3:
            protocol_errors += 1
            continue
        encoded = fields[2]
        if (
            len(encoded) != case.destination.hex_digits
            or re.fullmatch(r"[0-9a-fA-F]+", encoded) is None
        ):
            protocol_errors += 1
            continue
        value = int(encoded, 16)
        if value >= 1 << case.destination.width:
            protocol_errors += 1
            continue
        values[identifier] = value
    protocol_errors += len(expected.keys() - seen)
    return values, protocol_errors


def run_floatlib(
    runner: Path,
    cases: Sequence[Case],
    timeout: float,
) -> tuple[dict[str, int], int, str, str, int]:
    if not runner.is_file():
        raise AdapterError(f"FloatLib runner not found: {runner}")
    protocol = "\n".join(case.protocol_line() for case in cases) + "\n"
    try:
        completed = subprocess.run(
            [str(runner), "--lean-runner"],
            input=protocol,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise AdapterError(
            f"FloatLib runner timed out after {timeout:g} seconds"
        ) from error
    values, protocol_errors = parse_lean_output(completed.stdout, cases)
    if completed.returncode != 0:
        protocol_errors += 1
    return (
        values,
        protocol_errors,
        completed.stdout,
        completed.stderr,
        completed.returncode,
    )


def compare_results(
    cases: Sequence[Case],
    expected: dict[str, SolverValue],
    actual: dict[str, int],
) -> tuple[Counter[str], list[Mismatch]]:
    counts: Counter[str] = Counter(
        {
            "generated": 0,
            "exact_bit_cases": 0,
            "nan_class_cases": 0,
            "missing_floatlib": 0,
            "bit_mismatches": 0,
            "nan_class_mismatches": 0,
            "mismatches": 0,
        }
    )
    mismatches: list[Mismatch] = []
    for case in cases:
        counts["generated"] += 1
        solver_value = expected[case.identifier]
        actual_bits = actual.get(case.identifier)
        operand_text = tuple(case.source.hex(value) for value in case.operands)
        common = {
            "identifier": case.identifier,
            "operation": case.operation,
            "source": case.source.name,
            "destination": case.destination.name,
            "rounding": case.rounding.protocol,
            "operands": operand_text,
        }
        if actual_bits is None:
            counts["missing_floatlib"] += 1
            mismatches.append(
                Mismatch(
                    **common,
                    expected_kind=solver_value.kind,
                    expected_bits=(
                        None
                        if solver_value.bits is None
                        else case.destination.hex(solver_value.bits)
                    ),
                    actual_bits=None,
                    reason="missing_floatlib_result",
                )
            )
            continue

        if solver_value.kind == "nan":
            counts["nan_class_cases"] += 1
            if not case.destination.is_nan(actual_bits):
                counts["nan_class_mismatches"] += 1
                mismatches.append(
                    Mismatch(
                        **common,
                        expected_kind="nan",
                        expected_bits=None,
                        actual_bits=case.destination.hex(actual_bits),
                        reason="nan_class_mismatch",
                    )
                )
            continue

        counts["exact_bit_cases"] += 1
        if actual_bits != solver_value.bits:
            counts["bit_mismatches"] += 1
            mismatches.append(
                Mismatch(
                    **common,
                    expected_kind=solver_value.kind,
                    expected_bits=case.destination.hex(solver_value.bits),
                    actual_bits=case.destination.hex(actual_bits),
                    reason="bit_mismatch",
                )
            )

    counts["mismatches"] = len(mismatches)
    return counts, mismatches


def result_rows(
    cases: Sequence[Case],
    solver_values: dict[str, SolverValue],
    floatlib_values: dict[str, int],
) -> str:
    lines = [
        (
            "id\toperation\tsource\tdestination\trounding\toperands"
            "\tsolver_kind\tsolver_bits\tfloatlib_bits\tmatch"
        )
    ]
    for case in cases:
        expected = solver_values[case.identifier]
        actual = floatlib_values.get(case.identifier)
        if expected.kind == "nan":
            matches = actual is not None and case.destination.is_nan(actual)
        else:
            matches = actual == expected.bits
        lines.append(
            "\t".join(
                (
                    case.identifier,
                    case.operation,
                    case.source.name,
                    case.destination.name,
                    case.rounding.protocol,
                    ",".join(case.source.hex(value) for value in case.operands),
                    expected.kind,
                    (
                        ""
                        if expected.bits is None
                        else case.destination.hex(expected.bits)
                    ),
                    "" if actual is None else case.destination.hex(actual),
                    "true" if matches else "false",
                )
            )
        )
    return "\n".join(lines) + "\n"


def prepare_results(path: Path) -> None:
    if path.exists():
        if not path.is_dir() or any(path.iterdir()):
            raise AdapterError(f"results path is not empty: {path}")
    else:
        path.mkdir(parents=True)


def write_results(
    results: Path,
    script: str,
    solver_stdout: str,
    solver_stderr: str,
    lean_stdout: str,
    lean_stderr: str,
    rows: str,
    mismatches: Sequence[Mismatch],
    summary: dict[str, object],
) -> None:
    prepare_results(results)
    (results / "queries.smt2").write_text(script, encoding="utf-8")
    (results / "z3.stdout").write_text(solver_stdout, encoding="utf-8")
    (results / "z3.stderr").write_text(solver_stderr, encoding="utf-8")
    (results / "floatlib.stdout").write_text(lean_stdout, encoding="utf-8")
    (results / "floatlib.stderr").write_text(lean_stderr, encoding="utf-8")
    (results / "results.tsv").write_text(rows, encoding="utf-8")
    with (results / "mismatches.jsonl").open("w", encoding="utf-8") as stream:
        for mismatch in mismatches:
            stream.write(json.dumps(asdict(mismatch), sort_keys=True) + "\n")
    (results / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def default_runner() -> Path:
    return Path(__file__).resolve().with_suffix(".sh")


def parse_seed(text: str) -> int:
    try:
        value = int(text, 0)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"invalid integer seed: {text}") from error
    if value < 0:
        raise argparse.ArgumentTypeError("seed must be nonnegative")
    return value


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Generate bounded QF_FP cases, evaluate them with Z3 and FloatLib, "
            "and compare exact interchange words."
        )
    )
    parser.add_argument("--solver", default="z3", help="Z3 executable (default: z3)")
    parser.add_argument(
        "--lean-runner",
        type=Path,
        default=default_runner(),
        help="shell entry point that accepts --lean-runner",
    )
    parser.add_argument(
        "--seed",
        type=parse_seed,
        default=0x5EED5EED,
        help="deterministic integer seed (default: 0x5eed5eed)",
    )
    parser.add_argument(
        "--random-per-format",
        type=int,
        default=8,
        help="additional finite raw words per format (default: 8)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=300.0,
        help="per-process timeout in seconds (default: 300)",
    )
    parser.add_argument(
        "--results",
        type=Path,
        help="new or empty directory for queries, raw output, TSV, and JSON",
    )
    parser.add_argument(
        "--max-reports",
        type=int,
        default=20,
        help="maximum mismatch records embedded in stdout JSON (default: 20)",
    )
    args = parser.parse_args(argv)

    if args.random_per_format < 0:
        parser.error("--random-per-format must be nonnegative")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.max_reports < 0:
        parser.error("--max-reports must be nonnegative")

    try:
        cases = generate_cases(args.seed, args.random_per_format)
        script = build_smtlib(cases)
        solver_metadata, solver_stdout, solver_stderr = run_z3(
            args.solver, script, args.timeout
        )
        solver_values = parse_solver_output(solver_stdout, cases)
        (
            floatlib_values,
            protocol_errors,
            lean_stdout,
            lean_stderr,
            lean_returncode,
        ) = run_floatlib(args.lean_runner, cases, args.timeout)
        counts, mismatches = compare_results(cases, solver_values, floatlib_values)
        counts["protocol_errors"] = protocol_errors
        counts["tool_failures"] = int(lean_returncode != 0)
        failed = bool(mismatches or protocol_errors or lean_returncode != 0)
        summary: dict[str, object] = {
            "adapter": "smt_fp",
            "status": "fail" if failed else "pass",
            "seed": args.seed,
            "random_per_format": args.random_per_format,
            "formats": [fmt.name for fmt in FORMATS],
            "operations": ["add", "sub", "mul", "div", "sqrt", "fma", "cast"],
            "rounding_modes": [rounding.protocol for rounding in ROUNDINGS],
            "solver": solver_metadata,
            "counts": dict(sorted(counts.items())),
            "nan_policy": (
                "QF_FP has one abstract NaN; compare NaN class, not payload or "
                "signaling bit."
            ),
            "mismatch_samples": [
                asdict(mismatch) for mismatch in mismatches[: args.max_reports]
            ],
        }
        if args.results is not None:
            summary["results"] = str(args.results.resolve())
            write_results(
                args.results,
                script,
                solver_stdout,
                solver_stderr,
                lean_stdout,
                lean_stderr,
                result_rows(cases, solver_values, floatlib_values),
                mismatches,
                summary,
            )
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 1 if failed else 0
    except AdapterError as error:
        print(
            json.dumps(
                {
                    "adapter": "smt_fp",
                    "status": "error",
                    "error": str(error),
                },
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
