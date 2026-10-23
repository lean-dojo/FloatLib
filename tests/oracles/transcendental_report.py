#!/usr/bin/env python3
"""Gate FloatLib's transcendental results against MPFR and summarize the comparison.

The input is the MPFR oracle's output: one `case` line per evaluation, carrying the operation,
rounding mode, complete format descriptor, exact argument encodings, FloatLib's encoding and
MPFR's correctly rounded encoding with the sign of its ternary value. Each emitter shard brackets
its cases with manifest comments; the shards of one run must share one invocation, cover every
shard index once, and together account for the emitter's request count.

The gate compares encodings. A NaN reference matches any FloatLib NaN, because MPFR has a single
NaN; every other reference must match bit for bit, so the two zeros differ. FloatLib's current
kernels are approximations, so a checked-in list names each case known to differ, keyed by its
case id, with the kind of difference and the encoding and ternary FloatLib returns. The gate
fails on

* a mismatch that is not listed;
* a listed mismatch whose kind, FloatLib encoding or FloatLib ternary changed, for example a
  wrong value that now gives NaN or moves further away;
* a value mismatch inside a domain FloatLib declares correctly rounded, listed or not;
* a listed case that ran and now matches: the fix that repaired it deletes its row;
* a run whose coverage differs from the checked-in census.

The census records the coverage of the standard invocations: the default run, the release run
and the qualification run. An entry is keyed by the options transcendental_compare.sh varies
(random count, tier and exhaustive16) and holds the complete manifest, the sha256 of the
hard-case file, the request count, the count per format and operation, and a sha256 over the
sorted case ids. A run with the same options must reproduce all of them, so a truncated run, an
emitter that drops requests, or another hard-case file fails even when the run's own trailers
agree. The run recorded as `qualification` must also exercise every listed case. Other
invocations report their coverage as unchecked. Every manifest must name the emitter, the
random count, the tier, the hard-case file and exhaustive16 exactly once. The driver passes the
options it gave the emitter with `--expect-manifest`, so an emitter that misreports them fails,
and `--require-census NAME` fails a run that does not reproduce entry NAME.

Counts and maximum ULP distances per function and format are reported, never used to pass.
Optional shared libraries add observational CORE-MATH, OpenLibm, and RLIBM columns for binary32
and binary64 in nearest-even mode.
"""

from __future__ import annotations

import argparse
import csv
import ctypes
import ctypes.util
import hashlib
import json
import math
import re
import struct
import sys
from collections import defaultdict
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Collection, Iterable

ARITIES = {
    "exp": 1,
    "log": 1,
    "sin": 1,
    "cos": 1,
    "sinh": 1,
    "cosh": 1,
    "tanh": 1,
    "pow": 2,
    "pi": 0,
}
UNARY_OPERATIONS = ("exp", "log", "sin", "cos", "sinh", "cosh", "tanh")
MODES = ("RNDN", "RNDZ", "RNDU", "RNDD", "RNDA")
KINDS = ("value", "nan", "ternary")
# The kinds a correctly rounded declaration covers: a different encoding.
VALUE_KINDS = ("value", "nan")


@dataclass(frozen=True)
class Format:
    """A binary format descriptor: field widths, exponent bias and exceptional encoding."""

    exponent_bits: int
    fraction_bits: int
    bias: int
    encoding: str = "ieee"

    @property
    def width(self) -> int:
        return 1 + self.exponent_bits + self.fraction_bits

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

    @property
    def hex_digits(self) -> int:
        return (self.width + 3) // 4

    @property
    def name(self) -> str:
        """The catalog name, or `ieeeE_F` (with `_biasB` for a custom bias)."""
        catalog = CATALOG_NAMES.get(self)
        if catalog is not None:
            return catalog
        name = f"ieee{self.exponent_bits}_{self.fraction_bits}"
        if self.bias != ieee_bias(self.exponent_bits):
            name += f"_bias{self.bias}"
        if self.encoding != "ieee":
            name += f"_{self.encoding}"
        return name

    def hex(self, bits: int) -> str:
        return f"0x{bits:0{self.hex_digits}x}"


def ieee_bias(exponent_bits: int) -> int:
    return (1 << (exponent_bits - 1)) - 1


def ieee(exponent_bits: int, fraction_bits: int) -> Format:
    return Format(exponent_bits, fraction_bits, ieee_bias(exponent_bits))


CATALOG = {
    "binary16": ieee(5, 10),
    "bfloat16": ieee(8, 7),
    "binary32": ieee(8, 23),
    "binary64": ieee(11, 52),
    "binary128": ieee(15, 112),
    "binary256": ieee(19, 236),
}
CATALOG_NAMES = {fmt: name for name, fmt in CATALOG.items()}


def format_named(name: str) -> Format:
    """The descriptor a case-id format name denotes; the inverse of `Format.name`."""
    if name in CATALOG:
        return CATALOG[name]
    parts = name.split("_")
    try:
        if not parts[0].startswith("ieee") or len(parts) < 2:
            raise ValueError
        exponent_bits, fraction_bits = int(parts[0][4:]), int(parts[1])
        bias = ieee_bias(exponent_bits)
        encoding = "ieee"
        for part in parts[2:]:
            if part.startswith("bias"):
                bias = int(part[4:])
            else:
                encoding = part
    except ValueError:
        raise ValueError(f"unknown format name {name!r}") from None
    fmt = Format(exponent_bits, fraction_bits, bias, encoding)
    if fmt.name != name:
        raise ValueError(f"unknown format name {name!r}")
    return fmt


def is_nan(bits: int, fmt: Format) -> bool:
    return (bits & fmt.exponent_mask) == fmt.exponent_mask and (bits & fmt.fraction_mask) != 0


def is_infinite(bits: int, fmt: Format) -> bool:
    return (bits & fmt.exponent_mask) == fmt.exponent_mask and (bits & fmt.fraction_mask) == 0


def is_finite(bits: int, fmt: Format) -> bool:
    return (bits & fmt.exponent_mask) != fmt.exponent_mask


def is_zero(bits: int, fmt: Format) -> bool:
    return (bits & (fmt.sign_mask - 1)) == 0


def to_fraction(bits: int, fmt: Format) -> Fraction:
    """The exact value of a finite encoding."""
    if not is_finite(bits, fmt):
        raise ValueError("only finite encodings have a rational value")
    field = (bits & fmt.exponent_mask) >> fmt.fraction_bits
    fraction = bits & fmt.fraction_mask
    if field == 0:
        significand, exponent = fraction, 1 - fmt.bias - fmt.fraction_bits
    else:
        significand = fraction | (1 << fmt.fraction_bits)
        exponent = field - fmt.bias - fmt.fraction_bits
    value = Fraction(significand) * (Fraction(2) ** exponent)
    return -value if bits & fmt.sign_mask else value


def value_matches(candidate: int, reference: int, fmt: Format) -> bool:
    """Encodings agree, except that every NaN matches a NaN reference."""
    if is_nan(reference, fmt):
        return is_nan(candidate, fmt)
    return candidate == reference


def ordered_encoding(bits: int, fmt: Format) -> int:
    """Map finite encodings to an order where adjacent values differ by one."""
    bits &= fmt.width_mask
    magnitude = bits & (fmt.sign_mask - 1)
    if bits & fmt.sign_mask:
        return fmt.sign_mask - magnitude
    return fmt.sign_mask + magnitude


def ulp_distance(left: int, right: int, fmt: Format) -> int:
    """Distance in representable steps; both zeros have rank zero, so this is not a gate."""
    if not is_finite(left, fmt) or not is_finite(right, fmt):
        raise ValueError("ULP distance is defined here only for finite values")
    return abs(ordered_encoding(left, fmt) - ordered_encoding(right, fmt))


def case_id(operation: str, mode: str, fmt: Format, arguments: Iterable[int]) -> str:
    """Canonical identity of one evaluation: format, operation, mode and argument encodings."""
    return "/".join([fmt.name, operation, mode, *(fmt.hex(bits) for bits in arguments)])


@dataclass(frozen=True)
class Case:
    case_id: str
    operation: str
    mode: str
    fmt: Format
    arguments: tuple[int, ...]
    floatlib: int | None
    floatlib_ternary: int | None
    mpfr: int
    mpfr_ternary: int

    @property
    def format_name(self) -> str:
        return self.fmt.name


DIGITS = {10: frozenset("0123456789"), 16: frozenset("0123456789abcdefABCDEF")}


def parse_natural(text: str, what: str) -> int:
    """A nonnegative integer in decimal or `0x`-prefixed hexadecimal."""
    if text.startswith(("0x", "0X")):
        digits, base = text[2:], 16
    else:
        digits, base = text, 10
        if len(digits) > 1 and digits[0] == "0":
            raise ValueError(f"{what}: decimal number with a leading zero: {text!r}")
    if not digits or not set(digits) <= DIGITS[base]:
        raise ValueError(f"{what}: invalid number {text!r}")
    return int(digits, base)


def parse_ternary(text: str, what: str) -> int:
    if text not in ("-1", "0", "1"):
        raise ValueError(f"{what}: ternary must be -1, 0 or 1, got {text!r}")
    return int(text)


class Fields:
    def __init__(self, fields: list[str], where: str) -> None:
        self.fields = fields
        self.index = 0
        self.where = where

    def take(self, what: str) -> str:
        if self.index >= len(self.fields):
            raise ValueError(f"{self.where}: missing {what}")
        field = self.fields[self.index]
        self.index += 1
        return field

    def keyword(self, keyword: str) -> None:
        field = self.take(keyword)
        if field != keyword:
            raise ValueError(f"{self.where}: expected {keyword!r}, found {field!r}")

    def peek(self, keyword: str) -> bool:
        return self.index < len(self.fields) and self.fields[self.index] == keyword


def parse_case_id(identity: str, where: str) -> tuple[Format, str, str, tuple[int, ...]]:
    """The format, operation, mode and arguments that a canonical case id names."""
    parts = identity.split("/")
    if len(parts) < 3 or parts[1] not in ARITIES or parts[2] not in MODES:
        raise ValueError(f"{where}: malformed case id {identity!r}")
    fmt = format_named(parts[0])
    arguments = tuple(parse_encoding(text, fmt, where) for text in parts[3:])
    if len(arguments) != ARITIES[parts[1]] or identity != case_id(parts[1], parts[2], fmt,
                                                                  arguments):
        raise ValueError(f"{where}: malformed case id {identity!r}")
    return fmt, parts[1], parts[2], arguments


def parse_encoding(text: str, fmt: Format, where: str) -> int:
    """An encoding of `fmt`, written as `fmt.hex` writes it."""
    bits = parse_natural(text, where)
    if bits > fmt.width_mask or text != fmt.hex(bits):
        raise ValueError(f"{where}: {text!r} is not a {fmt.name} encoding in hexadecimal")
    return bits


def parse_case_line(line: str, where: str) -> Case:
    """Parse one oracle output line; the case id must equal its canonical identity."""
    fields = Fields(line.split(), where)
    fields.keyword("case")
    identity = fields.take("case id")
    fields.keyword("op")
    operation = fields.take("operation")
    if operation not in ARITIES:
        raise ValueError(f"{where}: unknown operation {operation!r}")
    fields.keyword("mode")
    mode = fields.take("mode")
    if mode not in MODES:
        raise ValueError(f"{where}: unknown rounding mode {mode!r}")
    fields.keyword("format")
    exponent_bits = parse_natural(fields.take("exponent width"), where)
    fraction_bits = parse_natural(fields.take("fraction width"), where)
    bias = parse_natural(fields.take("bias"), where)
    encoding = fields.take("encoding")
    if exponent_bits < 2 or fraction_bits < 1 or bias < 1:
        raise ValueError(f"{where}: invalid format descriptor")
    fmt = Format(exponent_bits, fraction_bits, bias, encoding)
    fields.keyword("args")
    count = parse_natural(fields.take("argument count"), where)
    if count != ARITIES[operation]:
        raise ValueError(f"{where}: {operation} takes {ARITIES[operation]} arguments, not {count}")
    arguments = tuple(parse_natural(fields.take("argument"), where) for _ in range(count))
    floatlib: int | None = None
    floatlib_ternary: int | None = None
    if fields.peek("floatlib"):
        fields.take("floatlib")
        floatlib = parse_natural(fields.take("FloatLib result"), where)
        if fields.peek("ternary"):
            fields.take("ternary")
            floatlib_ternary = parse_ternary(fields.take("FloatLib ternary"), where)
    fields.keyword("mpfr")
    mpfr = parse_natural(fields.take("MPFR result"), where)
    mpfr_ternary = parse_ternary(fields.take("MPFR ternary"), where)
    if fields.index != len(fields.fields):
        raise ValueError(f"{where}: unexpected trailing field {fields.fields[fields.index]!r}")
    values = arguments + (mpfr,) + (() if floatlib is None else (floatlib,))
    if any(value > fmt.width_mask for value in values):
        raise ValueError(f"{where}: encoding wider than {fmt.name}")
    expected = case_id(operation, mode, fmt, arguments)
    if identity != expected:
        raise ValueError(f"{where}: case id {identity!r} does not name its content {expected!r}")
    return Case(identity, operation, mode, fmt, arguments, floatlib, floatlib_ternary, mpfr,
                mpfr_ternary)


@dataclass
class ShardBlock:
    """The manifest comments and cases of one emitter shard."""

    manifest: list[str]
    shard: tuple[int, int] | None = None
    requests: int | None = None
    emitted: int | None = None
    cases: int = 0


def manifest_entries(lines: list[str]) -> dict[str, list[str]]:
    """Manifest lines as `key -> values`."""
    entries: dict[str, list[str]] = defaultdict(list)
    for line in lines:
        key, _, value = line.partition(" ")
        entries[key].append(value)
    return dict(entries)


# Manifest entries that every emitter shard names exactly once.
SINGLE_MANIFEST_ENTRIES = ("emitter", "random-count", "tier", "hard", "exhaustive16")
TIERS = ("default", "slow")


def check_manifest(where: str, lines: list[str]) -> None:
    """A complete invocation: each single entry once with a valid value, no line or seed twice."""
    entries = manifest_entries(lines)
    if len(set(lines)) != len(lines):
        raise ValueError(f"{where}: the manifest repeats a line")
    for key in SINGLE_MANIFEST_ENTRIES:
        if len(entries.get(key, [])) != 1:
            raise ValueError(f"{where}: the manifest must name {key} exactly once")
    count = entries["random-count"][0]
    if not count.isdigit() or str(int(count)) != count:
        raise ValueError(f"{where}: invalid random count {count!r}")
    if entries["tier"][0] not in TIERS:
        raise ValueError(f"{where}: unknown tier {entries['tier'][0]!r}")
    if entries["exhaustive16"][0] not in ("true", "false"):
        raise ValueError(f"{where}: exhaustive16 must be true or false")
    seeds = [value.partition(" ")[0] for value in entries.get("seed", [])]
    if len(set(seeds)) != len(seeds):
        raise ValueError(f"{where}: the manifest names a seed twice")


def check_shards(path: Path, blocks: list[ShardBlock], cases: int) -> None:
    if not blocks:
        raise ValueError(f"{path}: no emitter manifest")
    for index, block in enumerate(blocks):
        if block.shard is None or block.requests is None or block.emitted is None:
            raise ValueError(f"{path}: shard block {index} lacks its shard, request count or "
                             "emitted count")
        if block.emitted != block.cases:
            raise ValueError(f"{path}: a shard announced {block.emitted} cases but "
                             f"{block.cases} were evaluated")
        if block.manifest != blocks[0].manifest or block.requests != blocks[0].requests:
            raise ValueError(f"{path}: shards come from different invocations")
    shards = [block.shard for block in blocks if block.shard is not None]
    count = shards[0][1]
    indices = sorted(index for index, _ in shards)
    if any(total != count for _, total in shards) or indices != list(range(count)):
        raise ValueError(f"{path}: expected shards 0..{count - 1} once each, found {indices}")
    if blocks[0].requests != cases:
        raise ValueError(f"{path}: the emitter selected {blocks[0].requests} requests but "
                         f"{cases} were evaluated")
    check_manifest(str(path), blocks[0].manifest)


def parse_references(path: Path) -> tuple[list[Case], dict[str, list[str]], int]:
    """Parse the oracle output and validate its shards; returns cases, invocation, request count."""
    cases: list[Case] = []
    seen: set[str] = set()
    blocks: list[ShardBlock] = []
    current: ShardBlock | None = None
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            line = line.rstrip("\n")
            where = f"{path}:{line_number}"
            if not line.strip():
                continue
            if line.startswith("#"):
                words = line[1:].split()
                if len(words) >= 2 and words[0] == "manifest":
                    if current is None or current.emitted is not None:
                        current = ShardBlock([])
                        blocks.append(current)
                    if words[1] == "shard":
                        if current.shard is not None:
                            raise ValueError(f"{where}: repeated shard line")
                        index, _, count = words[2].partition("/")
                        current.shard = (parse_natural(index, where), parse_natural(count, where))
                    elif words[1] == "requests":
                        if current.requests is not None:
                            raise ValueError(f"{where}: repeated request count")
                        current.requests = parse_natural(words[2], where)
                    else:
                        current.manifest.append(" ".join(words[1:]))
                elif len(words) == 2 and words[0] == "emitted":
                    if current is None or current.emitted is not None:
                        raise ValueError(f"{where}: emitted count outside a shard block")
                    current.emitted = parse_natural(words[1], where)
                continue
            if current is None or current.emitted is not None:
                raise ValueError(f"{where}: case outside a shard block")
            case = parse_case_line(line, where)
            if case.case_id in seen:
                raise ValueError(f"{where}: duplicate case {case.case_id}")
            seen.add(case.case_id)
            cases.append(case)
            current.cases += 1
    if not cases:
        raise ValueError(f"{path}: no comparison cases")
    check_shards(path, blocks, len(cases))
    return cases, manifest_entries(blocks[0].manifest), len(cases)


@dataclass(frozen=True)
class KnownFailure:
    case_id: str
    kind: str
    floatlib: int
    floatlib_ternary: int | None
    owner: str
    note: str


def ternary_text(ternary: int | None) -> str:
    """A ternary as the known-failures list writes it: `-` when the emitter sent none."""
    return "-" if ternary is None else str(ternary)


def parse_known_failures(path: Path) -> dict[str, KnownFailure]:
    """Read `id<TAB>kind<TAB>floatlib<TAB>ternary<TAB>owner<TAB>note` rows; `#` lines are
    comments."""
    result: dict[str, KnownFailure] = {}
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            where = f"{path}:{line_number}"
            columns = line.split("\t")
            if len(columns) != 6 or not all(columns[:5]):
                raise ValueError(f"{where}: expected id, kind, FloatLib encoding, FloatLib "
                                 "ternary, owner and note")
            identity, kind, encoding, ternary, owner, note = columns
            if kind not in KINDS:
                raise ValueError(f"{where}: unknown kind {kind!r}")
            floatlib_ternary = None if ternary == "-" else parse_ternary(ternary, where)
            if identity in result:
                raise ValueError(f"{where}: duplicate known failure {identity}")
            fmt = parse_case_id(identity, where)[0]
            result[identity] = KnownFailure(identity, kind, parse_encoding(encoding, fmt, where),
                                            floatlib_ternary, owner, note)
    return result


def mismatch_kind(case: Case) -> str | None:
    """`None` when FloatLib agrees with MPFR, else the kind of disagreement."""
    if case.floatlib is None:
        raise ValueError(f"{case.case_id}: no FloatLib result to compare")
    if not value_matches(case.floatlib, case.mpfr, case.fmt):
        if is_nan(case.floatlib, case.fmt):
            return "nan"
        return "value"
    if case.floatlib_ternary is not None and case.floatlib_ternary != case.mpfr_ternary:
        return "ternary"
    return None


def ieee_nearest_declaration(case: Case) -> bool:
    """The mode and descriptor hypotheses shared by the binary real-rounding theorems."""
    fmt = case.fmt
    return (case.mode == "RNDN" and fmt.encoding == "ieee"
            and fmt.bias == ieee_bias(fmt.exponent_bits))


def integral_pow_declaration(case: Case) -> bool:
    """`Model.Power.toReal_pow_of_eq_intCast`: for an IEEE descriptor (IEEE encoding and bias),
    a finite nonzero base and a finite integral exponent, a finite FloatLib result has the real
    value of the nearest-even rounding. The theorem fixes the value, not the sign of a zero."""
    fmt = case.fmt
    if not ieee_nearest_declaration(case):
        return False
    base, exponent = case.arguments
    if not (is_finite(base, fmt) and not is_zero(base, fmt) and is_finite(exponent, fmt)):
        return False
    if case.floatlib is None or not is_finite(case.floatlib, fmt):
        return False
    if is_zero(case.floatlib, fmt) and is_zero(case.mpfr, fmt):
        return False
    return to_fraction(exponent, fmt).denominator == 1


# Domains FloatLib documents as correctly rounded. A value mismatch inside one fails the gate even
# when the known-failures list names it. Each converted function adds its declaration here.
CORRECTLY_ROUNDED: dict[str, tuple[str, Callable[[Case], bool]]] = {
    "pi": ("pi in an IEEE descriptor", ieee_nearest_declaration),
    "pow": ("pow with an integral exponent", integral_pow_declaration),
}


def correctly_rounded_domain(case: Case, kind: str) -> str | None:
    """The declared domain that a mismatch of `kind` violates. The declarations are theorems
    about values, so a ternary-only difference violates none; the list handles it like any
    other mismatch."""
    declaration = CORRECTLY_ROUNDED.get(case.operation)
    if declaration is None or kind not in VALUE_KINDS:
        return None
    description, applies = declaration
    return description if applies(case) else None


def row_matches(entry: KnownFailure, case: Case, kind: str) -> bool:
    """Whether a listed row records this mismatch: its kind, FloatLib encoding and ternary."""
    return ((entry.kind, entry.floatlib, entry.floatlib_ternary)
            == (kind, case.floatlib, case.floatlib_ternary))


@dataclass
class GateResult:
    new: list[tuple[Case, str]]
    changed: list[tuple[Case, KnownFailure, str]]
    declared: list[tuple[Case, str, str]]
    stale: list[tuple[Case, KnownFailure]]
    known: list[tuple[Case, KnownFailure]]
    unexercised: int

    @property
    def passed(self) -> bool:
        return not (self.new or self.changed or self.declared or self.stale)


def gate(cases: list[Case], known: dict[str, KnownFailure]) -> GateResult:
    result = GateResult([], [], [], [], [], 0)
    ran: set[str] = set()
    for case in cases:
        ran.add(case.case_id)
        kind = mismatch_kind(case)
        entry = known.get(case.case_id)
        if kind is not None:
            domain = correctly_rounded_domain(case, kind)
            if domain is not None:
                result.declared.append((case, kind, domain))
            elif entry is None:
                result.new.append((case, kind))
            elif not row_matches(entry, case, kind):
                result.changed.append((case, entry, kind))
            else:
                result.known.append((case, entry))
        elif entry is not None:
            result.stale.append((case, entry))
    result.unexercised = sum(1 for identity in known if identity not in ran)
    return result


def describe(case: Case) -> str:
    fmt = case.fmt
    floatlib = "-" if case.floatlib is None else fmt.hex(case.floatlib)
    if case.floatlib_ternary is not None:
        floatlib += f" ({case.floatlib_ternary:+d})"
    reference = f"MPFR {fmt.hex(case.mpfr)} ({case.mpfr_ternary:+d})"
    return f"{case.case_id}: FloatLib {floatlib}, {reference}"


def print_gate(result: GateResult, coverage: Coverage, limit: int = 20) -> None:
    sections = [
        ("mismatch not in the known-failures list", [
            f"{describe(case)} [{kind}]" for case, kind in result.new]),
        ("known failure changed", [
            f"{describe(case)} [listed {entry.kind} {case.fmt.hex(entry.floatlib)} with ternary "
            f"{ternary_text(entry.floatlib_ternary)}, now {kind} with ternary "
            f"{ternary_text(case.floatlib_ternary)}]"
            for case, entry, kind in result.changed]),
        ("mismatch in a domain declared correctly rounded", [
            f"{describe(case)} [{kind}; {domain}]" for case, kind, domain in result.declared]),
        ("known failure now matches; delete its row", [
            f"{describe(case)} [listed {entry.kind}, owner {entry.owner}]"
            for case, entry in result.stale]),
        (f"coverage difference from census entry {coverage.census!r}", coverage.differences),
    ]
    for title, lines in sections:
        if not lines:
            continue
        print(f"GATE FAILURE: {len(lines)} {title}", file=sys.stderr)
        for line in lines[:limit]:
            print(f"  {line}", file=sys.stderr)
        if len(lines) > limit:
            print(f"  ... {len(lines) - limit} more", file=sys.stderr)


def default_owner(case: Case, kind: str) -> tuple[str, str]:
    """Design item that repairs a failure, and a short note, for a regenerated list."""
    if case.operation == "pow":
        return "B5", "pow fell back to exp (y * log x)"
    if case.operation in ("sin", "cos"):
        if kind == "nan":
            return "B4", "NaN beyond the 2^21-bit reduction limit"
        return "B4", "trigonometric reduction"
    if case.operation == "pi":
        return "B3", "pi from the configured half-pi"
    return "B5", f"{case.operation} kernel accuracy"


def write_known_failures(path: Path, cases: list[Case], manifest: dict[str, list[str]],
                         previous: dict[str, KnownFailure]) -> int:
    """Write the observed mismatches as a known-failures list, keeping existing owners and notes."""
    rows: list[tuple[str, ...]] = []
    for case in cases:
        kind = mismatch_kind(case)
        if kind is None or correctly_rounded_domain(case, kind) is not None:
            continue
        assert case.floatlib is not None
        entry = previous.get(case.case_id)
        owner, note = (entry.owner, entry.note) if entry is not None else default_owner(case, kind)
        rows.append((case.case_id, kind, case.fmt.hex(case.floatlib),
                     ternary_text(case.floatlib_ternary), owner, note))
    exercised = {case.case_id for case in cases}
    for identity, entry in previous.items():
        if identity not in exercised:
            fmt = format_named(identity.split("/")[0])
            rows.append((identity, entry.kind, fmt.hex(entry.floatlib),
                         ternary_text(entry.floatlib_ternary), entry.owner, entry.note))
    rows.sort()
    with path.open("w", encoding="utf-8", newline="") as stream:
        stream.write(
            "# FloatLib transcendental results known to differ from MPFR, keyed by case id\n"
            "# (format/operation/mode/argument encodings). Columns: case id, kind (value: a\n"
            "# different encoding; nan: NaN where MPFR is not; ternary: a different ternary\n"
            "# sign), the encoding FloatLib returns, the ternary FloatLib reports (- when the\n"
            "# emitter sends none), the design item that repairs it, and a note. The gate\n"
            "# fails on any unlisted mismatch, on a listed case whose kind, encoding or\n"
            "# ternary changes, and on a listed case that now matches, so a fix deletes its\n"
            "# rows. Regenerate with transcendental_compare.sh --write-known-failures.\n"
        )
        for key in sorted(manifest):
            for value in sorted(set(manifest[key])):
                stream.write(f"# manifest {key} {value}\n")
        for row in rows:
            stream.write("\t".join(row) + "\n")
    return len(rows)


# The options transcendental_compare.sh varies; a census entry is keyed by their values. The
# hard-case file, the seeds and the emitter belong to the recorded manifest instead, so a run of
# the standard options with another corpus fails rather than going unchecked.
CENSUS_OPTIONS = ("random-count", "tier", "exhaustive16")
# The census entry whose run must exercise every row of the known-failures list.
QUALIFICATION = "qualification"
CENSUS_NAME = re.compile(r"[a-z][a-z0-9-]*")
SHA256_DIGEST = re.compile(r"[0-9a-f]{64}")
# Relative hard-case paths in a manifest are relative to the repository root, where
# transcendental_compare.sh runs the emitter.
REPOSITORY = Path(__file__).resolve().parents[2]
MISSING_CORPUS = "missing"


@dataclass(frozen=True)
class CensusEntry:
    """The requests of one invocation: its manifest lines without the shard index, the sha256 of
    its hard-case file (`none` when it reads none), the request count, the count per
    `format/operation`, and a sha256 over the sorted case ids, one per line."""

    manifest: tuple[str, ...]
    corpus_sha256: str
    requests: int
    requests_by_operation: dict[str, int]
    case_ids_sha256: str


# The JSON fields of an entry, in the order of `CensusEntry`.
CENSUS_FIELDS = ("manifest", "corpus_sha256", "requests", "requests_by_operation",
                 "case_ids_sha256")


def manifest_lines(manifest: dict[str, list[str]]) -> tuple[str, ...]:
    """A run's invocation as sorted `key value` lines."""
    return tuple(sorted(f"{key} {value}" for key, values in manifest.items() for value in values))


def census_key(lines: Iterable[str]) -> tuple[str, ...]:
    """The manifest lines that select the requests."""
    return tuple(sorted(line for line in lines if line.partition(" ")[0] in CENSUS_OPTIONS))


def corpus_sha256(manifest: dict[str, list[str]]) -> str:
    """sha256 of the hard-case file a run read, `none` when it read none."""
    paths = manifest.get("hard", ["none"])
    if paths == ["none"]:
        return "none"
    if len(paths) != 1:
        raise ValueError(f"the manifest names {len(paths)} hard-case files")
    path = Path(paths[0])
    if not path.is_absolute():
        path = REPOSITORY / path
    return sha256(path) if path.is_file() else MISSING_CORPUS


def census_counts(cases: list[Case]) -> tuple[int, dict[str, int], str]:
    """The request count, the count per `format/operation`, and the sha256 over the sorted case
    ids, one per line."""
    counts: dict[str, int] = defaultdict(int)
    for case in cases:
        counts[f"{case.format_name}/{case.operation}"] += 1
    identities = "".join(f"{identity}\n" for identity in sorted(case.case_id for case in cases))
    return (len(cases), dict(sorted(counts.items())),
            hashlib.sha256(identities.encode("utf-8")).hexdigest())


def census_entry(cases: list[Case], manifest: dict[str, list[str]]) -> CensusEntry:
    """What a run's census entry records."""
    requests, counts, digest = census_counts(cases)
    return CensusEntry(manifest_lines(manifest), corpus_sha256(manifest), requests, counts, digest)


def positive_integer(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def unique_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """A JSON object that names no key twice."""
    keys = [key for key, _ in pairs]
    if len(set(keys)) != len(keys):
        raise ValueError("a JSON object repeats a key")
    return dict(pairs)


def read_census(path: Path) -> dict[str, CensusEntry]:
    """Read a census file, `{"invocations": {NAME: ENTRY}}` with the fields of `CensusEntry`."""
    if not path.is_file():
        raise ValueError(f"census not found: {path}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_keys)
    except ValueError as error:
        raise ValueError(f"{path}: invalid JSON: {error}") from None
    if not isinstance(data, dict) or set(data) != {"invocations"} or not isinstance(
            data["invocations"], dict):
        raise ValueError(f"{path}: expected one object named `invocations`")
    result: dict[str, CensusEntry] = {}
    keys: dict[tuple[str, ...], str] = {}
    for name, raw in data["invocations"].items():
        where = f"{path}: census entry {name!r}"
        if not CENSUS_NAME.fullmatch(name):
            raise ValueError(f"{where}: invalid name")
        if not isinstance(raw, dict) or set(raw) != set(CENSUS_FIELDS):
            raise ValueError(f"{where}: expected the fields {', '.join(CENSUS_FIELDS)}")
        manifest, counts = raw["manifest"], raw["requests_by_operation"]
        corpus, identities = raw["corpus_sha256"], raw["case_ids_sha256"]
        if not (isinstance(manifest, list) and all(isinstance(line, str) for line in manifest)
                and manifest == sorted(set(manifest))):
            raise ValueError(f"{where}: the manifest must be sorted distinct lines")
        check_manifest(where, manifest)
        if not (isinstance(corpus, str) and (corpus == "none" or SHA256_DIGEST.fullmatch(corpus))
                and isinstance(identities, str) and SHA256_DIGEST.fullmatch(identities)):
            raise ValueError(f"{where}: digests must be lowercase hexadecimal sha256")
        if not (positive_integer(raw["requests"]) and isinstance(counts, dict)
                and all(group.count("/") == 1 and group.split("/")[1] in ARITIES
                        and positive_integer(count) for group, count in counts.items())
                and sum(counts.values()) == raw["requests"]):
            raise ValueError(f"{where}: the counts per format/operation must be positive and sum "
                             "to the request count")
        key = census_key(manifest)
        if key in keys:
            raise ValueError(f"{where}: records the same invocation as {keys[key]!r}")
        keys[key] = name
        result[name] = CensusEntry(tuple(manifest), corpus, raw["requests"], dict(counts),
                                   identities)
    return result


def write_census(path: Path, census: dict[str, CensusEntry], name: str,
                 entry: CensusEntry) -> None:
    """Record `entry` as census entry `name`, replacing any entry of that name."""
    if not CENSUS_NAME.fullmatch(name):
        raise ValueError(f"invalid census entry name {name!r}")
    if entry.corpus_sha256 == MISSING_CORPUS:
        raise ValueError("the run's hard-case file is missing")
    for other, recorded in census.items():
        if other != name and census_key(recorded.manifest) == census_key(entry.manifest):
            raise ValueError(f"census entry {other!r} already records this invocation")
    updated = {**census, name: entry}
    payload = {"invocations": {key: asdict(value) for key, value in updated.items()}}
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass
class Coverage:
    """A run's census check: the entry recording its invocation, if any, and each difference."""

    census: str | None
    differences: list[str]

    @property
    def passed(self) -> bool:
        return not self.differences

    @property
    def status(self) -> str:
        if self.census is None:
            return "unchecked"
        return "checked" if self.passed else "failed"


def check_coverage(cases: list[Case], manifest: dict[str, list[str]],
                   census: dict[str, CensusEntry], unexercised: int,
                   required: str | None = None) -> Coverage:
    """Compare a run with the census entry of its invocation, or with entry `required` when the
    driver names one; `unexercised` is the number of listed known failures the run did not
    exercise."""
    if required is not None:
        if required not in census:
            raise ValueError(f"the census has no entry {required!r}")
        name: str | None = required
    else:
        key = census_key(manifest_lines(manifest))
        name = next((name for name, entry in census.items()
                     if census_key(entry.manifest) == key), None)
    if name is None:
        return Coverage(None, [])
    expected, observed = census[name], census_entry(cases, manifest)
    differences: list[str] = []
    if observed.manifest != expected.manifest:
        missing = sorted(set(expected.manifest) - set(observed.manifest))
        unexpected = sorted(set(observed.manifest) - set(expected.manifest))
        differences.append(f"manifest lacks {missing} and adds {unexpected}")
    if observed.corpus_sha256 != expected.corpus_sha256:
        differences.append(f"hard-case file sha256 {observed.corpus_sha256}, census "
                           f"{expected.corpus_sha256}")
    if observed.requests != expected.requests:
        differences.append(f"{observed.requests} requests, census {expected.requests}")
    groups = sorted(set(observed.requests_by_operation) | set(expected.requests_by_operation))
    for group in groups:
        actual = observed.requests_by_operation.get(group, 0)
        recorded = expected.requests_by_operation.get(group, 0)
        if actual != recorded:
            differences.append(f"{group}: {actual} requests, census {recorded}")
    if observed.case_ids_sha256 != expected.case_ids_sha256:
        differences.append(f"sorted case ids hash to {observed.case_ids_sha256}, census "
                           f"{expected.case_ids_sha256}")
    if name == QUALIFICATION and unexercised:
        differences.append(f"{unexercised} listed known failures were not exercised")
    return Coverage(name, differences)


@dataclass(frozen=True)
class Summary:
    candidate: str
    format_name: str
    operation: str
    mode: str
    cases: int
    value_exact: int
    bit_exact: int
    finite_pairs: int
    nonfinite_mismatch: int
    zero_sign_mismatch: int
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


def percentile(sorted_values: list[int], probability: float) -> int | None:
    if not sorted_values:
        return None
    index = max(0, math.ceil(probability * len(sorted_values)) - 1)
    return sorted_values[index]


def make_summary(candidate: str, fmt: Format, operation: str, mode: str,
                 pairs: Iterable[tuple[int, int]]) -> Summary:
    materialized = list(pairs)
    distances = sorted(
        ulp_distance(output, reference, fmt)
        for output, reference in materialized
        if is_finite(output, fmt) and is_finite(reference, fmt)
    )

    def in_range(lower: int, upper: int | None = None) -> int:
        if upper is None:
            return sum(distance >= lower for distance in distances)
        return sum(lower <= distance <= upper for distance in distances)

    return Summary(
        candidate=candidate,
        format_name=fmt.name,
        operation=operation,
        mode=mode,
        cases=len(materialized),
        value_exact=sum(value_matches(o, r, fmt) for o, r in materialized),
        bit_exact=sum(o == r for o, r in materialized),
        finite_pairs=len(distances),
        nonfinite_mismatch=sum(
            not (is_finite(o, fmt) and is_finite(r, fmt)) and not value_matches(o, r, fmt)
            for o, r in materialized
        ),
        zero_sign_mismatch=sum(
            is_zero(o, fmt) and is_zero(r, fmt) and o != r and is_finite(o, fmt)
            and is_finite(r, fmt)
            for o, r in materialized
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


def bits_to_argument(bits: int, format_name: str) -> float:
    if format_name == "binary32":
        return struct.unpack("<f", struct.pack("<I", bits))[0]
    return struct.unpack("<d", struct.pack("<Q", bits))[0]


def result_to_bits(value: float, format_name: str) -> int:
    if format_name == "binary32":
        return struct.unpack("<I", struct.pack("<f", value))[0]
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def supported_by(groups: Collection[tuple[str, str]], case: Case) -> bool:
    """Whether a provider with these (format, operation) groups evaluates a case: the providers
    are binary32 and binary64 libm functions in nearest-even mode."""
    return case.mode == "RNDN" and (case.format_name, case.operation) in groups


class SharedLibraryProvider:
    """A host libm-style library evaluated through binary32/binary64 scalars."""

    def __init__(self, name: str, path: Path, symbols: dict[tuple[str, str], str]) -> None:
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

    def supports(self, case: Case) -> bool:
        return supported_by(self._functions, case)

    def evaluate(self, case: Case) -> int | None:
        if not self.supports(case):
            return None
        function = self._functions[(case.format_name, case.operation)]
        argument = bits_to_argument(case.arguments[0], case.format_name)
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
                raise ValueError(f"{path}: malformed provenance row {line_number}: {line!r}")
            key, value = fields
            if key in result:
                raise ValueError(f"{path}: duplicate provenance key {key!r}")
            result[key] = value
    return result


def core_math_symbols() -> dict[tuple[str, str], str]:
    result: dict[tuple[str, str], str] = {}
    for operation in UNARY_OPERATIONS:
        result[("binary32", operation)] = f"cr_{operation}f"
        result[("binary64", operation)] = f"cr_{operation}"
    return result


def openlibm_symbols() -> dict[tuple[str, str], str]:
    result: dict[tuple[str, str], str] = {}
    for operation in UNARY_OPERATIONS:
        result[("binary32", operation)] = f"{operation}f"
        result[("binary64", operation)] = operation
    return result


def rlibm_symbols() -> dict[tuple[str, str], str]:
    return {
        ("binary32", operation): f"floatlib_rlibm_{operation}"
        for operation in ("exp", "log", "sinh", "cosh")
    }


# The optional external providers in report order, each with its symbol per supported group.
PROVIDER_SYMBOLS: dict[str, Callable[[], dict[tuple[str, str], str]]] = {
    "CORE-MATH": core_math_symbols,
    "OpenLibm": openlibm_symbols,
    "RLIBM": rlibm_symbols,
}


def provider_coverage(name: str, groups: Collection[tuple[str, str]], cases: list[Case],
                      outputs: list[int | None]) -> dict[str, object]:
    """A provider's coverage record: its groups, the cases it supports and those it evaluated."""
    return {
        "name": name,
        "supported_groups": [
            {"format": format_name, "operation": operation}
            for format_name, operation in sorted(groups)
        ],
        "expected_evaluations": sum(1 for case in cases if supported_by(groups, case)),
        "actual_evaluations": sum(output is not None for output in outputs),
    }


def summarize(cases: list[Case], results: dict[str, list[int | None]]) -> list[Summary]:
    """One summary per candidate and (format, operation, mode) group, in report order."""
    groups: dict[tuple[str, str, str], list[int]] = defaultdict(list)
    formats: dict[str, Format] = {}
    for index, case in enumerate(cases):
        groups[(case.format_name, case.operation, case.mode)].append(index)
        formats[case.format_name] = case.fmt
    summaries: list[Summary] = []
    for candidate, outputs in results.items():
        for (format_name, operation, mode), indices in sorted(groups.items()):
            pairs = [(outputs[i], cases[i].mpfr) for i in indices if outputs[i] is not None]
            if pairs:
                summaries.append(make_summary(candidate, formats[format_name], operation, mode,
                                              pairs))
    return summaries


def percent(count: int, total: int) -> str:
    if total == 0:
        return "n/a"
    return f"{100.0 * count / total:.2f}%"


def optional_integer(value: int | None) -> str:
    return "n/a" if value is None else str(value)


def write_mismatches(path: Path, cases: list[Case], known: dict[str, KnownFailure]) -> None:
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(["case", "kind", "status", "floatlib_bits", "floatlib_ternary",
                         "mpfr_bits", "mpfr_ternary", "ulp"])
        for case in cases:
            kind = mismatch_kind(case)
            if kind is None:
                continue
            assert case.floatlib is not None
            entry = known.get(case.case_id)
            if correctly_rounded_domain(case, kind) is not None:
                status = "declared-correctly-rounded"
            elif entry is None:
                status = "new"
            elif not row_matches(entry, case, kind):
                status = "changed"
            else:
                status = "known"
            ulp = (ulp_distance(case.floatlib, case.mpfr, case.fmt)
                   if is_finite(case.floatlib, case.fmt) and is_finite(case.mpfr, case.fmt)
                   else "")
            writer.writerow([case.case_id, kind, status, case.fmt.hex(case.floatlib),
                             ternary_text(case.floatlib_ternary), case.fmt.hex(case.mpfr),
                             case.mpfr_ternary, ulp])


def write_details(path: Path, cases: list[Case], results: dict[str, list[int | None]]) -> None:
    """One row per case: its id, MPFR's encoding and ternary, each candidate's encoding (empty
    when it has none), and each candidate's ULP distance (empty unless both are finite)."""
    candidates = list(results)
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(["case", "mpfr_bits", "mpfr_ternary"]
                        + [f"{name}_bits" for name in candidates]
                        + [f"{name}_ulp" for name in candidates])
        for index, case in enumerate(cases):
            fmt = case.fmt
            outputs = [results[name][index] for name in candidates]
            distances = [
                ulp_distance(output, case.mpfr, fmt)
                if output is not None and is_finite(output, fmt) and is_finite(case.mpfr, fmt)
                else ""
                for output in outputs
            ]
            writer.writerow([case.case_id, fmt.hex(case.mpfr), case.mpfr_ternary]
                            + ["" if output is None else fmt.hex(output) for output in outputs]
                            + distances)


def coverage_text(coverage: Coverage) -> str:
    if coverage.census is None:
        return "coverage unchecked, no census entry records this invocation"
    if coverage.passed:
        return f"coverage matches census entry {coverage.census!r}"
    return (f"coverage differs from census entry {coverage.census!r}: "
            f"{len(coverage.differences)} differences")


def read_details(path: Path) -> tuple[list[Case], dict[str, list[int | None]]]:
    """Read `write_details` output back into cases and candidate results. FloatLib comes
    first and has a result for every case, as the report requires; the cases carry no FloatLib
    ternary, which the details do not record."""
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    header = rows[0] if rows else []
    width = (len(header) - 3) // 2
    candidates = [name.removesuffix("_bits") for name in header[3:3 + width]]
    if (header[:3] != ["case", "mpfr_bits", "mpfr_ternary"] or candidates[:1] != ["FloatLib"]
            or len(set(candidates)) != len(candidates)
            or header[3:] != [f"{name}_bits" for name in candidates]
            + [f"{name}_ulp" for name in candidates]):
        raise ValueError(f"{path}: unexpected details header")
    cases: list[Case] = []
    results: dict[str, list[int | None]] = {name: [] for name in candidates}
    seen: set[str] = set()
    for line_number, row in enumerate(rows[1:], start=2):
        where = f"{path}:{line_number}"
        if len(row) != len(header) or row[0] in seen:
            raise ValueError(f"{where}: malformed or duplicate details row")
        seen.add(row[0])
        fmt, operation, mode, arguments = parse_case_id(row[0], where)
        mpfr = parse_encoding(row[1], fmt, where)
        outputs = [None if text == "" else parse_encoding(text, fmt, where)
                   for text in row[3:3 + width]]
        if outputs[0] is None:
            raise ValueError(f"{where}: no FloatLib result")
        for output, text in zip(outputs, row[3 + width:], strict=True):
            distance = (ulp_distance(output, mpfr, fmt) if output is not None
                        and is_finite(output, fmt) and is_finite(mpfr, fmt) else "")
            if text != str(distance):
                raise ValueError(f"{where}: ULP column {text!r} is not the distance {distance}")
        cases.append(Case(row[0], operation, mode, fmt, arguments, outputs[0], None, mpfr,
                          parse_ternary(row[2], where)))
        for name, output in zip(candidates, outputs, strict=True):
            results[name].append(output)
    return cases, results


def write_markdown(path: Path, input_path: Path, result: GateResult, coverage: Coverage,
                   summaries: list[Summary], providers: list[SharedLibraryProvider]) -> None:
    provider_text = ", ".join(provider.name for provider in providers) or "none"
    status = "pass" if result.passed and coverage.passed else "FAIL"
    lines = [
        "# Transcendental comparison against MPFR",
        "",
        f"Gate: **{status}**. New mismatches: {len(result.new)}; changed known failures: "
        f"{len(result.changed)}; mismatches in correctly rounded domains: {len(result.declared)}; "
        f"stale known failures: {len(result.stale)}; known failures matched: {len(result.known)} "
        f"(not exercised by this run: {result.unexercised}). Coverage: {coverage.status}"
        + ("" if coverage.census is None else f" against census entry `{coverage.census}`")
        + "".join(f"; {difference}" for difference in coverage.differences[:5]) + ".",
        "",
        f"Input: `{input_path.name}`",
        f"Optional external providers: {provider_text}",
        "",
        (
            "MPFR gives the correctly rounded reference in the stated mode. `Value exact` treats "
            "any NaN result as a NaN match because MPFR has one NaN; `Bit exact` is literal "
            "encoding equality. ULP columns include only pairs where both outputs are finite, and "
            "both zeros have distance zero, so `Zero sign` counts the signed-zero mismatches "
            "separately. These counts describe the run; the gate is the known-failures list."
        ),
        "",
        "| Candidate | Format | Operation | Mode | Cases | Value exact | Bit exact | Finite | "
        "Nonfinite mismatch | Zero sign | 0 ULP | 1 ULP | 2-3 | 4-15 | 16-255 | >=256 | Max | "
        "P50 | P90 | P99 |",
        "| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | "
        "---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in summaries:
        lines.append(
            f"| {row.candidate} | {row.format_name} | {row.operation} | {row.mode} | {row.cases} | "
            f"{row.value_exact} ({percent(row.value_exact, row.cases)}) | "
            f"{row.bit_exact} ({percent(row.bit_exact, row.cases)}) | "
            f"{row.finite_pairs} | {row.nonfinite_mismatch} | {row.zero_sign_mismatch} | "
            f"{row.ulp_0} | {row.ulp_1} | {row.ulp_2_3} | {row.ulp_4_15} | {row.ulp_16_255} | "
            f"{row.ulp_256_plus} | {optional_integer(row.ulp_max)} | "
            f"{optional_integer(row.ulp_p50)} | {optional_integer(row.ulp_p90)} | "
            f"{optional_integer(row.ulp_p99)} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", type=Path, required=True, help="MPFR oracle output")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--known-failures", type=Path, required=True)
    parser.add_argument("--write-known-failures", type=Path,
                        help="write the observed mismatches as a new known-failures list")
    parser.add_argument("--census", type=Path, required=True,
                        help="coverage census of the standard invocations")
    parser.add_argument("--write-census", metavar="NAME",
                        help="record this run's coverage in the census as entry NAME")
    parser.add_argument("--require-census", metavar="NAME",
                        help="fail unless this run reproduces census entry NAME")
    parser.add_argument("--expect-manifest", metavar="LINE", action="append", default=[],
                        help="a manifest line the emitter must report, as the driver asked; "
                             "repeat for each option")
    parser.add_argument("--provenance", type=Path)
    parser.add_argument("--core-math-lib", type=Path)
    parser.add_argument("--openlibm-lib", type=Path)
    parser.add_argument("--rlibm-lib", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    cases, manifest, _ = parse_references(args.input)
    reported = manifest_lines(manifest)
    for line in args.expect_manifest:
        if line not in reported:
            raise ValueError(f"{args.input}: the driver asked for `{line}`, which the emitter's "
                             "manifest does not report")
    missing = [case.case_id for case in cases if case.floatlib is None]
    if missing:
        raise ValueError(f"{args.input}: {len(missing)} cases have no FloatLib result, "
                         f"starting with {missing[0]}")
    known = parse_known_failures(args.known_failures)
    if args.write_census is not None and not CENSUS_NAME.fullmatch(args.write_census):
        raise ValueError(f"invalid census entry name {args.write_census!r}")
    if args.write_census is not None and not args.census.exists():
        census: dict[str, CensusEntry] = {}
    else:
        census = read_census(args.census)
    if args.require_census is not None and args.require_census not in census:
        raise ValueError(f"the census has no entry {args.require_census!r}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    provenance = read_provenance(args.provenance)

    providers: list[SharedLibraryProvider] = []
    libraries = {"CORE-MATH": args.core_math_lib, "OpenLibm": args.openlibm_lib,
                 "RLIBM": args.rlibm_lib}
    for name, symbols in PROVIDER_SYMBOLS.items():
        if libraries[name] is not None:
            providers.append(SharedLibraryProvider(name, libraries[name], symbols()))
    rounding_environment = set_round_to_nearest() if providers else "not applicable"

    results: dict[str, list[int | None]] = {"FloatLib": [case.floatlib for case in cases]}
    for provider in providers:
        results[provider.name] = [provider.evaluate(case) for case in cases]
    coverage_records: list[dict[str, object]] = []
    for provider in providers:
        record = provider_coverage(provider.name, provider.supported_keys, cases,
                                   results[provider.name])
        if record["actual_evaluations"] != record["expected_evaluations"]:
            raise ValueError(f"{provider.name}: evaluated {record['actual_evaluations']} cases, "
                             f"expected {record['expected_evaluations']}")
        coverage_records.append(record)
    summaries = summarize(cases, results)

    result = gate(cases, known)
    coverage = check_coverage(cases, manifest, census, result.unexercised, args.require_census)
    passed = result.passed and coverage.passed
    write_details(args.output_dir / "details.tsv", cases, results)
    write_mismatches(args.output_dir / "mismatches.tsv", cases, known)
    write_markdown(args.output_dir / "summary.md", args.input, result, coverage, summaries,
                   providers)
    payload = {
        "adapter": "transcendental_compare",
        "status": "gate_pass" if passed else "gate_fail",
        "comparison_kind": "known-failure gate",
        "conformance": False,
        "input": args.input.name,
        "cases": len(cases),
        "manifest": manifest,
        "gate": {
            "new_mismatches": len(result.new),
            "changed_known_failures": len(result.changed),
            "correctly_rounded_mismatches": len(result.declared),
            "stale_known_failures": len(result.stale),
            "known_failures_matched": len(result.known),
            "known_failures_not_exercised": result.unexercised,
        },
        "coverage": {
            "status": coverage.status,
            "census": coverage.census,
            "entry": None if coverage.census is None else asdict(census[coverage.census]),
            "differences": coverage.differences,
        },
        "rounding_environment": rounding_environment,
        "provenance": provenance,
        "providers": [
            {"name": provider.name, "library": provider.path.name, "sha256": sha256(provider.path)}
            for provider in providers
        ],
        "provider_coverage": coverage_records,
        "summaries": [asdict(summary) for summary in summaries],
    }
    (args.output_dir / "summary.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.write_known_failures is not None:
        count = write_known_failures(args.write_known_failures, cases, manifest, known)
        print(f"wrote {count} known failures to {args.write_known_failures}")
    if args.write_census is not None:
        write_census(args.census, census, args.write_census, census_entry(cases, manifest))
        print(f"recorded census entry {args.write_census!r} ({len(cases)} requests) in "
              f"{args.census}")
    print(args.output_dir / "summary.md")
    print_gate(result, coverage)
    print(
        f"transcendental gate: {'pass' if passed else 'FAIL'} "
        f"({len(cases)} cases, {len(result.known)} known failures matched, "
        f"{len(result.new)} new, {len(result.changed)} changed, "
        f"{len(result.declared)} in correctly rounded domains, {len(result.stale)} stale; "
        f"{coverage_text(coverage)})"
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
