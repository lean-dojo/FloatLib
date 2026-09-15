#!/usr/bin/env python3

"""Measure ordinary CPython float expressions on the shared exact workload.

We include this lane because people will reasonably ask what the same scalar
expression costs in normal Python. It includes interpreter, object, indexing,
and integer-checksum work. The number is end-to-end CPython cost.

The CPython C API exposes Python `float` values through C `double`:
https://docs.python.org/3/c-api/float.html
The optional fused operation is the documented `math.fma`:
https://docs.python.org/3/library/math.html#math.fma
"""

from __future__ import annotations

import math
import os
import platform
import struct
import sys
import time
from collections.abc import Callable
from fractions import Fraction


ARRAY_SIZE = 16
ARRAY_MASK = ARRAY_SIZE - 1
DEPENDENCY_SEED = 14_695_981_039_346_656_037
EXPONENT_MIX = 0x9E3779B97F4A7C15
SIGN_MIX = 0x8000000000000000
ZERO_TAG = 0x2D358DCCAA6C78A5
INFINITY_TAG = 0x8BB84B93962EACC9
NAN_TAG = 0x4F1BBCDC6764C1AB
UINT64_MASK = (1 << 64) - 1
FixtureTrace = tuple[int, int]
OperationRunner = Callable[
    [int, tuple[float, ...], tuple[float, ...], tuple[float, ...], tuple[float, ...]],
    FixtureTrace,
]


def positive_environment(name: str, fallback: int) -> int:
    """Read one strictly positive integer environment variable."""

    text = os.environ.get(name)
    if text is None or text == "":
        return fallback
    try:
        value = int(text)
    except ValueError as error:
        raise SystemExit(f"{name} must be a positive integer: {text}") from error
    if value <= 0:
        raise SystemExit(f"{name} must be a positive integer: {text}")
    return value


def exact_input(index: int, salt: int, negative: bool) -> float:
    """Round one shared exact rational once to CPython's binary64 value."""

    numerator = (index * salt + salt + 1) % 113 + 7
    denominator = (index * 11 + salt) % 29 + 32
    value = float(Fraction(numerator, denominator))
    return -value if negative else value


def workload() -> tuple[
    tuple[float, ...],
    tuple[float, ...],
    tuple[float, ...],
    tuple[float, ...],
]:
    """Construct the same already-rounded input vectors used by the other runners."""

    xs = tuple(exact_input(index, 37, index % 5 == 0) for index in range(ARRAY_SIZE))
    ys = tuple(exact_input(index, 61, index % 3 == 0) for index in range(ARRAY_SIZE))
    sqrt_xs = tuple(exact_input(index, 43, False) for index in range(ARRAY_SIZE))
    return xs, ys, tuple(reversed(xs)), sqrt_xs


def float_bits(value: float) -> int:
    """Return the stored IEEE binary64 payload of one CPython float."""

    return struct.unpack(">Q", struct.pack(">d", value))[0]


def result_fingerprint(value: float) -> int:
    """Use the same normalized binary64 token as the other IEEE adapters."""

    bits = float_bits(value)
    negative = bits >> 63 != 0
    exponent_field = (bits >> 52) & 0x7FF
    significand = bits & 0x000F_FFFF_FFFF_FFFF
    if exponent_field == 0x7FF:
        if significand != 0:
            return NAN_TAG
        return INFINITY_TAG ^ (SIGN_MIX if negative else 0)
    if exponent_field == 0:
        if significand == 0:
            return ZERO_TAG ^ (SIGN_MIX if negative else 0)
        shift = 52 - (significand.bit_length() - 1)
        significand <<= shift
        exponent = -1021 - shift
    else:
        significand |= 1 << 52
        exponent = exponent_field - 1022
    return (
        significand
        ^ ((exponent & UINT64_MASK) * EXPONENT_MIX)
        ^ (SIGN_MIX if negative else 0)
    ) & UINT64_MASK


def mix_sink(sink: int, value: int) -> int:
    """Retain an observable 64-bit result fingerprint."""

    return ((sink ^ value) * 1_099_511_628_211) & UINT64_MASK


def dependent_index(sink: int) -> int:
    """Select the next ordinary fixture from the preceding result."""

    folded = sink ^ (sink >> 32)
    folded ^= folded >> 16
    return folded & ARRAY_MASK


def run_add(
    iterations: int,
    xs: tuple[float, ...],
    ys: tuple[float, ...],
    _zs: tuple[float, ...],
    _sqrt_xs: tuple[float, ...],
) -> FixtureTrace:
    remaining = iterations
    sink = DEPENDENCY_SEED
    fixture_trace = DEPENDENCY_SEED
    while remaining != 0:
        remaining -= 1
        index = dependent_index(sink)
        fixture_trace = mix_sink(fixture_trace, index)
        result = xs[index] + ys[index]
        sink = mix_sink(sink, result_fingerprint(result))
    return sink, fixture_trace


def run_sub(
    iterations: int,
    xs: tuple[float, ...],
    ys: tuple[float, ...],
    _zs: tuple[float, ...],
    _sqrt_xs: tuple[float, ...],
) -> FixtureTrace:
    remaining = iterations
    sink = DEPENDENCY_SEED
    fixture_trace = DEPENDENCY_SEED
    while remaining != 0:
        remaining -= 1
        index = dependent_index(sink)
        fixture_trace = mix_sink(fixture_trace, index)
        result = xs[index] - ys[index]
        sink = mix_sink(sink, result_fingerprint(result))
    return sink, fixture_trace


def run_mul(
    iterations: int,
    xs: tuple[float, ...],
    ys: tuple[float, ...],
    _zs: tuple[float, ...],
    _sqrt_xs: tuple[float, ...],
) -> FixtureTrace:
    remaining = iterations
    sink = DEPENDENCY_SEED
    fixture_trace = DEPENDENCY_SEED
    while remaining != 0:
        remaining -= 1
        index = dependent_index(sink)
        fixture_trace = mix_sink(fixture_trace, index)
        result = xs[index] * ys[index]
        sink = mix_sink(sink, result_fingerprint(result))
    return sink, fixture_trace


def run_div(
    iterations: int,
    xs: tuple[float, ...],
    ys: tuple[float, ...],
    _zs: tuple[float, ...],
    _sqrt_xs: tuple[float, ...],
) -> FixtureTrace:
    remaining = iterations
    sink = DEPENDENCY_SEED
    fixture_trace = DEPENDENCY_SEED
    while remaining != 0:
        remaining -= 1
        index = dependent_index(sink)
        fixture_trace = mix_sink(fixture_trace, index)
        result = xs[index] / ys[index]
        sink = mix_sink(sink, result_fingerprint(result))
    return sink, fixture_trace


def run_sqrt(
    iterations: int,
    _xs: tuple[float, ...],
    _ys: tuple[float, ...],
    _zs: tuple[float, ...],
    sqrt_xs: tuple[float, ...],
) -> FixtureTrace:
    remaining = iterations
    sink = DEPENDENCY_SEED
    fixture_trace = DEPENDENCY_SEED
    sqrt = math.sqrt
    while remaining != 0:
        remaining -= 1
        index = dependent_index(sink)
        fixture_trace = mix_sink(fixture_trace, index)
        result = sqrt(sqrt_xs[index])
        sink = mix_sink(sink, result_fingerprint(result))
    return sink, fixture_trace


def run_fma(
    iterations: int,
    xs: tuple[float, ...],
    ys: tuple[float, ...],
    zs: tuple[float, ...],
    _sqrt_xs: tuple[float, ...],
) -> FixtureTrace:
    if not hasattr(math, "fma"):
        raise SystemExit("this CPython build does not provide math.fma")
    remaining = iterations
    sink = DEPENDENCY_SEED
    fixture_trace = DEPENDENCY_SEED
    fma = math.fma
    while remaining != 0:
        remaining -= 1
        index = dependent_index(sink)
        fixture_trace = mix_sink(fixture_trace, index)
        result = fma(xs[index], ys[index], zs[index])
        sink = mix_sink(sink, result_fingerprint(result))
    return sink, fixture_trace


RUNNERS: dict[str, OperationRunner] = {
    "add": run_add,
    "sub": run_sub,
    "mul": run_mul,
    "div": run_div,
    "sqrt": run_sqrt,
    "fma": run_fma,
}


def main() -> None:
    if (
        sys.float_info.radix != 2
        or sys.float_info.mant_dig != 53
        or struct.calcsize("d") != 8
    ):
        raise SystemExit("the CPython lane requires an IEEE binary64 float payload")

    operation = os.environ.get("FORMAT_COMPARE_OPERATION")
    if operation not in RUNNERS:
        raise SystemExit(f"unsupported FORMAT_COMPARE_OPERATION: {operation}")
    width = os.environ.get("FORMAT_COMPARE_WIDTH")
    if width != "64":
        raise SystemExit("the CPython float lane supports only width 64")
    if operation == "fma" and not hasattr(math, "fma"):
        raise SystemExit("this CPython build does not provide math.fma")

    iterations = positive_environment("FORMAT_COMPARE_ITERATIONS", 100_000)
    warmup_iterations = positive_environment(
        "FORMAT_COMPARE_WARMUP_ITERATIONS", 256
    )
    agreement_iterations = positive_environment(
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS", 256
    )
    inputs = workload()
    runner = RUNNERS[operation]

    # We deliberately keep Python's integer and object overhead in this row.
    # The question here is what an ordinary CPython expression costs end to
    # end, not how many bare FPU instructions the processor can retire.
    warmup_sink, _ = runner(warmup_iterations, *inputs)
    agreement_sink, agreement_fixture_trace = runner(
        agreement_iterations, *inputs
    )
    start = time.perf_counter_ns()
    sink, fixture_trace = runner(iterations, *inputs)
    stop = time.perf_counter_ns()
    if warmup_sink < 0:
        raise AssertionError("an unsigned payload cannot be negative")

    backend = (
        f"CPython {platform.python_version()} float expression; "
        "interpreter and object overhead included"
    )
    print(
        "implementation,family,format,totalBits,operation,executionClass,"
        "backend,measurementMethod,iterations,totalNanos,sink,fixtureTraceDigest,"
        "agreementIterations,agreementSink,agreementFixtureTraceDigest"
    )
    print(
        f"CPython,python-runtime,python-float64,64,{operation},dynamic-runtime,"
        f"{backend},result-dependent-fixture-chain,{iterations},{stop - start},"
        f"{sink},{fixture_trace},{agreement_iterations},{agreement_sink},"
        f"{agreement_fixture_trace}"
    )


if __name__ == "__main__":
    main()
