#!/usr/bin/env python3
"""Check small-format casts against TensorLib and an encoding oracle, then time finite casts."""

import argparse
from bisect import bisect_left
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import random
import shutil
import statistics
import struct
import subprocess
import time

# Reuse only process, hashing, and measurement-report helpers, not the arithmetic protocol.
spec = importlib.util.spec_from_file_location(
    "comparison_helpers", Path(__file__).with_name("compare-p3109-flops.py"))
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)

ROOT = Path(__file__).resolve().parents[2]
REVISION = "85e61c9eb3211c736ded72b37254e2d608bbdbeb"
FORMATS = {
    "binary16": (5, 10, 15, False),
    "bfloat16": (8, 7, 127, False),
    "e4m3fn": (4, 3, 7, True),
    "e5m2": (5, 2, 15, False),
}
F32 = (8, 23, 127, False)


def bits32(value):
    return struct.unpack("<I", struct.pack("<f", value))[0]


def value32(bits):
    return struct.unpack("<f", struct.pack("<I", bits))[0]


def classify(code, fmt):
    exponent, fraction, _, finite_nan = fmt
    e, m = (code >> fraction) & ((1 << exponent) - 1), code & ((1 << fraction) - 1)
    if e == (1 << exponent) - 1:
        if finite_nan:
            return "nan" if m == (1 << fraction) - 1 else "finite"
        return "nan" if m else "infinity"
    return "zero" if e == 0 and m == 0 else "finite"


def value(code, fmt):
    """Exact small-format finite values; their <=11 significant bits fit in binary64."""
    exponent, fraction, bias, _ = fmt
    e, m = (code >> fraction) & ((1 << exponent) - 1), code & ((1 << fraction) - 1)
    magnitude = math.ldexp(m if e == 0 else (1 << fraction) + m,
                           (1 if e == 0 else e) - bias - fraction)
    return -magnitude if code >> (exponent + fraction) else magnitude


def positive_values(fmt):
    width = fmt[0] + fmt[1]
    return [value(code, fmt) for code in range(1 << width)
            if classify(code, fmt) in ("zero", "finite")]


def encode_expected(code, fmt, levels):
    """RNE by adjacent representable values, independently of either library's bit algorithm."""
    source_class = classify(code, F32)
    sign = (code >> 31) << (fmt[0] + fmt[1])
    infinity = ((1 << fmt[0]) - 1) << fmt[1]
    if source_class == "nan" or (source_class == "infinity" and fmt[3]):
        return None  # Any NaN encoding is accepted; payload/sign/quietness are not compared.
    if source_class == "infinity":
        return sign | infinity
    x = abs(value32(code))
    upper = bisect_left(levels, x)
    if upper == len(levels):
        threshold = levels[-1] + (levels[-1] - levels[-2]) / 2
        # E4M3FN's maximum finite code is even, so a tie remains finite.
        overflow = x > threshold if fmt[3] else x >= threshold
        return (None if fmt[3] else sign | infinity) if overflow else sign | (len(levels) - 1)
    if upper == 0 or levels[upper] == x:
        return sign | upper
    low_distance, high_distance = x - levels[upper - 1], levels[upper] - x
    if low_distance < high_distance:
        upper -= 1
    elif low_distance == high_distance and upper % 2:
        upper -= 1
    return sign | upper


def expected(code, fmt, direction, levels):
    if direction == "encode":
        return encode_expected(code, fmt, levels)
    kind = classify(code, fmt)
    if kind == "nan":
        return None
    if kind == "infinity":
        return ((code >> (fmt[0] + fmt[1])) << 31) | 0x7f800000
    return bits32(value(code, fmt))


def input_words(fmt, direction):
    if direction == "decode":
        return list(range(1 << (fmt[0] + fmt[1] + 1)))
    levels = positive_values(fmt)
    positive = {0, 1, 0x7f7fffff, 0x7f800000}
    boundaries = levels + [(a + b) / 2 for a, b in zip(levels, levels[1:])]
    boundaries.append(levels[-1] + (levels[-1] - levels[-2]) / 2)
    for boundary in boundaries:
        code = bits32(boundary)
        positive.update(c for c in (code - 1, code, code + 1) if 0 <= c <= 0x7f800000)
    # Exercise every source exponent with fixed mantissas, including NaN payload boundaries.
    for e in range(256):
        for m in (0, 1, 0x7fff, 0x8000, 0x8001, 0x3fffff, 0x400000, 0x7f7fff, 0x7fffff):
            positive.add((e << 23) | m)
    words = positive | {code | 0x80000000 for code in positive}
    generator = random.Random(20260915)
    words.update(generator.getrandbits(32) for _ in range(8192))
    return sorted(words)


def write_words(path, words):
    path.write_bytes(struct.pack(f"<{len(words)}I", *words))


def read_words(path, count):
    data = path.read_bytes()
    if len(data) != 4 * count:
        raise RuntimeError(f"wrong output length: {path}")
    return list(struct.unpack(f"<{count}I", data))


def checksum(outputs, iterations):
    index, total = 0, 0
    for i in range(iterations):
        result = outputs[index]
        index = (index + result + i + 1) % len(outputs)
        total = (total * 1664525 + result + index) % (1 << 64)
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--build-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()
    work, output, build_dir = (p.resolve() for p in (args.work_dir, args.output, args.build_dir))
    work.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / "results.json"
    if result_path.exists():
        parser.error("choose an output directory without results.json")
    tensorlib = work / "TensorLib"
    if not tensorlib.exists():
        subprocess.run(["git", "clone", "--quiet", "https://github.com/leanprover/TensorLib.git",
                        str(tensorlib)], check=True)
        subprocess.run(["git", "checkout", "--quiet", REVISION], cwd=tensorlib, check=True)
    if helpers.command(["git", "rev-parse", "HEAD"], tensorlib) != REVISION:
        parser.error(f"TensorLib must be at {REVISION}")
    if helpers.command(["git", "status", "--porcelain", "--", "TensorLib"], tensorlib):
        parser.error("TensorLib library sources must be unmodified")
    protocol = ROOT / "benchmarks/lean/FloatLibBenchmarks/Support/ConversionProtocol.lean"
    adapter = ROOT / "benchmarks/external/tensorlib/Main.lean"
    shutil.copyfile(protocol, tensorlib / "ConversionProtocol.lean")
    shutil.copyfile(adapter, tensorlib / "ComparisonMain.lean")
    lakefile = tensorlib / "lakefile.lean"
    target = ("\nlean_lib ConversionProtocol\n\nlean_exe conversionComparison where\n"
              "  root := `ComparisonMain\n")
    if target not in lakefile.read_text():
        lakefile.write_text(lakefile.read_text() + target)
    if not args.skip_build:
        helpers.build(["lake", "exe", "cache", "get", "TensorLib/Float.lean"],
                      tensorlib, work / "tensorlib-cache.log")
        helpers.build(["lake", "build", "conversionComparison"],
                      tensorlib, work / "tensorlib-build.log")
        helpers.build(["bash", "-c", "source tests/lib/lake.sh\n"
                       "floatlib_benchmark_lake build execFloatTensorLibComparison"],
                      ROOT, work / "floatlib-build.log",
                      dict(os.environ, FLOATLIB_BUILD_DIR=str(build_dir)))
    executables = {"FloatLib": build_dir / "bin/execFloatTensorLibComparison",
                   "TensorLib": tensorlib / ".lake/build/bin/conversionComparison"}
    allowed = sorted(os.sched_getaffinity(0))
    cpu = args.cpu if args.cpu is not None else allowed[0]
    if cpu not in allowed:
        parser.error("requested CPU is not in process affinity")
    records = {
        "protocol": {
            "formats": FORMATS, "rounding": "nearest-even", "saturation": "none",
            "decode_inputs": "every encoding, including signed zeros, infinities, and NaNs",
            "encode_inputs": "all finite destination values and midpoints with Float32 neighbors, "
                             "both signs; exponent/payload boundaries; 8192 seeded random words",
            "nan_comparison": "class only; payload, sign, signaling/quiet bit differences recorded separately",
            "oracle": "adjacent exactly represented binary64 values; nearest-even with explicit overflow",
            "timing": "16 normal finite fixtures shared by both implementations; output selects next input",
            "warmup_iterations": 256, "pilot_iterations": 10000, "paired_trials": 9,
            "target_minimum_ns": 20000000,
            "includes": "lookup, conversion call, encoded output, index and checksum",
            "excludes": "input construction, process startup, file IO",
        },
        "environment": {
            "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "platform": platform.platform(), "logical_cpu": cpu,
            "cpu_model": next(l.split(":", 1)[1].strip()
                              for l in Path("/proc/cpuinfo").read_text().splitlines()
                              if l.startswith("model name")),
            "FloatLib": helpers.source_record(ROOT, "FloatLib"),
            "TensorLib": helpers.source_record(tensorlib, "TensorLib"),
            "compilers": {name: helpers.command(["lake", "env", "leanc", "--version"], path).splitlines()[:3]
                          for name, path in (("FloatLib", ROOT), ("TensorLib", tensorlib))},
            "executable_sha256": {n: helpers.digest(p) for n, p in executables.items()},
            "adapter_sha256": {
                "protocol": helpers.digest(protocol), "TensorLib": helpers.digest(adapter),
                "FloatLib": helpers.digest(ROOT / "benchmarks/lean/FloatLibBenchmarks/Public/TensorLibComparison.lean"),
                "runner": helpers.digest(Path(__file__)),
            },
        },
        "preflight": [], "fixtures": [], "pilots": [], "trials": [], "summary": [],
    }
    vectors = work / "vectors"
    vectors.mkdir(exist_ok=True)

    def execute(name, fmt, direction, mode, input_path, last):
        return helpers.command(["taskset", "-c", str(cpu), str(executables[name]),
                                fmt, direction, mode, str(input_path), str(last)])

    for name, fmt in FORMATS.items():
        levels = positive_values(fmt)
        for direction in ("decode", "encode"):
            words = input_words(fmt, direction)
            input_path = vectors / f"{name}-{direction}-input.bin"
            write_words(input_path, words)
            outputs, hashes = {}, {}
            for implementation in executables:
                path = vectors / f"{implementation}-{name}-{direction}.bin"
                execute(implementation, name, direction, "check", input_path, path)
                outputs[implementation] = read_words(path, len(words))
                hashes[implementation] = helpers.digest(path)
            normalized = []
            if direction == "encode":
                echo_path = vectors / f"{name}-echo.bin"
                execute("TensorLib", "binary32", "echo", "check", input_path, echo_path)
                echoed = read_words(echo_path, len(words))
                normalized = [i for i, (a, b) in enumerate(zip(words, echoed)) if a != b]
                if any(classify(words[i], F32) != "nan" or classify(echoed[i], F32) != "nan"
                       for i in normalized):
                    raise RuntimeError("Float32.ofBits/toBits changed a non-NaN input")
            destination = fmt if direction == "encode" else F32
            oracle_failures = {n: [] for n in executables}
            differences, nan_only = [], []
            for i, code in enumerate(words):
                want = expected(code, fmt, direction, levels)
                for implementation in executables:
                    actual = outputs[implementation][i]
                    if not (classify(actual, destination) == "nan" if want is None else actual == want):
                        oracle_failures[implementation].append(i)
                left, right = (outputs[n][i] for n in executables)
                if left != right:
                    (nan_only if classify(left, destination) == classify(right, destination) == "nan"
                     else differences).append(i)
            def example(i):
                return {"input": f"0x{words[i]:08x}",
                        "input_class": classify(words[i], F32 if direction == "encode" else fmt),
                        **{n: f"0x{v[i]:08x}" for n, v in outputs.items()},
                        "expected": ("nan" if expected(words[i], fmt, direction, levels) is None
                                     else f"0x{expected(words[i], fmt, direction, levels):08x}")}
            row = {
                "format": name, "direction": direction, "cases": len(words),
                "input_sha256": helpers.digest(input_path), "output_sha256": hashes,
                "semantic_differences": len(differences), "nan_encoding_differences": len(nan_only),
                "oracle_failures": {n: len(v) for n, v in oracle_failures.items()},
                "first_differences": [example(i) for i in differences[:20]],
                "first_nan_encoding_differences": [example(i) for i in nan_only[:3]],
                "oracle_counterexamples": {n: [example(i) for i in v[:20]]
                                          for n, v in oracle_failures.items()},
                "float32_nan_inputs_normalized": len(normalized),
                "first_normalized_inputs": [
                    {"input": f"0x{words[i]:08x}", "observed": f"0x{echoed[i]:08x}"}
                    for i in normalized[:3]],
            }
            records["preflight"].append(row)
            result_path.write_text(json.dumps(records, indent=2) + "\n")
            print(f"{name} {direction}: {len(words)} cases; {len(differences)} semantic, "
                  f"{len(nan_only)} NaN-encoding differences; oracle {row['oracle_failures']}", flush=True)

            # Keep normal finite timing independent of exceptional-value disagreements.
            numbers = [-4, -3.5, -3, -2, -1.5, -1, -.75, -.5,
                       .5, .75, 1, 1.5, 2, 3, 3.5, 4]
            fixture_words = [bits32(v) if direction == "encode"
                             else encode_expected(bits32(v), fmt, levels) for v in numbers]
            fixture_path = vectors / f"{name}-{direction}-fixtures.bin"
            write_words(fixture_path, fixture_words)
            fixture_outputs = {}
            for implementation in executables:
                path = vectors / f"{implementation}-{name}-{direction}-fixtures.bin"
                execute(implementation, name, direction, "check", fixture_path, path)
                fixture_outputs[implementation] = read_words(path, 16)
            oracle = [expected(w, fmt, direction, levels) for w in fixture_words]
            if any(v != oracle for v in fixture_outputs.values()):
                raise RuntimeError(f"timing fixture disagreement: {name}/{direction}")
            records["fixtures"].append({"format": name, "direction": direction,
                                        "inputs": fixture_words, "outputs": oracle})
    result_path.write_text(json.dumps(records, indent=2) + "\n")

    def measure(implementation, fixture, iterations):
        name, direction = fixture["format"], fixture["direction"]
        before, idle_before = helpers.host_cpu_ticks()
        raw = execute(implementation, name, direction, "time",
                      vectors / f"{name}-{direction}-fixtures.bin", iterations)
        after, idle_after = helpers.host_cpu_ticks()
        count, elapsed, actual_checksum = map(int, raw.split(","))
        if count != iterations or elapsed <= 0:
            raise RuntimeError(f"invalid timing row: {raw}")
        return {"implementation": implementation, "format": name, "direction": direction,
                "iterations": count, "elapsed_ns": elapsed, "checksum": actual_checksum,
                "host_busy_percent": 100 * (1 - (idle_after - idle_before) / max(1, after - before))}

    for fixture in records["fixtures"]:
        pilots = [measure(n, fixture, 10000) for n in executables]
        if any(p["checksum"] != checksum(fixture["outputs"], 10000) for p in pilots):
            raise RuntimeError("pilot checksum differs")
        records["pilots"].extend(pilots)
        iterations = max(10000, math.ceil(10000 * 20000000 / min(p["elapsed_ns"] for p in pilots)))
        want = checksum(fixture["outputs"], iterations)
        for trial in range(9):
            order = list(executables)
            if trial % 2:
                order.reverse()
            for position, name in enumerate(order):
                row = measure(name, fixture, iterations)
                if row["checksum"] != want:
                    raise RuntimeError("timed checksum differs")
                records["trials"].append(dict(row, trial=trial, position=position))
        for name in executables:
            times = [r["elapsed_ns"] / r["iterations"] for r in records["trials"]
                     if r["implementation"] == name and r["format"] == fixture["format"]
                     and r["direction"] == fixture["direction"]]
            records["summary"].append({
                "implementation": name, "format": fixture["format"], "direction": fixture["direction"],
                "median_ns": statistics.median(times),
                "p05_ns": helpers.percentile(times, .05), "p95_ns": helpers.percentile(times, .95)})
        result_path.write_text(json.dumps(records, indent=2) + "\n")
        print(f"{fixture['format']} {fixture['direction']}: nine paired trials complete", flush=True)
    print(f"Wrote {result_path}")


if __name__ == "__main__":
    main()
