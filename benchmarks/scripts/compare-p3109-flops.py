#!/usr/bin/env python3
"""Compare P3109 result words, then time identical compiled workloads."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import time


FLOPS_REVISION = "4ead906d8bceefd400620dcc52ec3245f84669e9"
FORMATS = {"Binary4p2sf": 16, "Binary8p4se": 256, "Binary8p3se": 256}
OPERATIONS = ("add", "mul", "div", "fma")
ROOT = Path(__file__).resolve().parents[2]


def command(argv, cwd=None, env=None):
    return subprocess.check_output(argv, cwd=cwd, env=env, text=True).strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(argv, cwd, log, env=None):
    with log.open("w") as stream:
        subprocess.run(argv, cwd=cwd, env=env, stdout=stream,
                       stderr=subprocess.STDOUT, check=True)


def source_record(root, prefix):
    paths = command(["git", "ls-files", "--cached", "--others",
                     "--exclude-standard", "--", prefix, prefix + ".lean"], root).splitlines()
    hashes = {p: digest(root / p) for p in sorted(set(paths))
              if p.endswith(".lean") and (root / p).is_file()}
    return {
        "git_head": command(["git", "rev-parse", "HEAD"], root),
        "tracked_source_modified": bool(command(
            ["git", "status", "--porcelain", "--", prefix, prefix + ".lean"], root)),
        "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": digest(root / "lake-manifest.json"),
        "source_sha256": hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest(),
        "files": hashes,
    }


def percentile(values, fraction):
    values = sorted(values)
    index = (len(values) - 1) * fraction
    lo, hi = math.floor(index), math.ceil(index)
    return values[lo] + (values[hi] - values[lo]) * (index - lo)


def expected_checksum(fixtures, iterations):
    index, checksum = 0, 0
    for i in range(iterations):
        result = fixtures[index][3]
        index = (index + result + i + 1) % 16
        checksum = (checksum * 1664525 + result + index) % (1 << 64)
    return checksum


def host_cpu_ticks():
    ticks = list(map(int, Path("/proc/stat").read_text().splitlines()[0].split()[1:9]))
    return sum(ticks), ticks[3] + ticks[4]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--build-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()
    work = args.work_dir.resolve()
    output = args.output.resolve()
    work.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / "results.json"
    if result_path.exists():
        parser.error("output already contains results.json; choose a fresh directory")
    flops = work / "FLoPS"
    if not flops.exists():
        subprocess.run(["git", "clone", "--filter=blob:none", "--no-checkout",
                        "https://github.com/rutgers-apl/FLoPS.git", str(flops)], check=True)
        subprocess.run(["git", "checkout", FLOPS_REVISION], cwd=flops, check=True)
    if command(["git", "rev-parse", "HEAD"], flops) != FLOPS_REVISION:
        parser.error(f"FLoPS must be at {FLOPS_REVISION}")
    if command(["git", "status", "--porcelain", "Flops"], flops):
        parser.error("FLoPS library sources must be unmodified")
    protocol = ROOT / "benchmarks/lean/FloatLibBenchmarks/Support/P3109Protocol.lean"
    adapter = ROOT / "benchmarks/external/flops/Main.lean"
    shutil.copyfile(protocol, flops / "P3109Protocol.lean")
    shutil.copyfile(adapter, flops / "ComparisonMain.lean")
    lakefile = flops / "lakefile.lean"
    target = ("\nlean_lib P3109Protocol\n"
              "\nlean_exe p3109Comparison where\n  root := `ComparisonMain\n")
    if target not in lakefile.read_text():
        lakefile.write_text(lakefile.read_text() + target)
    env = dict(os.environ, FLOATLIB_BUILD_DIR=str(args.build_dir.resolve()))
    if not args.skip_build:
        build(["lake", "exe", "cache", "get"], flops, work / "flops-cache.log")
        build(["lake", "build", "p3109Comparison"], flops, work / "flops-build.log")
        build(["bash", "-c", 'source tests/lib/lake.sh\n'
               'floatlib_benchmark_lake build execFloatP3109Comparison'],
              ROOT, work / "floatlib-build.log", env)
    executables = {
        "FloatLib": args.build_dir.resolve() / "bin/execFloatP3109Comparison",
        "FLoPS": flops / ".lake/build/bin/p3109Comparison",
    }
    for executable in executables.values():
        if not executable.is_file():
            parser.error(f"missing executable: {executable}")
    allowed = sorted(os.sched_getaffinity(0))
    cpu = args.cpu if args.cpu is not None else allowed[0]
    if cpu not in allowed:
        parser.error(f"CPU {cpu} is outside the process affinity")
    cpu_model = next((line.split(":", 1)[1].strip()
                      for line in Path("/proc/cpuinfo").read_text().splitlines()
                      if line.startswith("model name")), platform.processor())
    records = {
        "protocol": {
            "rounding": "nearest-even", "saturation": "none",
            "formats": FORMATS, "operations": OPERATIONS,
            "binary_inputs": "all ordered encoded pairs, including exceptional values",
            "fma_inputs": "all four-bit triples; eight-bit z=(17*x+29*y+43) mod 256",
            "timing": "16 finite encoded fixtures; result selects next fixture",
            "warmup_iterations": 256, "pilot_iterations": 10000,
            "target_minimum_ns": 100000000, "paired_trials": 9,
            "includes": "input lookup, operation call, encoded result, index and checksum",
            "excludes": "input construction, process startup, file output",
        },
        "environment": {
            "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "cpu_model": cpu_model, "logical_cpu": cpu, "platform": platform.platform(),
            "FloatLib": source_record(ROOT, "FloatLib"),
            "FLoPS": source_record(flops, "Flops"),
            "compilers": {
                "FloatLib": command(["lake", "env", "leanc", "--version"],
                                    ROOT).splitlines()[:3],
                "FLoPS": command(["lake", "env", "leanc", "--version"],
                                 flops).splitlines()[:3],
            },
            "executable_sha256": {name: digest(path) for name, path in executables.items()},
            "adapter_sha256": {
                "protocol": digest(protocol), "FLoPS": digest(adapter),
                "FloatLib": digest(ROOT /
                    "benchmarks/lean/FloatLibBenchmarks/Public/P3109Comparison.lean"),
            },
        },
        "preflight": [], "fixtures": [], "pilots": [], "trials": [], "summary": [],
    }
    vectors = work / "vectors"
    vectors.mkdir(exist_ok=True)
    failed = False
    for fmt, cardinality in FORMATS.items():
        for operation in OPERATIONS:
            files = {}
            for name, executable in executables.items():
                path = vectors / f"{name}-{fmt}-{operation}.bin"
                command(["taskset", "-c", str(cpu), str(executable),
                         fmt, operation, "check", str(path)])
                files[name] = path
            left, right = (files[name].read_bytes() for name in executables)
            expected = cardinality ** (3 if operation == "fma" and cardinality == 16 else 2)
            if len(left) != expected or len(right) != expected:
                raise RuntimeError(f"incorrect preflight count for {fmt}/{operation}")
            differences = [i for i, (x, y) in enumerate(zip(left, right)) if x != y]
            record = {"format": fmt, "operation": operation, "cases": expected,
                      "mismatches": len(differences),
                      "output_sha256": {name: digest(path) for name, path in files.items()},
                      "first_differences": [
                          {"index": i, "FloatLib": left[i], "FLoPS": right[i]}
                          for i in differences[:20]]}
            records["preflight"].append(record)
            failed |= bool(differences)
            print(f"{fmt} {operation}: {expected} cases, {len(differences)} differences", flush=True)
            fixture_bytes = []
            for name, executable in executables.items():
                path = vectors / f"{name}-{fmt}-{operation}-fixtures.bin"
                command(["taskset", "-c", str(cpu), str(executable),
                         fmt, operation, "fixtures", str(path)])
                fixture_bytes.append(path.read_bytes())
            if any(len(data) != 64 for data in fixture_bytes):
                raise RuntimeError("expected sixteen encoded input/output quadruples")
            fixtures_agree = fixture_bytes[0] == fixture_bytes[1]
            failed |= not fixtures_agree
            records["fixtures"].append({
                "format": fmt, "operation": operation, "agree": fixtures_agree,
                "rows": {name: [list(data[i:i+4]) for i in range(0, 64, 4)]
                         for name, data in zip(executables, fixture_bytes)},
            })
    if failed:
        result_path.write_text(json.dumps(records, indent=2) + "\n")
        raise SystemExit("Result agreement failed; no timings collected.")

    def measure(name, fmt, operation, iterations):
        total_before, idle_before = host_cpu_ticks()
        raw = command(["taskset", "-c", str(cpu), str(executables[name]),
                       fmt, operation, "time", str(iterations)])
        total_after, idle_after = host_cpu_ticks()
        count, elapsed, checksum = map(int, raw.split(","))
        if count != iterations or elapsed <= 0:
            raise RuntimeError(f"invalid timing row: {raw}")
        return {"implementation": name, "format": fmt, "operation": operation,
                "iterations": count, "elapsed_ns": elapsed, "checksum": checksum,
                "host_busy_percent": 100 * (1 - (idle_after - idle_before) /
                                             max(1, total_after - total_before))}

    for fmt in FORMATS:
        for operation in OPERATIONS:
            fixtures = next(r["rows"]["FloatLib"] for r in records["fixtures"]
                            if r["format"] == fmt and r["operation"] == operation)
            pilots = [measure(name, fmt, operation, 10000) for name in executables]
            records["pilots"].extend(pilots)
            if any(p["checksum"] != expected_checksum(fixtures, 10000) for p in pilots):
                raise RuntimeError("pilot fixture paths differ")
            iterations = max(10000, math.ceil(10000 * 100000000 /
                                              min(p["elapsed_ns"] for p in pilots)))
            checksum = expected_checksum(fixtures, iterations)
            for trial in range(9):
                order = list(executables)
                if trial % 2:
                    order.reverse()
                pair = []
                for position, name in enumerate(order):
                    row = measure(name, fmt, operation, iterations)
                    row.update(trial=trial, position=position)
                    pair.append(row)
                if any(p["checksum"] != checksum for p in pair):
                    raise RuntimeError("timed fixture paths differ")
                records["trials"].extend(pair)
            for name in executables:
                times = [r["elapsed_ns"] / r["iterations"] for r in records["trials"]
                         if r["implementation"] == name and r["format"] == fmt
                         and r["operation"] == operation]
                records["summary"].append({
                    "implementation": name, "format": fmt, "operation": operation,
                    "median_ns": statistics.median(times),
                    "p05_ns": percentile(times, .05), "p95_ns": percentile(times, .95)})
            result_path.write_text(json.dumps(records, indent=2) + "\n")
            print(f"{fmt} {operation}: nine paired trials complete", flush=True)
    print(f"Wrote {result_path}")


if __name__ == "__main__":
    main()
