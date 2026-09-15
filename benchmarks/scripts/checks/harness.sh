#!/usr/bin/env bash

# Check the benchmark package and CLI without imposing machine-dependent timing thresholds.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
python3 "$ROOT/benchmarks/scripts/checks/publication.py"
source "$ROOT/tests/lib/lake.sh"
floatlib_benchmark_lake build execFloatSweep execFloatFP8Bench

python3 - "$(floatlib_build_path bin/execFloatSweep)" \
  "$(floatlib_build_path bin/execFloatFP8Bench)" <<'PY'
import csv
import io
import os
import subprocess
import sys

executable = sys.argv[1]
environment = dict(os.environ, BENCH_ITERATIONS="17")
operations = ["add", "sub", "mul", "div", "sqrt", "fma"]
columns = ["implementation", "operation", "precision", "backend", "policy", "expectedCalls",
           "iterations", "totalNanos", "sink"]


def invoke(arguments, *, iterations="17"):
    return subprocess.run([executable, *arguments], text=True, capture_output=True,
                          env=dict(environment, BENCH_ITERATIONS=iterations), check=False)


def measurements(arguments):
    result = invoke(arguments)
    assert result.returncode == 0, result.stderr
    reader = csv.DictReader(io.StringIO(result.stdout))
    assert reader.fieldnames == columns, reader.fieldnames
    rows = list(reader)
    for row in rows:
        assert row["implementation"] == "ExecFloat"
        assert row["backend"] and row["policy"]
        assert row["iterations"] == "17"
        assert int(row["totalNanos"]) >= 0
        assert 0 <= int(row["sink"]) < 2**64
        del row["totalNanos"]
    return rows


all_rows = measurements(["all"])
assert len(all_rows) == 102
coverage = None
for operation in operations:
    rows = measurements([operation])
    assert len(rows) == 17
    assert rows == [row for row in all_rows if row["operation"] == operation]
    precisions = {int(row["precision"]) for row in rows}
    assert len(precisions) == 17 and min(precisions) == 2 and max(precisions) == 4096
    assert coverage is None or coverage == precisions
    coverage = precisions
assert measurements([]) == all_rows

help_result = invoke(["--help"])
assert help_result.returncode == 0 and "usage:" in help_result.stdout
for arguments in [["unknown"], ["add", "extra"]]:
    result = invoke(arguments)
    assert result.returncode == 2 and "usage:" in result.stderr
for iterations in ["0", "invalid"]:
    result = invoke(["add"], iterations=iterations)
    assert result.returncode != 0 and "BENCH_ITERATIONS" in result.stderr

fp8_result = subprocess.run([sys.argv[2]], env=environment, text=True, capture_output=True, check=True)
fp8_rows = list(csv.DictReader(io.StringIO(fp8_result.stdout)))
assert len(fp8_rows) == 48
pairs = {}
for row in fp8_rows:
    key = row["format"], row["operation"]
    pair = pairs.setdefault(key, {})
    assert row["implementation"] not in pair
    pair[row["implementation"]] = row["iterations"], row["sink"]
assert len(pairs) == 24
for key, pair in pairs.items():
    assert set(pair) == {"ExecFloat nominal", "ExecFloat descriptor"}, key
    assert pair["ExecFloat nominal"] == pair["ExecFloat descriptor"], key

print("Benchmark harness passed: 102 precision rows, 24 FP8 pairs, and CLI validation.")
PY
