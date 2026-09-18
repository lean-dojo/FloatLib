#!/usr/bin/env python3
"""Exercise the regression CLI's fail-closed baseline contract without timing thresholds.

Pass the built execFloatPerformanceRegression path to also smoke every runtime row and filter.
"""

import csv
import io
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / "benchmarks/scripts/performance-regression.sh"
FORMATS = {"binary16": 16, "binary32": 32, "binary64": 64, "binary128": 128,
           "binary256": 256, "descriptor24": 24, "descriptor48": 48, "descriptor64": 64,
           "posit16": 16, "posit32": 32, "posit65": 65}
OPERATIONS = ["add", "sub", "mul", "div", "sqrt", "fma"]
HEADER = ["schema", "metric", "subject", "baseline", "maxRatio", "iterations",
          "warmupIterations", "sink", "backend"]
RUNTIME_HEADER = ["schema", "format", "totalBits", "operation", "inputClass", "backend",
                  "iterations", "warmupIterations", "totalNanos", "sink"]
ENV = {key: value for key, value in os.environ.items() if not key.startswith("PERF_")}
ENVIRONMENT = """lean=test
ccCommand=cc
ccPath=/test/cc
cc=test
arch=test
cpu=test
cpuCount=1
cpuAffinity=0
"""


def subjects():
    result = set()
    for name in FORMATS:
        for operation in OPERATIONS:
            classes = ["ordinary"]
            if name in {"binary32", "binary256", "descriptor24", "posit32", "posit65"}:
                classes += ["zero"]
                if name in {"binary32", "binary256", "descriptor24"}:
                    classes += ["subnormal"]
                    if operation != "sqrt":
                        classes += ["tie"]
                if operation in {"add", "sub", "fma"}:
                    classes += ["cancel", "gap"]
            result.update((name, operation, kind) for kind in classes)
    return result


SUBJECTS = subjects()
assert len(SUBJECTS) == 159


def baseline_rows():
    rows = []
    for metric in ["compile-nanos", "generated-c-body-bytes"]:
        for name in ["binary32", "binary64", "binary128", "posit32", "binary256"]:
            rows.append(["2", metric, name, "100", "1.35", "-", "-", "-", "-"])
    for name, operation, kind in sorted(SUBJECTS):
        iterations = (100000 if name in {"binary16", "binary32", "binary64"} else
                      20000 if name in {"posit16", "posit32"} else
                      10000 if name == "binary128" else 5000)
        rows.append(["2", "runtime-nanos-per-operation", f"{name}/{operation}/{kind}",
                     "100", "1.35", str(iterations), "256", "123", "baseline kernel"])
    return rows


def invoke(args, **environment):
    return subprocess.run(["bash", str(SCRIPT), *map(str, args)],
                          env=dict(ENV, **environment), text=True, capture_output=True,
                          timeout=30, check=False)


def parser_checks(directory):
    baseline = directory / "baseline"
    baseline.mkdir()
    path = baseline / "baseline.csv"
    env_path = baseline / "environment.env"
    env_path.write_text(ENVIRONMENT)
    good = baseline_rows()

    def write(rows=good, header=HEADER):
        with path.open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(header)
            writer.writerows(rows)

    def reject(message, **environment):
        result = invoke(["validate", baseline], **environment)
        assert result.returncode != 0, result.stdout
        assert message in result.stderr, (message, result.stderr)

    # A complete baseline is accepted; focused checks still require that complete baseline.
    write()
    for selection in [{}, {"PERF_FORMAT": "descriptor24", "PERF_OPERATION": "fma",
                           "PERF_INPUT_CLASS": "tie"}]:
        result = invoke(["validate", baseline], **selection)
        assert result.returncode == 0, result.stderr
    path.unlink()
    reject("baseline.csv")
    write()
    env_path.unlink()
    reject("environment.env")
    env_path.write_text(ENVIRONMENT)
    for index in [0, 5, 10, len(good) - 1]:
        write(good[:index] + good[index + 1:])
        reject("baseline metric mismatch")
    write(good[:-1])
    reject("baseline metric mismatch", PERF_FORMAT="binary32")
    write(good + [good[0]])
    reject("duplicate metric")
    write(good, HEADER[:-1])
    reject("expected CSV header")
    write([["runtime-nanos-per-add", "binary32", "1", "1.35"]],
          ["metric", "subject", "baseline", "maxRatio"])
    reject("old baselines require re-recording")
    for index, column, values, message in [
        (0, 0, ["1", "3"], "unsupported schema"),
        (0, 1, ["unknown", "runtime-nanos-per-add"], "unexpected or duplicate metric"),
        (10, 2, ["binary32/add/missing", "posit32/sqrt/tie"], "unexpected or duplicate metric"),
        (0, 3, ["NaN", "inf", "0", "-1", "oops"], "performance data:"),
        (0, 4, ["NaN", "inf", "0", "-1", "oops"], "performance data:"),
        (10, 5, ["0", "1.5", "01", "-1", "nan"], "performance data:"),
        (10, 6, ["0", "1.5", "-1"], "performance data:"),
        (10, 7, [str(2**64), "-1", "1.5", "NaN"], "performance data:"),
        (10, 8, ["-", " "], "runtime metrics require a backend name"),
        (0, 5, ["1"], "compile metrics require"),
        (0, 8, ["kernel"], "compile metrics require"),
    ]:
        for value in values:
            rows = [row.copy() for row in good]
            rows[index][column] = value
            write(rows)
            reject(message)
    rows = [row.copy() for row in good]
    rows[0][3:5] = ["1e308", "1e308"]
    write(rows)
    reject("budget product is not finite")
    write([good[0][:-1], *good[1:]])
    reject("missing or extra CSV fields")
    write([good[0] + ["extra"], *good[1:]])
    reject("missing or extra CSV fields")
    write()
    with path.open("a") as stream:
        stream.write('"unterminated')
    reject("performance data:")
    write()
    for environment in [ENVIRONMENT + "cpuCount=2\n", ENVIRONMENT.replace("cpuCount=1\n", ""),
                        ENVIRONMENT.replace("cpuCount=1", "cpuCount=0")]:
        env_path.write_text(environment)
        reject("performance data:")
    env_path.write_text(ENVIRONMENT)
    reject("workload settings mismatch", PERF_ITERATIONS="17")
    reject("workload settings mismatch", PERF_WARMUP_ITERATIONS="17")
    reject("select no rows", PERF_FORMAT="posit32", PERF_INPUT_CLASS="subnormal")
    reject("invalid PERF_OPERATION", PERF_OPERATION="unknown")
    reject("PERF_FULL=1 requires", PERF_FULL="1", PERF_FORMAT="binary32")
    reject("PERF_FULL=1 requires", PERF_FULL="1", PERF_SKIP_CODEGEN="1")
    for mode, environment, message in [
        ("check", {}, "requires PERF_BASELINE_DIR"),
        ("record", {"PERF_OPERATION": "add"}, "record requires full runtime coverage"),
        ("record", {"PERF_ITERATIONS": "0"}, "expected a positive integer"),
    ]:
        output = directory / "must-not-be-created"
        result = invoke([mode, output], **environment)
        assert result.returncode != 0 and message in result.stderr, result.stderr
        assert not output.exists(), "invalid configuration reached the build stage"
    print("Performance parser passed: complete schema accepted; missing/malformed baselines rejected.")


def runtime_checks(executable):
    environment = dict(ENV, PERF_ITERATIONS="32", PERF_WARMUP_ITERATIONS="16")

    def run(**filters):
        return subprocess.run([str(executable)], env=dict(environment, **filters),
                              text=True, capture_output=True, timeout=120, check=False)

    def rows(**filters):
        result = run(**filters)
        assert result.returncode == 0, result.stderr
        reader = csv.DictReader(io.StringIO(result.stdout))
        assert reader.fieldnames == RUNTIME_HEADER, reader.fieldnames
        measured = {}
        for row in reader:
            key = tuple(row[field] for field in ["format", "operation", "inputClass"])
            assert key not in measured and key in SUBJECTS, key
            assert row["schema"] == "2" and row["backend"].strip(), row
            assert int(row["totalBits"]) == FORMATS[key[0]], row
            assert row["iterations"] == "32" and row["warmupIterations"] == "16", row
            assert int(row["totalNanos"]) > 0 and 0 <= int(row["sink"]) < 2**64, row
            del row["totalNanos"]
            measured[key] = row
        return measured

    all_rows = rows()
    assert all_rows.keys() == SUBJECTS
    assert rows(PERF_REVERSE="1") == all_rows
    for key, column, choices in [("PERF_FORMAT", 0, FORMATS), ("PERF_OPERATION", 1, OPERATIONS),
                                  ("PERF_INPUT_CLASS", 2,
                                   ["ordinary", "zero", "subnormal", "cancel", "gap", "tie"])]:
        for choice in choices:
            assert rows(**{key: choice}) == {k: v for k, v in all_rows.items() if k[column] == choice}
    for filters in [{"PERF_FORMAT": "unknown"}, {"PERF_OPERATION": "unknown"},
                    {"PERF_INPUT_CLASS": "unknown"}, {"PERF_ITERATIONS": "0"},
                    {"PERF_WARMUP_ITERATIONS": "bad"}, {"PERF_REVERSE": "2"},
                    {"PERF_FORMAT": "posit32", "PERF_INPUT_CLASS": "subnormal"},
                    {"PERF_OPERATION": "sqrt", "PERF_INPUT_CLASS": "tie"}]:
        assert run(**filters).returncode != 0, filters
    print("Performance runtime passed: 159 rows, reversed trials, every format/operation/class filter.")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="floatlib-performance-parser-") as directory:
        parser_checks(Path(directory))
    if len(sys.argv) == 2:
        runtime_checks(Path(sys.argv[1]).resolve())
    elif len(sys.argv) != 1:
        raise SystemExit(f"usage: {sys.argv[0]} [execFloatPerformanceRegression]")
