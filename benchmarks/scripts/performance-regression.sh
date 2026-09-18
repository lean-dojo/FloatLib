#!/usr/bin/env bash

set -euo pipefail

export LC_ALL=C

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

mode="${1:-check}"
timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
output="${2:-${TMPDIR:-/tmp}/floatlib-benchmarks/performance-regression/$timestamp}"
baseline_dir="${PERF_BASELINE_DIR:-}"
runs="${PERF_RUNS:-5}"
compile_runs="${PERF_COMPILE_RUNS:-3}"
cpu="${PERF_CPU:-}"
skip_codegen="${PERF_SKIP_CODEGEN:-0}"
full="${PERF_FULL:-0}"

usage() {
  echo "usage: $0 [check|record] [new-output-directory] | validate baseline-directory"
  echo "  record writes baseline.csv and environment.env for review"
  echo "  check requires PERF_BASELINE_DIR pointing to a reviewed baseline directory"
  echo "  validate checks baseline schema and workload settings without compiling"
  echo "  PERF_FORMAT / PERF_OPERATION / PERF_INPUT_CLASS select runtime rows for check"
  echo "  PERF_ITERATIONS / PERF_WARMUP_ITERATIONS set positive counts (must match baseline)"
  echo "  PERF_FULL=1 requires unfiltered coverage and all generated-code checks"
}
if [[ "$#" -eq 1 && ("$mode" == --help || "$mode" == -h) ]]; then
  usage
  exit 0
fi
if [[ "$#" -gt 2 || ("$mode" != check && "$mode" != record && "$mode" != validate) ]]; then
  usage >&2
  exit 2
fi
for count in "$runs" "$compile_runs"; do
  if ! [[ "$count" =~ ^[1-9][0-9]*$ ]]; then
    echo "trial counts must be positive integers: $count" >&2
    exit 2
  fi
done
if [[ "$full" != 0 && "$full" != 1 ]]; then
  echo "PERF_FULL must be 0 or 1: $full" >&2
  exit 2
fi
if [[ "$skip_codegen" != 0 && "$skip_codegen" != 1 ]]; then
  echo "PERF_SKIP_CODEGEN must be 0 or 1: $skip_codegen" >&2
  exit 2
fi
if [[ -n "$cpu" ]]; then
  if ! command -v taskset >/dev/null 2>&1 ||
      ! taskset --cpu-list "$cpu" true >/dev/null 2>&1; then
    echo "PERF_CPU is not a valid available CPU list: $cpu" >&2
    exit 2
  fi
fi
if [[ "$mode" != validate && ( -e "$output" || -L "$output" ) ]]; then
  echo "output path already exists; choose a new directory: $output" >&2
  exit 2
fi

# The same parser validates a selected baseline before compilation and reads it for comparison.
performance_data() {
  python3 - "$@" <<'PY'
import csv
import math
import os
import re
import statistics
import sys
from pathlib import Path

SCHEMA = "2"
COMPILE_FORMATS = {"binary32": 32, "binary64": 64, "binary128": 128, "posit32": 32, "binary256": 256}
FORMATS = {"binary16": 16, "binary32": 32, "binary64": 64, "binary128": 128,
           "binary256": 256, "descriptor24": 24, "descriptor48": 48, "descriptor64": 64,
           "posit16": 16, "posit32": 32, "posit65": 65}
OPERATIONS = ["add", "sub", "mul", "div", "sqrt", "fma"]
CLASSES = ["ordinary", "zero", "subnormal", "cancel", "gap", "tie"]
BUDGETS = {
    "compile-nanos": 1.30,
    "generated-c-body-bytes": 1.15,
    "runtime-nanos-per-operation": 1.35,
}
BASELINE_HEADER = ["schema", "metric", "subject", "baseline", "maxRatio",
                   "iterations", "warmupIterations", "sink", "backend"]
RUNTIME_HEADER = ["schema", "format", "totalBits", "operation", "inputClass", "backend",
                  "iterations", "warmupIterations", "totalNanos", "sink"]
ENVIRONMENT_KEYS = {
    "lean", "ccCommand", "ccPath", "cc", "arch", "cpu", "cpuCount", "cpuAffinity",
}


def classes_for(name, operation):
    classes = ["ordinary"]
    binary = name in {"binary32", "binary256", "descriptor24"}
    if binary or name in {"posit32", "posit65"}:
        classes.append("zero")
        if binary:
            classes.append("subnormal")
        if operation in {"add", "sub", "fma"}:
            classes.extend(["cancel", "gap"])
        if binary and operation != "sqrt":
            classes.append("tie")
    return classes


SUBJECTS = {f"{name}/{operation}/{kind}": (name, operation, kind)
            for name in FORMATS for operation in OPERATIONS
            for kind in classes_for(name, operation)}
EXPECTED = {(metric, name) for metric in ["compile-nanos", "generated-c-body-bytes"]
            for name in COMPILE_FORMATS} | {("runtime-nanos-per-operation", s) for s in SUBJECTS}


def read_rows(path, header):
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, strict=True)
        if reader.fieldnames != header:
            raise ValueError(f"{path}: expected CSV header {header}; old baselines require re-recording")
        rows = list(reader)
    for row in rows:
        if None in row or any(value is None or value == "" for value in row.values()):
            raise ValueError(f"{path}: missing or extra CSV fields")
    return rows


def positive_number(text, context):
    value = float(text)
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"{context}: expected a finite positive number, got {text!r}")
    return value


def natural(text, context):
    if not re.fullmatch(r"0|[1-9][0-9]*", text):
        raise ValueError(f"{context}: expected a canonical natural number, got {text!r}")
    return int(text)


def positive_integer(text, context):
    value = natural(text, context)
    if value == 0:
        raise ValueError(f"{context}: expected a positive integer")
    return value


def sink_value(text, context):
    value = natural(text, context)
    if value >= 2**64:
        raise ValueError(f"{context}: invalid UInt64 sink")
    return value


def default_iterations(name):
    if name in {"binary16", "binary32", "binary64"}:
        return 100000
    if name in {"posit16", "posit32"}:
        return 20000
    return 10000 if name == "binary128" else 5000


def selection():
    choices = [os.environ.get(key) for key in ["PERF_FORMAT", "PERF_OPERATION", "PERF_INPUT_CLASS"]]
    for key, value, allowed in zip(["PERF_FORMAT", "PERF_OPERATION", "PERF_INPUT_CLASS"], choices,
                                   [FORMATS, OPERATIONS, CLASSES]):
        if value is not None and value not in allowed:
            raise ValueError(f"invalid {key}: {value!r}")
    selected = {subject for subject, parts in SUBJECTS.items()
                if all(value is None or value == part for value, part in zip(choices, parts))}
    if not selected:
        raise ValueError("performance filters select no rows")
    for key in ["PERF_ITERATIONS", "PERF_WARMUP_ITERATIONS"]:
        if key in os.environ:
            positive_integer(os.environ[key], key)
    return selected


def settings(subject):
    name = SUBJECTS[subject][0]
    return (positive_integer(os.environ.get("PERF_ITERATIONS", str(default_iterations(name))),
                             "PERF_ITERATIONS"),
            positive_integer(os.environ.get("PERF_WARMUP_ITERATIONS", "256"),
                             "PERF_WARMUP_ITERATIONS"))


def read_baseline(directory, selected):
    path = directory / "baseline.csv"
    baseline = {}
    for row in read_rows(path, BASELINE_HEADER):
        key = row["metric"], row["subject"]
        if row["schema"] != SCHEMA:
            raise ValueError(f"{path}: unsupported schema {row['schema']!r}; record a new baseline")
        if key not in EXPECTED or key in baseline:
            raise ValueError(f"{path}: unexpected or duplicate metric {key}")
        reference = positive_number(row["baseline"], f"{path}: {key} baseline")
        budget = positive_number(row["maxRatio"], f"{path}: {key} maxRatio")
        if not math.isfinite(reference * budget):
            raise ValueError(f"{path}: {key} budget product is not finite")
        if key[0] == "runtime-nanos-per-operation":
            iterations = positive_integer(row["iterations"], str(path))
            warmup = positive_integer(row["warmupIterations"], str(path))
            sink = sink_value(row["sink"], str(path))
            if not row["backend"].strip() or row["backend"] == "-":
                raise ValueError(f"{path}: runtime metrics require a backend name")
            if key[1] in selected and (iterations, warmup) != settings(key[1]):
                raise ValueError(f"{path}: workload settings mismatch for {key[1]}")
            identity = (iterations, warmup, sink)
        else:
            if any(row[key] != "-" for key in ["iterations", "warmupIterations", "sink", "backend"]):
                raise ValueError(f"{path}: compile metrics require '-' runtime fields")
            identity = ("-", "-", "-")
        baseline[key] = reference, budget, identity, row["backend"]
    if baseline.keys() != EXPECTED:
        raise ValueError(f"{path}: baseline metric mismatch; missing={sorted(EXPECTED - baseline.keys())}")
    return baseline


def validate_environment(directory):
    path = directory / "environment.env"
    fields = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, separator, value = line.partition("=")
        if not separator or not value.strip() or key in fields:
            raise ValueError(f"{path}: invalid or duplicate environment field {key!r}")
        fields[key] = value
    if fields.keys() != ENVIRONMENT_KEYS:
        raise ValueError(f"{path}: environment fields do not match the recorded schema")
    positive_integer(fields["cpuCount"], f"{path}: cpuCount")


def measurements(output, runs, compile_runs, selected):
    rows = []
    path = output / "raw/compile-nanos.csv"
    compile_samples = {name: {} for name in COMPILE_FORMATS}
    for row in read_rows(path, ["format", "trial", "nanos"]):
        name = row["format"]
        trial = positive_integer(row["trial"], str(path))
        if name not in COMPILE_FORMATS or trial > compile_runs or trial in compile_samples[name]:
            raise ValueError(f"{path}: unexpected or duplicate compile trial {name}, {trial}")
        compile_samples[name][trial] = positive_integer(row["nanos"], str(path))
    for name, samples in compile_samples.items():
        if len(samples) != compile_runs:
            raise ValueError(f"{path}: {name} expected {compile_runs} compile trials")
        rows.append(("compile-nanos", name, statistics.median(samples.values()), "-", "-", "-", "-"))

    path = output / "raw/code-size.csv"
    sizes = {}
    for row in read_rows(path, ["format", "bytes"]):
        name = row["format"]
        if name not in COMPILE_FORMATS or name in sizes:
            raise ValueError(f"{path}: unexpected or duplicate code-size row {name}")
        sizes[name] = positive_integer(row["bytes"], str(path))
    if sizes.keys() != COMPILE_FORMATS.keys():
        raise ValueError(f"{path}: missing code-size rows")
    rows.extend(("generated-c-body-bytes", name, sizes[name], "-", "-", "-", "-")
                for name in COMPILE_FORMATS)

    runtime = {subject: [] for subject in sorted(selected)}
    for trial in range(1, runs + 1):
        path = output / f"raw/runtime-{trial}.csv"
        seen = set()
        for row in read_rows(path, RUNTIME_HEADER):
            subject = "/".join(row[key] for key in ["format", "operation", "inputClass"])
            if row["schema"] != SCHEMA or subject not in selected or subject in seen:
                raise ValueError(f"{path}: unexpected schema, row, or duplicate {subject}")
            seen.add(subject)
            if natural(row["totalBits"], str(path)) != FORMATS[row["format"]]:
                raise ValueError(f"{path}: invalid width for {subject}")
            iterations = positive_integer(row["iterations"], str(path))
            warmup = positive_integer(row["warmupIterations"], str(path))
            if (iterations, warmup) != settings(subject):
                raise ValueError(f"{path}: workload settings mismatch for {subject}")
            sink = sink_value(row["sink"], str(path))
            nanos = positive_integer(row["totalNanos"], str(path))
            if not row["backend"].strip() or row["backend"] == "-":
                raise ValueError(f"{path}: runtime metrics require a backend name")
            runtime[subject].append((row["backend"], iterations, warmup, sink, nanos))
        if seen != selected:
            raise ValueError(f"{path}: missing runtime rows {sorted(selected - seen)}")
    for subject, samples in runtime.items():
        identities = {sample[:4] for sample in samples}
        if len(identities) != 1:
            raise ValueError(f"{output}: {subject} runtime identity changed between trials")
        backend, iterations, warmup, sink = identities.pop()
        value = statistics.median(sample[4] / iterations for sample in samples)
        rows.append(("runtime-nanos-per-operation", subject, value, iterations, warmup, sink, backend))
    for metric, subject, value, *_ in rows:
        positive_number(value, f"{metric}, {subject}")
    return rows


def main():
    action = sys.argv[1]
    selected = selection()
    if action == "selection":
        if sys.argv[2] == "record" and selected != SUBJECTS.keys():
            raise ValueError("record requires full runtime coverage; unset PERF_FORMAT/OPERATION/INPUT_CLASS")
        if os.environ.get("PERF_FULL", "0") == "1" and (
                selected != SUBJECTS.keys() or os.environ.get("PERF_SKIP_CODEGEN", "0") != "0"):
            raise ValueError("PERF_FULL=1 requires all runtime rows and generated-code checks")
        return
    if action == "validate":
        directory = Path(sys.argv[2])
        read_baseline(directory, selected)
        validate_environment(directory)
        return

    output = Path(sys.argv[2])
    baseline_dir = Path(sys.argv[3])
    mode = sys.argv[4]
    rows = measurements(output, int(sys.argv[5]), int(sys.argv[6]), selected)
    full = selected == SUBJECTS.keys() and os.environ.get("PERF_SKIP_CODEGEN", "0") == "0"
    coverage = f"{'FULL' if full else 'PARTIAL'} gate: {len(selected)}/{len(SUBJECTS)} runtime rows"
    with (output / "coverage.txt").open("w") as stream:
        stream.write(f"schema={SCHEMA}\n{coverage}\ncodegen={os.environ.get('PERF_SKIP_CODEGEN', '0') == '0'}\n")
    print(coverage)
    if mode == "record":
        path = output / "baseline.csv"
        with path.open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(BASELINE_HEADER)
            writer.writerows((SCHEMA, metric, subject, value, BUDGETS[metric], *identity)
                             for metric, subject, value, *identity in rows)
        read_baseline(output, selected)
        validate_environment(output)
        print(f"baseline for review: {path}")
        print(f"baseline environment: {output / 'environment.env'}")
        print("Review both files before selecting this directory with PERF_BASELINE_DIR.")
        return

    baseline = read_baseline(baseline_dir, selected)
    with (output / "measurements.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["metric", "subject", "value", "iterations", "warmupIterations", "sink", "backend"])
        writer.writerows(rows)
    failed = False
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(["metric", "subject", "current", "baseline", "maxAllowed", "ratio", "status",
                     "baselineBackend", "currentBackend"])
    for metric, subject, value, iterations, warmup, sink, backend in rows:
        reference, budget, reference_identity, reference_backend = baseline[metric, subject]
        if (iterations, warmup, sink) != reference_identity:
            raise ValueError(f"runtime sink or workload settings changed for {subject}; investigate before re-recording")
        maximum = reference * budget
        status = "pass" if value <= maximum else "FAIL"
        failed |= status == "FAIL"
        writer.writerow([metric, subject, f"{value:.3f}", f"{reference:.3f}", f"{maximum:.3f}",
                         f"{value / reference:.3f}", status, reference_backend, backend])
    raise SystemExit(1 if failed else 0)


try:
    main()
except (OSError, ValueError, OverflowError, csv.Error) as error:
    raise SystemExit(f"performance data: {error}")
PY
}

performance_data selection "$mode"
if [[ "$mode" == validate ]]; then
  if [[ "$#" != 2 ]]; then
    usage >&2
    exit 2
  fi
  performance_data validate "$2"
  echo "baseline schema and workload settings validated: $2"
  exit 0
fi

if [[ "$mode" == check ]]; then
  if [[ -z "$baseline_dir" ]]; then
    echo "check requires PERF_BASELINE_DIR; record and review a baseline first" >&2
    exit 2
  fi
  if [[ ! -d "$baseline_dir" ]]; then
    echo "baseline directory does not exist: $baseline_dir" >&2
    exit 2
  fi
  baseline_dir="$(cd "$baseline_dir" && pwd -P)"
  performance_data validate "$baseline_dir"
fi

mkdir -p "$output/raw" "$output/compile"
output="$(cd "$output" && pwd -P)"
compile_template="$root/benchmarks/lean/FloatLibBenchmarks/Public/PerformanceCompileProbe.lean.in"
environment="$output/environment.env"

cd "$root"
floatlib_benchmark_lake build FloatLibBenchmarks.Public.PerformanceRegression
lean_path="$(floatlib_benchmark_lake env printenv LEAN_PATH | tail -n 1)"
lean_executable="$(floatlib_benchmark_lake env which lean | tail -n 1)"
lean_prefix="$("$lean_executable" --print-prefix)"
# Match Lake's compiler selection; bundled and custom compilers use different default flags.
compiler_kind=custom
if [[ ${LEAN_CC+x} ]]; then
  compiler="$LEAN_CC"
elif [[ -e "$lean_prefix/bin/clang" ]]; then
  compiler="$lean_prefix/bin/clang"
  compiler_kind=bundled
else
  compiler="${CC-cc}"
fi
compiler_executable="$(command -v "$compiler")"
if [[ -n "$cpu" ]]; then
  actual_affinity="$(
    taskset --cpu-list "$cpu" \
      awk '/^Cpus_allowed_list:/ {print $2}' /proc/self/status
  )"
else
  actual_affinity="$(awk '/^Cpus_allowed_list:/ {print $2}' /proc/self/status)"
fi

{
  echo "lean=$("$lean_executable" --version | head -n 1)"
  echo "ccCommand=$compiler_kind:$compiler"
  echo "ccPath=$compiler_executable"
  echo "cc=$("$compiler_executable" --version | head -n 1)"
  echo "arch=$(uname -m)"
  echo "cpu=$(sed -n 's/^model name[[:space:]]*: //p' /proc/cpuinfo | head -n 1)"
  echo "cpuCount=$(env -u OMP_NUM_THREADS -u OMP_THREAD_LIMIT nproc)"
  echo "cpuAffinity=$actual_affinity"
} >"$environment"

if [[ "$mode" == check ]] && ! cmp -s "$baseline_dir/environment.env" "$environment"; then
  echo "performance baseline requires the same toolchain and machine configuration" >&2
  diff -u "$baseline_dir/environment.env" "$environment" >&2 || true
  exit 1
fi

if [[ "$skip_codegen" == 0 ]]; then
  bash benchmarks/scripts/checks/configured-binary-codegen.sh
  bash benchmarks/scripts/checks/posit-codegen.sh
  bash benchmarks/scripts/checks/automatic-selection-codegen.sh
fi

# Compile one format instantiation at a time into disposable outputs. Imported oleans remain warm
# and fixed, so these are incremental per-format compilation measurements rather than clean-build
# timings polluted by unrelated dependencies.
formats=(binary32 binary64 binary128 posit32 binary256)
printf '%s\n' "format,trial,nanos" >"$output/raw/compile-nanos.csv"
for format in "${formats[@]}"; do
  case "$format" in
    binary32)
      probe_type='FloatLibBenchmarks.Public.Sweep.P24'
      result_bits='FloatLibBenchmarks.Public.Sweep.resultBits'
      ;;
    binary64)
      probe_type='FloatLibBenchmarks.Public.Sweep.P53'
      result_bits='FloatLibBenchmarks.Public.Sweep.resultBits'
      ;;
    binary128)
      probe_type='FloatLibBenchmarks.Public.Sweep.P113'
      result_bits='FloatLibBenchmarks.Public.Sweep.resultBits'
      ;;
    posit32)
      probe_type='ExecFloat.Posit 32'
      result_bits='FloatLibBenchmarks.Support.Posit.resultBits'
      ;;
    binary256)
      probe_type='FloatLibBenchmarks.Public.Sweep.P237'
      result_bits='FloatLibBenchmarks.Public.Sweep.resultBits'
      ;;
  esac
  for ((trial = 1; trial <= compile_runs; ++trial)); do
    trial_dir="$output/compile/$format/$trial"
    mkdir -p "$trial_dir"
    generated_source="$trial_dir/PerformanceCompileProbe.lean"
    sed \
      -e "s|@PROBE_TYPE@|$probe_type|g" \
      -e "s|@RESULT_BITS@|$result_bits|g" \
      "$compile_template" >"$generated_source"
    compile_command=(
      env "LEAN_PATH=$lean_path" "$lean_executable"
      -R "$trial_dir"
      -o "$trial_dir/PerformanceCompileProbe.olean"
      -c "$trial_dir/PerformanceCompileProbe.c"
      "$generated_source"
    )
    if [[ -n "$cpu" ]]; then
      compile_command=(taskset --cpu-list "$cpu" "${compile_command[@]}")
    fi
    start="$(date +%s%N)"
    "${compile_command[@]}"
    stop="$(date +%s%N)"
    echo "$format,$trial,$((stop - start))" >>"$output/raw/compile-nanos.csv"
  done
done

# Verify the generated hot bodies before recording their sizes. Static planners may be retrieved
# through `lean_obj_once`; planner evaluation, thunk forcing, and new indirect calls may not enter
# a measured loop. The two arbitrary-width binary rows retain the current single selected-kernel
# call boundary, while the native-word and Posit32 rows are fully first-order.
python3 - "$output/compile" "$compile_runs" "$output/raw/code-size.csv" <<'PY'
import csv
import re
import sys
from pathlib import Path

compile_root = Path(sys.argv[1])
compile_runs = sys.argv[2]
output = Path(sys.argv[3])
expected_indirect = {
    "binary32": 0,
    "binary64": 0,
    "binary128": 1,
    "posit32": 0,
    "binary256": 1,
}
forbidden = re.compile(
    r"List_foldl|considerCertified|selectCertified|lean_mk_thunk|lean_thunk_get(?:_own)?"
)

def body_for(source: str) -> str:
    signature = re.compile(
        r"^LEAN_EXPORT .*PerformanceCompileProbe_probeAdd\([^;\n]*\)\{", re.MULTILINE
    )
    match = signature.search(source)
    if match is None:
        raise SystemExit("missing generated hot body: probeAdd")
    depth = 0
    entered = False
    for index in range(match.start(), len(source)):
        char = source[index]
        if char == "{":
            entered = True
            depth += 1
        elif char == "}":
            depth -= 1
            if entered and depth == 0:
                return source[match.start() : index + 1]
    raise SystemExit("unterminated generated hot body: probeAdd")

with output.open("w", newline="") as stream:
    writer = csv.writer(stream)
    writer.writerow(["format", "bytes"])
    for format_name, indirect_count in expected_indirect.items():
        source = (
            compile_root / format_name / compile_runs / "PerformanceCompileProbe.c"
        ).read_text()
        body = body_for(source)
        if forbidden.search(body):
            raise SystemExit(f"{format_name} performs planning or thunk work in its hot loop")
        if "lean_obj_once" not in body:
            raise SystemExit(f"{format_name} lost its closed prepared backend")
        actual_indirect = len(re.findall(r"\blean_apply_[0-9]+\b", body))
        if actual_indirect != indirect_count:
            raise SystemExit(
                f"{format_name} indirect-call count changed: "
                f"expected {indirect_count}, found {actual_indirect}"
            )
        writer.writerow([format_name, len(body.encode())])
PY

floatlib_benchmark_lake build execFloatPerformanceRegression
executable="$(floatlib_build_path bin/execFloatPerformanceRegression)"
if [[ ! -x "$executable" ]]; then
  echo "performance-regression executable is missing: $executable" >&2
  exit 1
fi

# One process per trial; the executable reverses formats, operations, and classes on even trials.
# Save complete CSV output so malformed headers, dropped rows, and duplicates cannot be hidden.
for ((trial = 1; trial <= runs; ++trial)); do
  command=(env "PERF_REVERSE=$((1 - trial % 2))" "$executable")
  if [[ -n "$cpu" ]]; then
    command=(taskset --cpu-list "$cpu" "${command[@]}")
  fi
  "${command[@]}" >"$output/raw/runtime-$trial.csv"
done

performance_data summarize "$output" "$baseline_dir" "$mode" "$runs" "$compile_runs"

echo "$output"
