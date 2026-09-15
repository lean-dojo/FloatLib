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

usage() {
  echo "usage: $0 [check|record] [new-output-directory]"
  echo "  record writes baseline.csv and environment.env for review"
  echo "  check requires PERF_BASELINE_DIR pointing to a reviewed baseline directory"
}
if [[ "$#" -eq 1 && ("$mode" == --help || "$mode" == -h) ]]; then
  usage
  exit 0
fi
if [[ "$#" -gt 2 || ("$mode" != check && "$mode" != record) ]]; then
  usage >&2
  exit 2
fi
for count in "$runs" "$compile_runs"; do
  if ! [[ "$count" =~ ^[1-9][0-9]*$ ]]; then
    echo "trial counts must be positive integers: $count" >&2
    exit 2
  fi
done
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
if [[ -e "$output" || -L "$output" ]]; then
  echo "output path already exists; choose a new directory: $output" >&2
  exit 2
fi

# The same parser validates a selected baseline before compilation and reads it for comparison.
performance_data() {
  python3 - "$@" <<'PY'
import csv
import math
import statistics
import sys
from pathlib import Path

FORMATS = {"binary32": 32, "binary64": 64, "binary128": 128, "posit32": 32, "binary256": 256}
BUDGETS = {
    "compile-nanos": 1.30,
    "generated-c-body-bytes": 1.15,
    "runtime-nanos-per-add": 1.35,
}
BASELINE_HEADER = ["metric", "subject", "baseline", "maxRatio"]
ENVIRONMENT_KEYS = {
    "lean", "ccCommand", "ccPath", "cc", "arch", "cpu", "cpuCount", "cpuAffinity",
}


def read_rows(path, header):
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, strict=True)
        if reader.fieldnames != header:
            raise ValueError(f"{path}: expected CSV header {header}")
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


def positive_integer(text, context):
    value = int(text)
    if value <= 0:
        raise ValueError(f"{context}: expected a positive integer, got {text!r}")
    return value


def read_baseline(directory):
    path = directory / "baseline.csv"
    baseline = {}
    for row in read_rows(path, BASELINE_HEADER):
        key = row["metric"], row["subject"]
        if key in baseline:
            raise ValueError(f"{path}: duplicate metric {key}")
        reference = positive_number(row["baseline"], f"{path}: {key} baseline")
        budget = positive_number(row["maxRatio"], f"{path}: {key} maxRatio")
        if not math.isfinite(reference * budget):
            raise ValueError(f"{path}: {key} budget product is not finite")
        baseline[key] = reference, budget
    expected = {(metric, name) for metric in BUDGETS for name in FORMATS}
    if baseline.keys() != expected:
        raise ValueError(
            f"{path}: baseline metric mismatch; "
            f"missing={sorted(expected - baseline.keys())}, "
            f"extra={sorted(baseline.keys() - expected)}"
        )
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


def measurements(output, runs, compile_runs):
    rows = []
    path = output / "raw/compile-nanos.csv"
    compile_samples = {name: {} for name in FORMATS}
    for row in read_rows(path, ["format", "trial", "nanos"]):
        name = row["format"]
        trial = positive_integer(row["trial"], str(path))
        if name not in FORMATS or trial > compile_runs or trial in compile_samples[name]:
            raise ValueError(f"{path}: unexpected or duplicate compile trial {name}, {trial}")
        compile_samples[name][trial] = positive_integer(row["nanos"], str(path))
    for name, samples in compile_samples.items():
        if len(samples) != compile_runs:
            raise ValueError(f"{path}: {name} expected {compile_runs} compile trials")
        rows.append(("compile-nanos", name, statistics.median(samples.values())))

    path = output / "raw/code-size.csv"
    sizes = {}
    for row in read_rows(path, ["format", "bytes"]):
        name = row["format"]
        if name not in FORMATS or name in sizes:
            raise ValueError(f"{path}: unexpected or duplicate code-size row {name}")
        sizes[name] = positive_integer(row["bytes"], str(path))
    if sizes.keys() != FORMATS.keys():
        raise ValueError(f"{path}: missing code-size rows")
    rows.extend(("generated-c-body-bytes", name, sizes[name]) for name in FORMATS)

    path = output / "raw/runtime.csv"
    runtime = {name: [] for name in FORMATS}
    header = ["format", "totalBits", "backend", "iterations", "totalNanos", "sink"]
    for row in read_rows(path, header):
        name = row["format"]
        if name not in FORMATS or int(row["totalBits"]) != FORMATS[name]:
            raise ValueError(f"{path}: unexpected runtime format or width {name}")
        if not 0 <= int(row["sink"]) < 2**64:
            raise ValueError(f"{path}: invalid result sink")
        positive_integer(row["iterations"], str(path))
        positive_integer(row["totalNanos"], str(path))
        runtime[name].append(row)
    for name, samples in runtime.items():
        if len(samples) != runs:
            raise ValueError(f"{path}: {name} expected {runs} runtime rows, got {len(samples)}")
        identities = {
            (row["totalBits"], row["backend"], row["iterations"], row["sink"])
            for row in samples
        }
        if len(identities) != 1:
            raise ValueError(f"{path}: {name} runtime identity changed between trials")
        times = [int(row["totalNanos"]) / int(row["iterations"]) for row in samples]
        rows.append(("runtime-nanos-per-add", name, statistics.median(times)))
    for metric, name, value in rows:
        positive_number(value, f"{metric}, {name}")
    return rows


def main():
    action = sys.argv[1]
    if action == "validate":
        directory = Path(sys.argv[2])
        read_baseline(directory)
        validate_environment(directory)
        return

    output = Path(sys.argv[2])
    baseline_dir = Path(sys.argv[3])
    mode = sys.argv[4]
    rows = measurements(output, int(sys.argv[5]), int(sys.argv[6]))
    if mode == "record":
        path = output / "baseline.csv"
        with path.open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(BASELINE_HEADER)
            writer.writerows(
                (metric, name, value, BUDGETS[metric]) for metric, name, value in rows
            )
        read_baseline(output)
        validate_environment(output)
        print(f"baseline for review: {path}")
        print(f"baseline environment: {output / 'environment.env'}")
        print("Review both files before selecting this directory with PERF_BASELINE_DIR.")
        return

    baseline = read_baseline(baseline_dir)
    with (output / "measurements.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["metric", "subject", "value"])
        writer.writerows(rows)
    failed = False
    print("metric,subject,current,baseline,maxAllowed,ratio,status")
    for metric, name, value in rows:
        reference, budget = baseline[metric, name]
        maximum = reference * budget
        status = "pass" if value <= maximum else "FAIL"
        failed |= status == "FAIL"
        print(
            f"{metric},{name},{value:.3f},{reference:.3f},"
            f"{maximum:.3f},{value / reference:.3f},{status}"
        )
    raise SystemExit(1 if failed else 0)


try:
    main()
except (OSError, ValueError, OverflowError, csv.Error) as error:
    raise SystemExit(f"performance data: {error}")
PY
}

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
compiler="${CC:-cc}"

cd "$root"
floatlib_benchmark_lake build FloatLibBenchmarks.Public.PerformanceRegression
lean_path="$(floatlib_benchmark_lake env printenv LEAN_PATH | tail -n 1)"
lean_executable="$(floatlib_benchmark_lake env which lean | tail -n 1)"
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
  echo "lean=$($lean_executable --version | head -n 1)"
  echo "ccCommand=$compiler"
  echo "ccPath=$compiler_executable"
  echo "cc=$($compiler_executable --version | head -n 1)"
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

declare -A iterations=(
  [binary32]=1000000
  [binary64]=1000000
  [binary128]=100000
  [posit32]=500000
  [binary256]=50000
)
printf '%s\n' "format,totalBits,backend,iterations,totalNanos,sink" \
  >"$output/raw/runtime.csv"
for ((trial = 1; trial <= runs; ++trial)); do
  order=("${formats[@]}")
  if ((trial % 2 == 0)); then
    order=(binary256 posit32 binary128 binary64 binary32)
  fi
  for format in "${order[@]}"; do
    command=(env "PERF_FORMAT=$format" "PERF_ITERATIONS=${iterations[$format]}" "$executable")
    if [[ -n "$cpu" ]]; then
      command=(taskset --cpu-list "$cpu" "${command[@]}")
    fi
    "${command[@]}" | tail -n 1 >>"$output/raw/runtime.csv"
  done
done

performance_data summarize "$output" "$baseline_dir" "$mode" "$runs" "$compile_runs"

echo "$output"
