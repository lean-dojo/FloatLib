#!/usr/bin/env bash

set -euo pipefail

export LC_ALL=C

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"
runs="${1:-${BENCH_RUNS:-9}}"
timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
output="${2:-${TMPDIR:-/tmp}/floatlib-benchmarks/posit/$timestamp}"
allocation_profile="${POSIT_BENCH_ALLOCPROF:-0}"
isolate_rows="${POSIT_BENCH_ISOLATE_ROWS:-0}"
cold_iterations="${POSIT_BENCH_COLD_ITERATIONS:-1}"
warmup_iterations="${POSIT_BENCH_WARMUP_ITERATIONS:-256}"
benchmark_cpu="${POSIT_BENCH_CPU:-}"
calibrate_rows="${POSIT_BENCH_CALIBRATE:-1}"
target_nanos="${POSIT_BENCH_TARGET_NANOS:-200000000}"
benchmark_override="${POSIT_BENCH_BINARY:-}"
skip_build="${POSIT_BENCH_SKIP_BUILD:-0}"
runtime_tmp="${POSIT_BENCH_TMPDIR:-${TMPDIR:-/tmp}}"
cache_root="${POSIT_BENCH_CACHE_DIR:-$runtime_tmp/floatlib-posit-benchmark-cache}"
row_csv=""
resource_csv=""

declare -A calibrated_iterations

cleanup() {
  if [[ -n "$row_csv" && -f "$row_csv" ]]; then
    rm -f "$row_csv"
  fi
}
trap cleanup EXIT

if ! [[ "$runs" =~ ^[1-9][0-9]*$ ]]; then
  echo "run count must be a positive integer: $runs" >&2
  exit 2
fi
if [[ "$allocation_profile" != 0 && "$allocation_profile" != 1 ]]; then
  echo "POSIT_BENCH_ALLOCPROF must be 0 or 1: $allocation_profile" >&2
  exit 2
fi
if [[ "$isolate_rows" != 0 && "$isolate_rows" != 1 ]]; then
  echo "POSIT_BENCH_ISOLATE_ROWS must be 0 or 1: $isolate_rows" >&2
  exit 2
fi
if [[ "$calibrate_rows" != 0 && "$calibrate_rows" != 1 ]]; then
  echo "POSIT_BENCH_CALIBRATE must be 0 or 1: $calibrate_rows" >&2
  exit 2
fi
if [[ "$skip_build" != 0 && "$skip_build" != 1 ]]; then
  echo "POSIT_BENCH_SKIP_BUILD must be 0 or 1: $skip_build" >&2
  exit 2
fi
if ! [[ "$target_nanos" =~ ^[1-9][0-9]*$ ]]; then
  echo "POSIT_BENCH_TARGET_NANOS must be a positive integer: $target_nanos" >&2
  exit 2
fi
for count in "$cold_iterations" "$warmup_iterations"; do
  if ! [[ "$count" =~ ^[1-9][0-9]*$ ]]; then
    echo "cold and warmup counts must be positive integers: $count" >&2
    exit 2
  fi
done
if [[ -n "$benchmark_cpu" ]]; then
  if ! command -v taskset >/dev/null 2>&1; then
    echo "POSIT_BENCH_CPU requires taskset" >&2
    exit 2
  fi
  if ! taskset --cpu-list "$benchmark_cpu" true >/dev/null 2>&1; then
    echo "invalid or unavailable POSIT_BENCH_CPU: $benchmark_cpu" >&2
    exit 2
  fi
fi

mkdir -p \
  "$output/raw" \
  "$output/plots" \
  "$output/alloc" \
  "$output/calibration" \
  "$output/environment" \
  "$output/resources" \
  "$cache_root/xdg" \
  "$cache_root/matplotlib"

export TMPDIR="$runtime_tmp"
export XDG_CACHE_HOME="$cache_root/xdg"
export MPLCONFIGDIR="$cache_root/matplotlib"

if [[ -n "$benchmark_override" ]]; then
  benchmark="$benchmark_override"
elif [[ "$skip_build" == 0 ]]; then
  (
    cd "$root"
    floatlib_benchmark_lake build execFloatPositBench
  )
  benchmark="$(floatlib_build_path bin/execFloatPositBench)"
else
  benchmark="$(floatlib_build_path bin/execFloatPositBench)"
fi
if [[ ! -x "$benchmark" ]]; then
  echo "posit benchmark executable is missing or not executable: $benchmark" >&2
  exit 2
fi

resource_csv="$output/resources/process.csv"
printf '%s\n' \
  "trial,totalBits,operation,maxResidentSetKiB,majorPageFaults,minorPageFaults,userSeconds,systemSeconds,elapsedSeconds,exitStatus" \
  >"$resource_csv"
widths=(2 3 4 5 6 7 8 16 32 64 128 256 512 1024 2048 4096)
operations=(add sub mul div sqrt fma)
if [[ -n "${POSIT_BENCH_WIDTH:-}" ]]; then
  widths=("$POSIT_BENCH_WIDTH")
fi
if [[ -n "${POSIT_BENCH_OPERATION:-}" ]]; then
  operations=("$POSIT_BENCH_OPERATION")
fi

run_benchmark() {
  local trial="${1:?trial label is required}"
  local width="${2:-}"
  local operation="${3:-}"
  local iteration_override="${4:-}"
  local record_resources="${5:-1}"
  local profile_override="${6:-$allocation_profile}"
  local iteration_map="${7:-}"
  local reverse_traversal="${8:-0}"
  local resource_width="${width:-all}"
  local resource_operation="${operation:-all}"
  local command=(
    env
    "POSIT_BENCH_ALLOCPROF=$profile_override"
    "POSIT_BENCH_COLD_ITERATIONS=$cold_iterations"
    "POSIT_BENCH_WARMUP_ITERATIONS=$warmup_iterations"
    "POSIT_BENCH_REVERSE=$reverse_traversal"
  )
  if [[ -n "$iteration_override" ]]; then
    command+=("POSIT_BENCH_ITERATIONS=$iteration_override")
  fi
  if [[ -n "$width" ]]; then
    command+=("POSIT_BENCH_WIDTH=$width")
  fi
  if [[ -n "$operation" ]]; then
    command+=("POSIT_BENCH_OPERATION=$operation")
  fi
  if [[ -n "$iteration_map" ]]; then
    command+=("POSIT_BENCH_ITERATION_MAP=$iteration_map")
  fi
  if [[ -n "$benchmark_cpu" ]]; then
    command+=(taskset --cpu-list "$benchmark_cpu")
  fi
  command+=("$benchmark")
  if [[ "$record_resources" == 1 ]]; then
    /usr/bin/time \
      -q \
      -a \
      -o "$resource_csv" \
      -f "$trial,$resource_width,$resource_operation,%M,%F,%R,%U,%S,%e,%x" \
      "${command[@]}"
  else
    "${command[@]}"
  fi
}

date -u +%Y-%m-%dT%H:%M:%SZ >"$output/environment/start-time-utc.txt"
lscpu >"$output/environment/lscpu.txt"
cp /proc/loadavg "$output/environment/loadavg-before.txt"
if [[ -r /etc/os-release ]]; then
  cp /etc/os-release "$output/environment/os-release.txt"
fi
if command -v taskset >/dev/null 2>&1; then
  taskset -pc "$$" >"$output/environment/driver-affinity.txt"
fi

if [[ -n "${POSIT_BENCH_ITERATIONS:-}" ]]; then
  calibrate_rows=0
fi

calibration_csv="$output/calibration/selected-iterations.csv"
printf '%s\n' \
  "totalBits,operation,pilotIterations,pilotNanos,targetNanos,selectedIterations,pilotSink" \
  >"$calibration_csv"
if [[ "$calibrate_rows" == 1 ]]; then
  echo "calibrating posit benchmark rows to ${target_nanos} ns" >&2
  calibration_log="$output/alloc/calibration.log"
  : >"$calibration_log"
  for width in "${widths[@]}"; do
    for operation in "${operations[@]}"; do
      pilot_csv="$output/calibration/pilot-${width}-${operation}.csv"
      run_benchmark "calibration" "$width" "$operation" "" 0 0 \
        >"$pilot_csv" 2>>"$calibration_log"
      if [[ "$(wc -l <"$pilot_csv")" != 2 ]]; then
        echo "expected exactly one calibration row for posit${width} ${operation}" >&2
        exit 1
      fi
      IFS=, read -r \
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ \
        pilot_iterations pilot_nanos pilot_sink \
        < <(tail -n 1 "$pilot_csv")
      if ! [[ "$pilot_iterations" =~ ^[1-9][0-9]*$ &&
              "$pilot_nanos" =~ ^[1-9][0-9]*$ ]]; then
        echo "invalid calibration timing for posit${width} ${operation}" >&2
        exit 1
      fi
      selected_iterations="$(
        python3 - "$target_nanos" "$pilot_iterations" "$pilot_nanos" <<'PY'
import math
import sys

target, iterations, elapsed = map(int, sys.argv[1:])
selected = math.ceil(target * iterations / elapsed)
print(max(1, min(selected, 50_000_000)))
PY
      )"
      calibrated_iterations["$width:$operation"]="$selected_iterations"
      printf '%s,%s,%s,%s,%s,%s,%s\n' \
        "$width" "$operation" "$pilot_iterations" "$pilot_nanos" \
        "$target_nanos" "$selected_iterations" "$pilot_sink" \
        >>"$calibration_csv"
    done
  done
elif [[ -n "${POSIT_BENCH_ITERATIONS:-}" ]]; then
  for width in "${widths[@]}"; do
    for operation in "${operations[@]}"; do
      calibrated_iterations["$width:$operation"]="$POSIT_BENCH_ITERATIONS"
    done
  done
fi

iteration_map=""
iteration_map_entries=0
for width in "${widths[@]}"; do
  for operation in "${operations[@]}"; do
    calibration_key="$width:$operation"
    iteration_override="${calibrated_iterations[$calibration_key]:-}"
    if [[ -n "$iteration_override" ]]; then
      if [[ -n "$iteration_map" ]]; then
        iteration_map+=";"
      fi
      iteration_map+="$width:$operation:$iteration_override"
      ((iteration_map_entries += 1))
    fi
  done
done

for ((trial = 1; trial <= runs; ++trial)); do
  printf -v trial_name "%02d" "$trial"
  echo "posit benchmark trial $trial/$runs" >&2
  allocation_log="$output/alloc/trial-$trial_name.log"
  trial_csv="$output/raw/trial-$trial_name.csv"
  : >"$allocation_log"
  if [[ "$isolate_rows" == 0 ]]; then
    reverse_traversal=0
    if ((trial % 2 == 0)); then
      reverse_traversal=1
    fi
    run_benchmark "$trial_name" "" "" "${POSIT_BENCH_ITERATIONS:-}" \
      1 "$allocation_profile" "$iteration_map" "$reverse_traversal" \
      >"$trial_csv" 2>"$allocation_log"
    continue
  fi

  # Each row gets a fresh process. Alternating traversal order prevents every width from always
  # occupying the same thermal position in a trial while retaining deterministic raw data.
  trial_widths=("${widths[@]}")
  trial_operations=("${operations[@]}")
  if ((trial % 2 == 0)); then
    trial_widths=()
    trial_operations=()
    for ((index = ${#widths[@]} - 1; index >= 0; --index)); do
      trial_widths+=("${widths[$index]}")
    done
    for ((index = ${#operations[@]} - 1; index >= 0; --index)); do
      trial_operations+=("${operations[$index]}")
    done
  fi

  row_csv="$output/raw/.trial-$trial_name-row.csv"
  first_row=1
  for width in "${trial_widths[@]}"; do
    for operation in "${trial_operations[@]}"; do
      calibration_key="$width:$operation"
      iteration_override="${calibrated_iterations[$calibration_key]:-${POSIT_BENCH_ITERATIONS:-}}"
      run_benchmark "$trial_name" "$width" "$operation" "$iteration_override" \
        >"$row_csv" 2>>"$allocation_log"
      if [[ "$(wc -l <"$row_csv")" != 2 ]]; then
        echo "expected exactly one benchmark row for posit${width} ${operation}" >&2
        exit 1
      fi
      if [[ "$first_row" == 1 ]]; then
        cp "$row_csv" "$trial_csv"
        first_row=0
      else
        tail -n 1 "$row_csv" >>"$trial_csv"
      fi
    done
  done
  rm -f "$row_csv"
done

date -u +%Y-%m-%dT%H:%M:%SZ >"$output/environment/finish-time-utc.txt"
cp /proc/loadavg "$output/environment/loadavg-after.txt"

allocation_status="not-requested"
if [[ "$allocation_profile" == 1 ]]; then
  if rg -q \
      'Allocation profiling data is not available' \
      "$output/alloc"; then
    allocation_status="unavailable-runtime-not-built-with-RUNTIME_STATS"
  elif rg -q '[Aa]llocat' "$output/alloc"; then
    allocation_status="reports-present"
  else
    allocation_status="requested-but-no-recognized-report"
  fi
fi
{
  echo "status=$allocation_status"
  echo "scope=Lean runtime allocations in the separately repeated measured workload"
  echo "processMemory=$output/resources/process.csv records whole-process peak RSS, not allocation"
  if [[ "$allocation_status" == "unavailable-runtime-not-built-with-RUNTIME_STATS" ]]; then
    echo "requirement=Rebuild Lean with -D RUNTIME_STATS=ON for allocation counters"
  fi
} >"$output/alloc/status.txt"

plot_args=()
if [[ -n "${POSIT_NAMED_FORMAT_SUMMARY:-}" ]]; then
  plot_args+=(--named-format-summary "$POSIT_NAMED_FORMAT_SUMMARY")
fi
if [[ -n "${POSIT_EXTERNAL_SUMMARY:-}" ]]; then
  plot_args+=(--external-summary "$POSIT_EXTERNAL_SUMMARY")
fi

python3 "$root/benchmarks/plots/posit.py" \
  "$output/raw" "$output/plots" "${plot_args[@]}"

{
  echo "timestampUTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "runs=$runs"
  echo "iterationsOverride=${POSIT_BENCH_ITERATIONS:-adaptive}"
  echo "iterationMapEntries=$iteration_map_entries"
  echo "iterationMapTransport=width:operation:iterations entries parsed once before timing"
  echo "coldIterations=$cold_iterations"
  echo "warmupIterations=$warmup_iterations"
  echo "isolatedRows=$isolate_rows"
  echo "calibratedRows=$calibrate_rows"
  echo "calibrationExecution=fresh isolated process per selected width and operation"
  echo "steadyTraversal=$(
    if [[ "$isolate_rows" == 0 ]]; then
      echo "one process per trial, alternating forward and reverse width/operation order"
    else
      echo "one process per row, alternating forward and reverse width/operation order"
    fi
  )"
  echo "targetMeasuredNanos=$target_nanos"
  echo "benchmarkCPU=${benchmark_cpu:-unpinned}"
  echo "benchmarkPath=$benchmark"
  echo "benchmarkOverride=${benchmark_override:-none}"
  echo "skipBuild=$skip_build"
  echo "runtimeTmp=$runtime_tmp"
  echo "cacheRoot=$cache_root"
  echo "allocationProfile=$allocation_profile"
  echo "allocationStatus=$allocation_status"
  echo "processResourceMeasurement=GNU time 1.9 whole-process counters"
  echo "timingBoundary=cold operation timing begins after Lean runtime initialization and filter parsing"
  echo "namedFormatSummary=${POSIT_NAMED_FORMAT_SUMMARY:-none}"
  echo "externalSummary=${POSIT_EXTERNAL_SUMMARY:-none}"
  echo "uname=$(uname -a)"
  echo "cpuCount=$(getconf _NPROCESSORS_ONLN)"
  echo "cpuModel=$(lscpu | awk -F: '$1 == "Model name" {sub(/^[[:space:]]+/, "", $2); print $2}')"
  echo "cpuArchitecture=$(lscpu | awk -F: '$1 == "Architecture" {sub(/^[[:space:]]+/, "", $2); print $2}')"
  echo "numaNodes=$(lscpu | awk -F: '$1 == "NUMA node(s)" {sub(/^[[:space:]]+/, "", $2); print $2}')"
  if command -v taskset >/dev/null 2>&1; then
    echo "driverAffinity=$(taskset -pc "$$" | sed 's/^[^:]*: //')"
  else
    echo "driverAffinity=taskset-unavailable"
  fi
  echo "scalingGovernors=$(
    for governor in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
      [[ -r "$governor" ]] && cat "$governor"
    done | sort -u | paste -sd,
  )"
  if [[ -r /sys/devices/system/cpu/intel_pstate/no_turbo ]]; then
    echo "intelPstateNoTurbo=$(cat /sys/devices/system/cpu/intel_pstate/no_turbo)"
  fi
  if [[ -r /sys/devices/system/cpu/cpufreq/boost ]]; then
    echo "cpuFrequencyBoost=$(cat /sys/devices/system/cpu/cpufreq/boost)"
  fi
  echo "leanVersion=$(cd "$root" && floatlib_benchmark_lake env lean --version | head -n 1)"
  echo "pythonVersion=$(python3 --version)"
  echo "matplotlibVersion=$(python3 -c 'import matplotlib; print(matplotlib.__version__)')"
  echo "cCompiler=$(${CC:-cc} --version | head -n 1)"
  echo "benchmarkBinarySha256=$(sha256sum "$benchmark" | awk '{print $1}')"
  if git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "gitCommit=$(git -C "$root" rev-parse HEAD)"
    echo "gitDirtyFiles=$(git -C "$root" status --short | wc -l)"
  fi
  if git -C "$root/.lake/packages/mathlib" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "mathlibCommit=$(git -C "$root/.lake/packages/mathlib" rev-parse HEAD)"
  fi
  source_tree_hash="$(
    cd "$root"
    # Keep provenance reproducible in the minimal evaluator image. The runner
    # guarantees these standard file tools, whereas `rg` is only a developer
    # convenience and may not be installed on a benchmark node.
    {
      find FloatLib -type f -name '*.lean' -print0
      printf '%s\0' \
        lakefile.lean \
        lean-toolchain \
        lake-manifest.json \
        benchmarks/plots/posit.py \
        benchmarks/scripts/posit.sh
    } | sort -zu |
      xargs -0 sha256sum |
      sha256sum |
      awk '{print $1}'
  )"
  echo "leanSourceAndBenchmarkTreeHash=$source_tree_hash"
  for generated in \
    "$FLOATLIB_BUILD_DIR/ir/FloatLib/Floats/Formats/Posit/Configured/Core.c" \
    "$FLOATLIB_BUILD_DIR/ir/FloatLib/Floats/Formats/Posit/Configured/Backend.c" \
    "$FLOATLIB_BUILD_DIR/ir/FloatLib/Floats/Formats/Posit/Configured/Plan.c" \
    "$FLOATLIB_BUILD_DIR/ir/FloatLib/Floats/Formats/Posit/Configured/Plan/Dispatch.c" \
    "$FLOATLIB_BUILD_DIR/ir/FloatLibBenchmarks/Public/Posit.c"; do
    if [[ -f "$generated" ]]; then
      relative="${generated#"$FLOATLIB_BUILD_DIR/ir/"}"
      echo "generatedCBytes[$relative]=$(stat -c %s "$generated")"
      echo "generatedCSha256[$relative]=$(sha256sum "$generated" | awk '{print $1}')"
    fi
  done
  echo "rawDataSha256=$(
    cd "$output/raw"
    sha256sum trial-*.csv | sha256sum | awk '{print $1}'
  )"
  (
    cd "$root"
    sha256sum \
      benchmarks/lean/FloatLibBenchmarks/Public/Posit.lean \
      benchmarks/plots/posit.py \
      benchmarks/scripts/posit.sh
  )
} >"$output/metadata.txt"

echo "$output"
