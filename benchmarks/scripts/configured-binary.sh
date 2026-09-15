#!/usr/bin/env bash

set -euo pipefail

export LC_ALL=C

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"
runs="${1:-${BENCH_RUNS:-7}}"
timestamp="$(date -u +%Y-%m-%dT%H%M%SZ)"
output="${2:-${TMPDIR:-/tmp}/floatlib-benchmarks/configured-binary/$timestamp}"
iterations="${BENCH_ITERATIONS:-250000}"
cpu="${CONFIGURED_BINARY_CPU:-}"

if ! [[ "$runs" =~ ^[1-9][0-9]*$ ]]; then
  echo "run count must be a positive integer: $runs" >&2
  exit 2
fi
if ! [[ "$iterations" =~ ^[1-9][0-9]*$ ]]; then
  echo "BENCH_ITERATIONS must be a positive integer: $iterations" >&2
  exit 2
fi
if [[ -n "$cpu" ]] && ! taskset --cpu-list "$cpu" true >/dev/null 2>&1; then
  echo "CONFIGURED_BINARY_CPU is not a valid available CPU list: $cpu" >&2
  exit 2
fi

cd "$root"
bash benchmarks/scripts/checks/configured-binary-codegen.sh
floatlib_benchmark_lake build execFloatConfiguredBinaryBench

mkdir -p "$output/raw" "$output/plots"
lean_executable="$(floatlib_build_path bin/execFloatConfiguredBinaryBench)"
symbol_suffix="FloatLibBenchmarks_Kernels_ConfiguredBinary_"
layout="$output/code-layout.csv"

printf '%s\n' \
  "width,operation,publicAddress,directAddress,sizeBytes,pageAlignmentBytes" >"$layout"
for width in 32 64; do
  for operation in Add Sub Mul Div Sqrt Fma; do
    public_symbol="${symbol_suffix}public${width}${operation}"
    direct_symbol="${symbol_suffix}direct${width}${operation}"
    public_line="$(
      nm -S "$lean_executable" |
        awk -v symbol="$public_symbol" '
          $3 ~ /^[Tt]$/ &&
          length($4) >= length(symbol) &&
          substr($4, length($4) - length(symbol) + 1) == symbol {
            print $1, $2
          }
        '
    )"
    direct_line="$(
      nm -S "$lean_executable" |
        awk -v symbol="$direct_symbol" '
          $3 ~ /^[Tt]$/ &&
          length($4) >= length(symbol) &&
          substr($4, length($4) - length(symbol) + 1) == symbol {
            print $1, $2
          }
        '
    )"
    if [[ -z "$public_line" || -z "$direct_line" ]]; then
      echo "missing configured benchmark symbols for binary${width} ${operation}" >&2
      exit 1
    fi
    read -r public_address public_size <<<"$public_line"
    read -r direct_address direct_size <<<"$direct_line"
    if [[ "$public_size" != "$direct_size" ]]; then
      echo "compiled-size mismatch for binary${width} ${operation}" >&2
      exit 1
    fi
    if [[ "${public_address: -3}" != "000" || "${direct_address: -3}" != "000" ]]; then
      echo "benchmark functions are not 4096-byte aligned for binary${width} ${operation}" >&2
      exit 1
    fi
    operation_label="${operation,,}"
    printf '%s,%s,%s,%s,%s,%s\n' \
      "$width" "$operation_label" "$public_address" "$direct_address" \
      "$public_size" "4096" >>"$layout"
  done
done

for ((trial = 1; trial <= runs; ++trial)); do
  printf -v trial_name "%02d" "$trial"
  raw="$output/raw/trial-$trial_name.csv"
  reverse=$(( (trial + 1) % 2 ))
  echo "configured binary trial $trial/$runs (reverse=$reverse)" >&2
  if [[ -n "$cpu" ]]; then
    BENCH_ITERATIONS="$iterations" \
      BENCH_REVERSE="$reverse" \
      taskset --cpu-list "$cpu" "$lean_executable" >"$raw"
  else
    BENCH_ITERATIONS="$iterations" \
      BENCH_REVERSE="$reverse" \
      "$lean_executable" >"$raw"
  fi
done

python3 benchmarks/plots/configured_binary.py \
  "$output/raw" "$output/plots"

{
  echo "timestampUTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "runs=$runs"
  echo "iterations=$iterations"
  echo "cpuAffinity=${cpu:-unrestricted}"
  echo "lean=$(lean --version | head -n 1)"
  echo "lake=$(lake --version | head -n 1)"
  echo "kernel=$(uname -srmo)"
  echo "cpu=$(sed -n 's/^model name[[:space:]]*: //p' /proc/cpuinfo | head -n 1)"
  sha256sum \
    benchmarks/lean/FloatLibBenchmarks/Kernels/ConfiguredBinary.lean \
    benchmarks/lean/FloatLibBenchmarks/Codegen/ConfiguredBinary.lean \
    FloatLib/Floats/Formats/BinaryInterchange/Configured.lean \
    FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Runtime.lean \
    FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Proof.lean \
    benchmarks/plots/configured_binary.py \
    benchmarks/scripts/configured-binary.sh \
    lakefile.lean \
    benchmarks/scripts/checks/configured-binary-codegen.sh \
    "$lean_executable"
} >"$output/metadata.txt"

echo "$output"
