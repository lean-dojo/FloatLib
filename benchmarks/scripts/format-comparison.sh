#!/usr/bin/env bash

set -euo pipefail

export LC_ALL=C

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"
runs="${1:-${FORMAT_COMPARE_RUNS:-9}}"
timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
output="${2:-${TMPDIR:-/tmp}/floatlib-benchmarks/format-comparison/$timestamp}"
measurement_method="result-dependent-fixture-chain"
minimum_publication_runs=7
minimum_publication_nanos="${FORMAT_COMPARE_MINIMUM_PUBLICATION_NANOS:-50000000}"
warmup_iterations="${FORMAT_COMPARE_WARMUP_ITERATIONS:-256}"
agreement_iterations="${FORMAT_COMPARE_AGREEMENT_ITERATIONS:-256}"
target_nanos="${FORMAT_COMPARE_TARGET_NANOS:-200000000}"
calibrate="${FORMAT_COMPARE_CALIBRATE:-1}"
development_only="${FORMAT_COMPARE_DEVELOPMENT_ONLY:-1}"
skip_build="${FORMAT_COMPARE_SKIP_BUILD:-0}"
profile="${FORMAT_COMPARE_PROFILE:-release}"
case "$profile" in
  release)
    default_flocq=0
    default_other_providers=1
    ;;
  flocq)
    default_flocq=1
    default_other_providers=0
    ;;
  *)
    echo "unsupported FORMAT_COMPARE_PROFILE: $profile (expected release or flocq)" >&2
    exit 2
    ;;
esac
include_flocq="${FORMAT_COMPARE_INCLUDE_FLOCQ:-$default_flocq}"
include_universal="${FORMAT_COMPARE_INCLUDE_UNIVERSAL:-$default_other_providers}"
include_python="${FORMAT_COMPARE_INCLUDE_PYTHON:-$default_other_providers}"
include_softfloat="${FORMAT_COMPARE_INCLUDE_SOFTFLOAT:-$default_other_providers}"
benchmark_cpu="${FORMAT_COMPARE_CPU:-}"
runtime_tmp="${FORMAT_COMPARE_TMPDIR:-${TMPDIR:-/tmp}}"
build_dir="$runtime_tmp/floatlib-format-comparison-${UID:-user}-$timestamp"
benchmark="$(
  printf '%s' \
    "${FORMAT_COMPARE_BINARY:-$(floatlib_build_path bin/execFloatFormatComparison)}"
)"
posit_vectors="$(
  printf '%s' \
    "${FORMAT_COMPARE_POSIT_VECTORS_BINARY:-$(floatlib_build_path bin/execFloatPositVectors)}"
)"
selection_matrix="$(
  printf '%s' \
    "${FORMAT_COMPARE_SELECTION_MATRIX_BINARY:-$(floatlib_build_path bin/execFloatSelectionMatrix)}"
)"
python_benchmark="$root/benchmarks/python/cpython_float.py"
mpfr_benchmark="$build_dir/exact_format_mpfr"
native_benchmark="$build_dir/exact_format_native"
softfloat_benchmark="$build_dir/softfloat_ieee"
flocq_image="${FLOCQ_BENCH_IMAGE:-floatlib-flocq-bench:4.2.2}"
flocq_build_dir="$build_dir/flocq"
flocq_external_binary="${FLOCQ_BENCH_BINARY:-}"
flocq_runner=docker
# We pin the exact Stillwater Universal commit we tested instead of following
# its moving main branch:
# https://github.com/stillwater-sc/universal/commit/26e69f5487b2e592b82002751d900a2437641fad
universal_revision="${UNIVERSAL_REVISION:-26e69f5487b2e592b82002751d900a2437641fad}"
universal_source="${UNIVERSAL_SOURCE:-$build_dir/universal-source}"
universal_repository="${UNIVERSAL_REPOSITORY:-https://github.com/stillwater-sc/universal.git}"
# SoftFloat is the executable IEEE reference distributed alongside TestFloat.
# We build this exact revision from a detached archive, keeping old build
# objects out of a new publication run.
softfloat_revision="${SOFTFLOAT_REVISION:-a0c6494cdc11865811dec815d5c0049fba9d82a8}"
softfloat_repository="${SOFTFLOAT_REPOSITORY:-https://github.com/ucb-bar/berkeley-softfloat-3.git}"
softfloat_source="${SOFTFLOAT_SOURCE:-$build_dir/softfloat-source}"
softfloat_tree="$build_dir/softfloat-tree"

if ! [[ "$runs" =~ ^[1-9][0-9]*$ ]]; then
  echo "run count must be a positive integer: $runs" >&2
  exit 2
fi
for count in \
  "$minimum_publication_nanos" \
  "$warmup_iterations" \
  "$agreement_iterations" \
  "$target_nanos"; do
  if ! [[ "$count" =~ ^[1-9][0-9]*$ ]]; then
    echo "duration and iteration settings must be positive integers: $count" >&2
    exit 2
  fi
done
for flag in \
  "$calibrate" "$development_only" "$skip_build" \
  "$include_flocq" "$include_universal" "$include_python" "$include_softfloat"; do
  if [[ "$flag" != 0 && "$flag" != 1 ]]; then
    echo "format-comparison Boolean flags must be 0 or 1: $flag" >&2
    exit 2
  fi
done
if [[ "$profile" == flocq &&
      ( "$include_flocq" != 1 || "$include_universal" != 0 ||
        "$include_python" != 0 || "$include_softfloat" != 0 ) ]]; then
  echo "the flocq profile requires Flocq enabled and Universal, CPython, and SoftFloat disabled" >&2
  exit 2
fi
if [[ "$development_only" == 0 ]]; then
  # These are positive decimal strings. Compare lengths first to avoid shell overflow.
  if [[ ${#minimum_publication_nanos} -lt 8 ||
      ( ${#minimum_publication_nanos} -eq 8 && "$minimum_publication_nanos" < 50000000 ) ]]; then
    echo "public benchmark runs require FORMAT_COMPARE_MINIMUM_PUBLICATION_NANOS >= 50000000" >&2
    exit 2
  fi
  if [[ ${#target_nanos} -lt ${#minimum_publication_nanos} ||
      ( ${#target_nanos} -eq ${#minimum_publication_nanos} &&
        "$target_nanos" < "$minimum_publication_nanos" ) ]]; then
    echo "public benchmark runs require FORMAT_COMPARE_TARGET_NANOS >= the minimum duration" >&2
    exit 2
  fi
  if ((runs < minimum_publication_runs)); then
    echo \
      "public benchmark runs require at least $minimum_publication_runs trials; " \
      "set FORMAT_COMPARE_DEVELOPMENT_ONLY=1 for a diagnostic run" >&2
    exit 2
  fi
  if [[ "$calibrate" != 1 ]]; then
    echo \
      "public benchmark runs require FORMAT_COMPARE_CALIBRATE=1; " \
      "set FORMAT_COMPARE_DEVELOPMENT_ONLY=1 for an uncalibrated diagnostic" >&2
    exit 2
  fi
  if [[ -n "${FORMAT_COMPARE_ITERATIONS:-}" ]]; then
    echo \
      "public benchmark runs choose iterations by calibration; " \
      "set FORMAT_COMPARE_DEVELOPMENT_ONLY=1 to override them" >&2
    exit 2
  fi
  if [[ "$skip_build" != 0 ]]; then
    echo \
      "public benchmark runs build their executables from the retained source; " \
      "set FORMAT_COMPARE_DEVELOPMENT_ONLY=1 to use FORMAT_COMPARE_SKIP_BUILD=1" \
      >&2
    exit 2
  fi
  if [[ "$agreement_iterations" != 256 ]]; then
    echo \
      "public benchmark runs use the fixed 256-step agreement prefix; " \
      "set FORMAT_COMPARE_DEVELOPMENT_ONLY=1 to change it" >&2
    exit 2
  fi
  if ! [[ "$benchmark_cpu" =~ ^[0-9]+$ ]]; then
    echo \
      "public benchmark runs require one numeric CPU ID in FORMAT_COMPARE_CPU; " \
      "development runs may leave it unset or use a CPU list" >&2
    exit 2
  fi
  if [[ "$profile" == release ]]; then
    for required_lane in \
      include_flocq \
      include_universal \
      include_python \
      include_softfloat; do
      if [[ "${!required_lane}" != 1 ]]; then
        echo "public release benchmark runs require $required_lane=1" >&2
        exit 2
      fi
    done
  fi
  for matrix_override in \
    FORMAT_COMPARE_LANES \
    FORMAT_COMPARE_WIDTHS \
    FORMAT_COMPARE_OPERATIONS; do
    if [[ -n "${!matrix_override:-}" ]]; then
      echo \
        "public benchmark runs use the complete $profile profile matrix and do not accept " \
        "$matrix_override" >&2
      exit 2
    fi
  done
  for override in \
    FORMAT_COMPARE_BINARY \
    FORMAT_COMPARE_POSIT_VECTORS_BINARY \
    FORMAT_COMPARE_SELECTION_MATRIX_BINARY; do
    if [[ -n "${!override:-}" ]]; then
      echo \
        "public benchmark runs do not accept $override; " \
        "set FORMAT_COMPARE_DEVELOPMENT_ONLY=1 for an external executable" >&2
      exit 2
    fi
  done
fi
if [[ -n "$benchmark_cpu" ]]; then
  if ! command -v taskset >/dev/null 2>&1; then
    echo "FORMAT_COMPARE_CPU requires taskset" >&2
    exit 2
  fi
  if ! taskset --cpu-list "$benchmark_cpu" true >/dev/null 2>&1; then
    echo "invalid or unavailable FORMAT_COMPARE_CPU: $benchmark_cpu" >&2
    exit 2
  fi
fi

flocq_cpu_set="$benchmark_cpu"
if [[ "$include_flocq" == 1 && -z "$flocq_external_binary" && -z "$flocq_cpu_set" ]]; then
  # Docker containers are started by the daemon, so pass the client's inherited affinity.
  flocq_cpu_set="$(awk '/^Cpus_allowed_list:/ { print $2 }' /proc/self/status)"
  if [[ -z "$flocq_cpu_set" ]]; then
    echo "cannot determine inherited CPUs for Docker Flocq" >&2
    exit 2
  fi
fi
if [[ "$include_softfloat" == 1 ]]; then
  softfloat_build_jobs="${FORMAT_COMPARE_BUILD_JOBS:-}"
  if [[ -z "$softfloat_build_jobs" ]]; then
    softfloat_build_jobs="$(nproc)"
    affinity_cpus="$(env -u OMP_NUM_THREADS -u OMP_THREAD_LIMIT nproc)"
    if ((softfloat_build_jobs > affinity_cpus)); then
      softfloat_build_jobs="$affinity_cpus"
    fi
  fi
  if ! [[ "$softfloat_build_jobs" =~ ^[1-9][0-9]*$ ]]; then
    echo "FORMAT_COMPARE_BUILD_JOBS must be a positive integer" >&2
    exit 2
  fi
fi

if [[ -e "$output" ]]; then
  echo "output path already exists; choose a new directory: $output" >&2
  exit 2
fi
mkdir -p \
  "$build_dir" \
  "$output/raw/rows" \
  "$output/calibration" \
  "$output/environment" \
  "$output/plots" \
  "$output/resources"

if [[ "$skip_build" == 0 ]]; then
  (
    cd "$root"
    build_targets=(execFloatFormatComparison)
    if [[ "$profile" == release ]]; then
      build_targets+=(execFloatPositVectors)
    fi
    build_targets+=(execFloatSelectionMatrix)
    floatlib_benchmark_lake build "${build_targets[@]}"
  )
fi

validate_measured_row() {
  local row_csv="${1:?row CSV is required}"
  local required_nanos="${2:-0}"
  python3 - "$row_csv" "$measurement_method" "$required_nanos" <<'PY'
import csv
import sys
from pathlib import Path

path = Path(sys.argv[1])
expected_method = sys.argv[2]
minimum_nanos = int(sys.argv[3])
required = {
    "implementation",
    "family",
    "format",
    "totalBits",
    "operation",
    "executionClass",
    "backend",
    "measurementMethod",
    "iterations",
    "totalNanos",
    "sink",
    "fixtureTraceDigest",
    "agreementIterations",
    "agreementSink",
    "agreementFixtureTraceDigest",
}
with path.open(newline="", encoding="utf-8") as stream:
    reader = csv.DictReader(stream)
    header = reader.fieldnames
    if header is None:
        raise SystemExit(f"missing CSV header: {path}")
    if len(header) != len(set(header)):
        raise SystemExit(f"duplicate CSV field in {path}: {header}")
    missing = sorted(required.difference(header))
    if missing:
        raise SystemExit(
            f"retired or incomplete benchmark CSV {path}: missing {missing}"
        )
    rows = list(reader)
if len(rows) != 1:
    raise SystemExit(f"expected one measured row in {path}, found {len(rows)}")
row = rows[0]
if row["measurementMethod"] != expected_method:
    raise SystemExit(
        f"unexpected measurement method in {path}: "
        f"{row['measurementMethod']!r}"
    )
for field in (
    "totalBits",
    "iterations",
    "totalNanos",
    "sink",
    "fixtureTraceDigest",
    "agreementIterations",
    "agreementSink",
    "agreementFixtureTraceDigest",
):
    try:
        int(row[field])
    except ValueError as error:
        raise SystemExit(f"non-integer {field} in {path}: {row[field]!r}") from error

total_nanos = int(row["totalNanos"])
if minimum_nanos and total_nanos < minimum_nanos:
    raise SystemExit(
        f"timed row is too short for public reporting in {path}: "
        f"{total_nanos} ns < {minimum_nanos} ns"
    )
PY
}

if [[ ! -x "$benchmark" ]]; then
  echo "format-comparison executable is missing: $benchmark" >&2
  exit 2
fi
if [[ "$include_universal" == 1 && ! -x "$posit_vectors" ]]; then
  echo "posit-vector executable is missing: $posit_vectors" >&2
  exit 2
fi
if [[ ! -x "$selection_matrix" ]]; then
  echo "backend-selection executable is missing: $selection_matrix" >&2
  exit 2
fi
if [[ "$include_python" == 1 && ! -f "$python_benchmark" ]]; then
  echo "CPython float benchmark is missing: $python_benchmark" >&2
  exit 2
fi

python_has_fma=0
if [[ "$include_python" == 1 ]]; then
  python_has_fma="$(
    python3 -c 'import math; print(1 if hasattr(math, "fma") else 0)'
  )"
fi

cc="${CC:-cc}"
cflags=(-O3 -march=native -std=c11 -Wall -Wextra -Werror)
read -r -a mpfr_flags <<<"$(pkg-config --cflags --libs mpfr)"
"$cc" "${cflags[@]}" \
  "$root/benchmarks/c/exact_format_mpfr.c" \
  "${mpfr_flags[@]}" \
  -o "$mpfr_benchmark"
"$cc" "${cflags[@]}" \
  "$root/benchmarks/c/exact_format_native.c" \
  "${mpfr_flags[@]}" -lm \
  -o "$native_benchmark"

if [[ "$include_softfloat" == 1 ]]; then
  if [[ ! -d "$softfloat_source/.git" ]]; then
    if [[ -n "${SOFTFLOAT_SOURCE:-}" ]]; then
      echo "SOFTFLOAT_SOURCE is not a Git checkout: $softfloat_source" >&2
      exit 2
    fi
    git clone --quiet --filter=blob:none "$softfloat_repository" "$softfloat_source"
  fi
  if ! git -C "$softfloat_source" cat-file -e "$softfloat_revision^{commit}" \
      2>/dev/null; then
    if [[ -n "${SOFTFLOAT_SOURCE:-}" ]]; then
      echo "SOFTFLOAT_SOURCE does not contain revision $softfloat_revision" >&2
      exit 2
    fi
    git -C "$softfloat_source" fetch --quiet origin "$softfloat_revision"
  fi
  softfloat_commit="$(
    git -C "$softfloat_source" rev-parse "$softfloat_revision^{commit}"
  )"
  git -C "$softfloat_source" checkout --quiet --detach "$softfloat_commit"
  if [[ -n "$(
      git -C "$softfloat_source" status \
        --porcelain=v1 --untracked-files=all --ignored=matching
    )" ]]; then
    echo "SOFTFLOAT_SOURCE must be completely clean: $softfloat_source" >&2
    exit 2
  fi
  mkdir -p "$softfloat_tree"
  git -C "$softfloat_source" archive "$softfloat_commit" |
    tar -x -C "$softfloat_tree"
  make -C "$softfloat_tree/build/Linux-x86_64-GCC" \
    -j "$softfloat_build_jobs" softfloat.a >/dev/null
  "$cc" "${cflags[@]}" \
    "-I$softfloat_tree/source/include" \
    "$root/benchmarks/c/softfloat_ieee.c" \
    "$softfloat_tree/build/Linux-x86_64-GCC/softfloat.a" \
    "${mpfr_flags[@]}" -lm \
    -o "$softfloat_benchmark"
fi

if [[ "$include_flocq" == 1 ]]; then
  mkdir -p "$flocq_build_dir"
  if [[ -n "$flocq_external_binary" ]]; then
    if [[ ! -x "$flocq_external_binary" ]]; then
      echo "FLOCQ_BENCH_BINARY is not executable: $flocq_external_binary" >&2
      exit 2
    fi
    cp "$flocq_external_binary" "$flocq_build_dir/flocq_format_bench"
    flocq_runner=external-binary
  else
    if ! command -v docker >/dev/null 2>&1; then
      echo \
        "FORMAT_COMPARE_INCLUDE_FLOCQ=1 requires Docker or FLOCQ_BENCH_BINARY" \
        >&2
      exit 2
    fi
    if ! docker image inspect "$flocq_image" >/dev/null 2>&1; then
      docker build \
        --tag "$flocq_image" \
        "$root/benchmarks/rocq" >/dev/null
    fi
    docker run --rm \
      --cpuset-cpus "$flocq_cpu_set" \
      --user "$(id -u):$(id -g)" \
      --env HOME=/home/coq \
      --volume "$root/benchmarks/rocq:/src:ro" \
      --volume "$flocq_build_dir:/build" \
      --workdir /build \
      "$flocq_image" \
      sh -lc '
        cp /src/FlocqKernel.v .
        cp /src/flocq_format_bench.ml .
        cp /src/monotonic_clock.c .
        opam exec -- coqc FlocqKernel.v
        opam exec -- ocamlfind ocamlopt \
          -O3 -linkpkg -package zarith,unix \
          monotonic_clock.c flocq_kernel.mli flocq_kernel.ml \
          flocq_format_bench.ml -cclib -lrt \
          -o flocq_format_bench
      '
  fi
  # Each campaign starts empty; the wrapper memoizes the real agreement prefix.
  flocq_cache_dir="$(cd "$flocq_build_dir" && pwd)/agreement-cache"
  mkdir "$flocq_cache_dir"
  flocq_binary_sha256="$(sha256sum "$flocq_build_dir/flocq_format_bench" | awk '{print $1}')"
fi

if [[ "$profile" == flocq ]]; then
  # BinarySingleNaN.Prec_lt_emax requires prec < emax; widths 4, 5 and 7 fail it.
  widths=(6 8 16 32 64 128 256 512 1024 2048 4096)
  lanes=(binary-software mpfr-reference)
else
  widths=(2 3 4 5 6 7 8 16 32 64 128 256 512 1024 2048 4096)
  lanes=(posit-software binary-software binary-native-c mpfr-reference)
fi
operations=(add sub mul div sqrt fma)
if [[ "$include_softfloat" == 1 ]]; then
  lanes+=(softfloat-reference)
fi
if [[ "$include_python" == 1 ]]; then
  lanes+=(cpython-float64)
fi
if [[ "$include_universal" == 1 ]]; then
  lanes+=(universal-posit)
fi
if [[ "$include_flocq" == 1 ]]; then
  lanes+=(flocq-reference)
fi
if [[ -n "${FORMAT_COMPARE_LANES:-}" ]]; then
  read -r -a requested_lanes <<<"$FORMAT_COMPARE_LANES"
  lanes=()
  for lane in "${requested_lanes[@]}"; do
    case "$lane" in
      posit-software|binary-software|binary-native-c|mpfr-reference)
        ;;
      softfloat-reference)
        if [[ "$include_softfloat" != 1 ]]; then
          echo "FORMAT_COMPARE_LANES requests SoftFloat while it is disabled" >&2
          exit 2
        fi
        ;;
      cpython-float64)
        if [[ "$include_python" != 1 ]]; then
          echo "FORMAT_COMPARE_LANES requests CPython while it is disabled" >&2
          exit 2
        fi
        ;;
      universal-posit)
        if [[ "$include_universal" != 1 ]]; then
          echo "FORMAT_COMPARE_LANES requests Universal while it is disabled" >&2
          exit 2
        fi
        ;;
      flocq-reference)
        if [[ "$include_flocq" != 1 ]]; then
          echo "FORMAT_COMPARE_LANES requests Flocq while it is disabled" >&2
          exit 2
        fi
        ;;
      *)
        echo "unsupported FORMAT_COMPARE_LANES entry: $lane" >&2
        exit 2
        ;;
    esac
    lanes+=("$lane")
  done
  if [[ "${#lanes[@]}" == 0 ]]; then
    echo "FORMAT_COMPARE_LANES must name at least one lane" >&2
    exit 2
  fi
fi
if [[ -n "${FORMAT_COMPARE_WIDTHS:-}" ]]; then
  read -r -a widths <<<"$FORMAT_COMPARE_WIDTHS"
fi
if [[ -n "${FORMAT_COMPARE_OPERATIONS:-}" ]]; then
  read -r -a operations <<<"$FORMAT_COMPARE_OPERATIONS"
fi

for width in "${widths[@]}"; do
  if [[ "$profile" == flocq ]]; then
    case "$width" in
      6|8|16|32|64|128|256|512|1024|2048|4096) ;;
      *)
        echo "the flocq profile requires a supported binary width with prec < emax: $width" >&2
        exit 2
        ;;
    esac
  fi
  case "$width" in
    2|3|4|5|6|7|8|16|24|32|48|64|96|112|128|256|512|1024|2048|4096)
      ;;
    *)
      echo "unsupported comparison width: $width" >&2
      exit 2
      ;;
  esac
done
for operation in "${operations[@]}"; do
  if [[ "$operation" != add && "$operation" != sub &&
        "$operation" != mul && "$operation" != div &&
        "$operation" != sqrt && "$operation" != fma ]]; then
    echo "unsupported comparison operation: $operation" >&2
    exit 2
  fi
done

binary_only_width() {
  case "${1:?width is required}" in
    24|48|96|112) return 0 ;;
    *) return 1 ;;
  esac
}

declare -A universal_available
if [[ "$include_universal" == 1 ]]; then
  if [[ ! -d "$universal_source/.git" ]]; then
    if [[ -n "${UNIVERSAL_SOURCE:-}" ]]; then
      echo "UNIVERSAL_SOURCE is not a Git checkout: $universal_source" >&2
      exit 2
    fi
    git clone --quiet --filter=blob:none "$universal_repository" "$universal_source"
  fi
  if ! git -C "$universal_source" cat-file -e "$universal_revision^{commit}" \
      2>/dev/null; then
    if [[ -n "${UNIVERSAL_SOURCE:-}" ]]; then
      echo "UNIVERSAL_SOURCE does not contain revision $universal_revision" >&2
      exit 2
    fi
    git -C "$universal_source" fetch --quiet origin "$universal_revision"
  fi
  universal_commit="$(git -C "$universal_source" rev-parse "$universal_revision^{commit}")"
  if [[ -n "${UNIVERSAL_SOURCE:-}" ]]; then
    if [[ "$(git -C "$universal_source" rev-parse HEAD)" != "$universal_commit" ]]; then
      echo "UNIVERSAL_SOURCE must be checked out at $universal_commit" >&2
      exit 2
    fi
  else
    git -C "$universal_source" checkout --quiet --detach "$universal_commit"
    # `/tmp` cleaners can remove an old checkout's ordinary files while leaving its hidden
    # `.git` directory. Re-materialize the pinned tree because this cache is owned entirely by
    # the harness; never mutate a caller-supplied `UNIVERSAL_SOURCE`.
    git -C "$universal_source" restore \
      --quiet \
      --source="$universal_commit" \
      --worktree \
      -- .
  fi
  if [[ -n "$(
      git -C "$universal_source" status \
        --porcelain=v1 --untracked-files=all --ignored=matching
    )" ]]; then
    echo "UNIVERSAL_SOURCE must be completely clean: $universal_source" >&2
    exit 2
  fi
  universal_header="$universal_source/include/sw/universal/number/posit/posit.hpp"
  if [[ ! -f "$universal_header" ]]; then
    echo "pinned Universal checkout is missing $universal_header" >&2
    exit 2
  fi

  cxx="${CXX:-c++}"
  cxx_standard=-std=c++20
  if ! "$cxx" "$cxx_standard" -include concepts -x c++ -fsyntax-only /dev/null \
      2>/dev/null; then
    cxx_standard=-std=c++2a
    if ! "$cxx" "$cxx_standard" -include concepts -x c++ -fsyntax-only /dev/null \
        2>/dev/null; then
      echo "Stillwater Universal requires a compiler with C++20 support" >&2
      exit 2
    fi
  fi
  universal_cxxflags=(-O3 -march=native "$cxx_standard" -Wall -Wextra -Werror)
  printf '%s\n' \
    "library,totalBits,operation,status,diagnosticFile" \
    >"$output/environment/external-posit-conformance.csv"
  for width in "${widths[@]}"; do
    # Universal's generic es=2 FMA requires at least five encoded bits.
    if ((width < 5)) || binary_only_width "$width"; then
      continue
    fi
    vector_file="$build_dir/posit-vectors-$width.csv"
    env "POSIT_VECTOR_WIDTH=$width" "$posit_vectors" >"$vector_file"
    universal_binary="$build_dir/universal-posit-$width"
    "$cxx" "${universal_cxxflags[@]}" \
      "-DFLOATLIB_POSIT_WIDTH=$width" \
      "-DFLOATLIB_UNIVERSAL_REVISION=\"$universal_commit\"" \
      "-I$universal_source/include/sw" \
      "$root/benchmarks/cpp/universal_posit.cpp" \
      -o "$universal_binary"
    for operation in "${operations[@]}"; do
      diagnostic="$output/environment/universal-$width-$operation.txt"
      if env \
          "FORMAT_COMPARE_WIDTH=$width" \
          "FORMAT_COMPARE_OPERATION=$operation" \
          "FORMAT_COMPARE_WARMUP_ITERATIONS=1" \
          "FORMAT_COMPARE_ITERATIONS=1" \
          "POSIT_VECTOR_FILE=$vector_file" \
          "$universal_binary" >/dev/null 2>"$diagnostic"; then
        universal_available["$width:$operation"]=1
        status=pass
      else
        universal_available["$width:$operation"]=0
        status=reject
      fi
      printf 'Stillwater Universal,%s,%s,%s,%s\n' \
        "$width" "$operation" "$status" "$(basename "$diagnostic")" \
        >>"$output/environment/external-posit-conformance.csv"
    done
  done
fi

lane_available() {
  local lane="${1:?lane is required}"
  local width="${2:?width is required}"
  local operation="${3:?operation is required}"
  # Optional widths exist only as configured binary rows.
  if binary_only_width "$width" && [[ "$lane" != binary-software ]]; then
    return 1
  fi
  case "$lane" in
    posit-software)
      ((width >= 2))
      ;;
    binary-software)
      ((width >= 4))
      ;;
    binary-native-c)
      [[ "$width" == 32 || "$width" == 64 ]]
      ;;
    softfloat-reference)
      [[ "$width" == 32 || "$width" == 64 ]]
      ;;
    cpython-float64)
      [[ "$width" == 64 && ("$operation" != fma || "$python_has_fma" == 1) ]]
      ;;
    universal-posit)
      ((width >= 5)) &&
        [[ "${universal_available["$width:$operation"]:-0}" == 1 ]]
      ;;
    mpfr-reference)
      ((width >= 4))
      ;;
    flocq-reference)
      # The certified BinarySingleNaN API requires prec < emax.
      ((width >= 4)) && [[ "$width" != 4 && "$width" != 5 && "$width" != 7 ]]
      ;;
    *)
      return 0
      ;;
  esac
}

run_lane() {
  local lane="${1:?lane is required}"
  local width="${2:?width is required}"
  local operation="${3:?operation is required}"
  local iterations="${4:-}"
  local resource_trial="${5:-}"
  local command=()

  case "$lane" in
    posit-software)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        "FORMAT_COMPARE_FAMILY=posit"
        "FORMAT_COMPARE_EXECUTION_CLASS=proved-software"
        "$benchmark"
      )
      ;;
    binary-software)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        "FORMAT_COMPARE_FAMILY=binary-interchange"
        "FORMAT_COMPARE_EXECUTION_CLASS=proved-software"
        "$benchmark"
      )
      ;;
    binary-native-c)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        "$native_benchmark"
      )
      ;;
    mpfr-reference)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        "$mpfr_benchmark"
      )
      ;;
    softfloat-reference)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        "$softfloat_benchmark"
      )
      ;;
    cpython-float64)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        python3
        "$python_benchmark"
      )
      ;;
    universal-posit)
      command=(
        env
        "FORMAT_COMPARE_WIDTH=$width"
        "FORMAT_COMPARE_OPERATION=$operation"
        "FORMAT_COMPARE_WARMUP_ITERATIONS=$warmup_iterations"
        "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
        ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
        "POSIT_VECTOR_FILE=$build_dir/posit-vectors-$width.csv"
        "$build_dir/universal-posit-$width"
      )
      ;;
    flocq-reference)
      if [[ "$(sha256sum "$flocq_build_dir/flocq_format_bench" | awk '{print $1}')" != "$flocq_binary_sha256" ]]; then
        echo "Flocq executable changed after its agreement cache was initialized" >&2
        exit 1
      fi
      local flocq_warmup_iterations="$warmup_iterations"
      local flocq_warmup_cap
      if ((width <= 128)); then
        flocq_warmup_cap=64
      elif ((width <= 512)); then
        flocq_warmup_cap=16
      elif ((width <= 1024)); then
        flocq_warmup_cap=4
      else
        flocq_warmup_cap=1
      fi
      if ((flocq_warmup_iterations > flocq_warmup_cap)); then
        flocq_warmup_iterations="$flocq_warmup_cap"
      fi
      if [[ "$flocq_runner" == external-binary ]]; then
        command=(
          env
          "FORMAT_COMPARE_WIDTH=$width"
          "FORMAT_COMPARE_OPERATION=$operation"
          "FORMAT_COMPARE_WARMUP_ITERATIONS=$flocq_warmup_iterations"
          "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
          "FORMAT_COMPARE_FLOCQ_CACHE=$flocq_cache_dir"
          "FORMAT_COMPARE_FLOCQ_BINARY_SHA256=$flocq_binary_sha256"
          ${iterations:+"FORMAT_COMPARE_ITERATIONS=$iterations"}
          "$flocq_build_dir/flocq_format_bench"
        )
      else
        command=(
          docker run --rm
          --cpuset-cpus "$flocq_cpu_set"
          --user "$(id -u):$(id -g)"
          --env HOME=/home/coq
          --volume "$flocq_build_dir:/build:ro"
          --volume "$flocq_cache_dir:/build/agreement-cache:rw"
          --workdir /build
          --env "FORMAT_COMPARE_WIDTH=$width"
          --env "FORMAT_COMPARE_OPERATION=$operation"
          --env "FORMAT_COMPARE_WARMUP_ITERATIONS=$flocq_warmup_iterations"
          --env "FORMAT_COMPARE_AGREEMENT_ITERATIONS=$agreement_iterations"
          --env "FORMAT_COMPARE_FLOCQ_CACHE=/build/agreement-cache"
          --env "FORMAT_COMPARE_FLOCQ_BINARY_SHA256=$flocq_binary_sha256"
        )
        if [[ -n "$iterations" ]]; then
          command+=(--env "FORMAT_COMPARE_ITERATIONS=$iterations")
        fi
        command+=(
          "$flocq_image"
          sh -lc "opam exec -- ./flocq_format_bench"
        )
      fi
      ;;
    *)
      echo "unknown comparison lane: $lane" >&2
      exit 2
      ;;
  esac

  if [[ -n "$benchmark_cpu" ]]; then
    command=(taskset --cpu-list "$benchmark_cpu" "${command[@]}")
  fi
  if [[ -n "$resource_trial" ]]; then
    /usr/bin/time \
      -q \
      -a \
      -o "$output/resources/process.csv" \
      -f "$resource_trial,$lane,$width,$operation,%M,%F,%R,%U,%S,%e,%x" \
      "${command[@]}"
  else
    "${command[@]}"
  fi
}

date -u +%Y-%m-%dT%H:%M:%SZ >"$output/environment/start-time-utc.txt"
lscpu >"$output/environment/lscpu.txt"
cp /proc/loadavg "$output/environment/loadavg-before.txt"
"$selection_matrix" >"$output/environment/backend-selection.csv"
if [[ -r /etc/os-release ]]; then
  cp /etc/os-release "$output/environment/os-release.txt"
fi
printf '%s\n' \
  "trial,lane,totalBits,operation,maxResidentSetKiB,majorPageFaults,minorPageFaults,userSeconds,systemSeconds,elapsedSeconds,exitStatus" \
  >"$output/resources/process.csv"

declare -A selected_iterations
if [[ -n "${FORMAT_COMPARE_ITERATIONS:-}" ]]; then
  calibrate=0
  for width in "${widths[@]}"; do
    for operation in "${operations[@]}"; do
      for lane in "${lanes[@]}"; do
        if lane_available "$lane" "$width" "$operation"; then
          selected_iterations["$lane:$width:$operation"]="$FORMAT_COMPARE_ITERATIONS"
        fi
      done
    done
  done
fi

printf '%s\n' \
  "lane,totalBits,operation,pilotIterations,pilotNanos,targetNanos,selectedIterations,pilotSink" \
  >"$output/calibration/selected-iterations.csv"
if [[ "$calibrate" == 1 ]]; then
  echo "calibrating every format-comparison lane to ${target_nanos} ns" >&2
  for width in "${widths[@]}"; do
    for operation in "${operations[@]}"; do
      for lane in "${lanes[@]}"; do
        if ! lane_available "$lane" "$width" "$operation"; then
          continue
        fi
        pilot="$output/calibration/pilot-${lane}-${width}-${operation}.csv"
        run_lane "$lane" "$width" "$operation" "" "" >"$pilot"
        if [[ "$(wc -l <"$pilot")" != 2 ]]; then
          echo "expected exactly one pilot row for $lane $width $operation" >&2
          exit 1
        fi
        validate_measured_row "$pilot" 0
        IFS=, read -r pilot_iterations pilot_nanos pilot_sink < <(
          python3 - "$pilot" <<'PY'
import csv
import sys

with open(sys.argv[1], newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream))
if len(rows) != 1:
    raise SystemExit(f"expected one row in {sys.argv[1]}")
row = rows[0]
print(row["iterations"], row["totalNanos"], row["sink"], sep=",")
PY
        )
        if ! [[ "$pilot_iterations" =~ ^[1-9][0-9]*$ &&
                "$pilot_nanos" =~ ^[1-9][0-9]*$ ]]; then
          echo "invalid pilot timing for $lane $width $operation" >&2
          exit 1
        fi
        iterations="$(
          python3 - "$target_nanos" "$pilot_iterations" "$pilot_nanos" <<'PY'
import math
import sys

target, iterations, elapsed = map(int, sys.argv[1:])
selected = math.ceil(target * iterations / elapsed)
print(max(1, min(selected, 50_000_000)))
PY
        )"
        selected_iterations["$lane:$width:$operation"]="$iterations"
        printf '%s,%s,%s,%s,%s,%s,%s,%s\n' \
          "$lane" "$width" "$operation" "$pilot_iterations" "$pilot_nanos" \
          "$target_nanos" "$iterations" "$pilot_sink" \
          >>"$output/calibration/selected-iterations.csv"
      done
    done
  done
fi

rows=()
for width in "${widths[@]}"; do
  for operation in "${operations[@]}"; do
    for lane in "${lanes[@]}"; do
      if lane_available "$lane" "$width" "$operation"; then
        rows+=("$lane:$width:$operation")
      fi
    done
  done
done

mapfile -t scheduled_rows < <(
  printf '%s\n' "${rows[@]}" |
    python3 -c '
import random
import sys

rows = [line.strip() for line in sys.stdin if line.strip()]
random.Random(20260911).shuffle(rows)
print(*rows, sep="\n")
'
)
if ((${#scheduled_rows[@]} == 0)); then
  echo "the requested benchmark matrix contains no runnable cells" >&2
  exit 2
fi
requested_matrix="$output/environment/requested-matrix.csv"
{
  printf '%s\n' "lane,totalBits,operation"
  for row in "${rows[@]}"; do
    printf '%s\n' "${row//:/,}"
  done
} >"$requested_matrix"
printf '%s\n' "trial,orderIndex,lane,totalBits,operation" \
  >"$output/environment/trial-order.csv"

required_row_nanos=0
if [[ "$development_only" == 0 ]]; then
  required_row_nanos="$minimum_publication_nanos"
fi

for ((trial = 1; trial <= runs; ++trial)); do
  printf -v trial_name "%02d" "$trial"
  echo "format comparison trial $trial/$runs" >&2
  trial_csv="$output/raw/trial-$trial_name.csv"
  first_row=1

  ordered_rows=()
  row_count="${#scheduled_rows[@]}"
  start_index=$(((trial - 1) * row_count / runs))
  for ((order_index = 0; order_index < row_count; ++order_index)); do
    scheduled_index=$(((start_index + order_index) % row_count))
    row="${scheduled_rows[$scheduled_index]}"
    ordered_rows+=("$row")
    IFS=: read -r scheduled_lane scheduled_width scheduled_operation <<<"$row"
    printf '%s,%s,%s,%s,%s\n' \
      "$trial_name" "$order_index" "$scheduled_lane" \
      "$scheduled_width" "$scheduled_operation" \
      >>"$output/environment/trial-order.csv"
  done

  for row in "${ordered_rows[@]}"; do
    IFS=: read -r lane width operation <<<"$row"
    key="$lane:$width:$operation"
    iterations="${selected_iterations[$key]:-}"
    row_csv="$output/raw/rows/trial-${trial_name}-${lane}-${width}-${operation}.csv"
    run_lane "$lane" "$width" "$operation" "$iterations" "$trial_name" \
      >"$row_csv"
    if [[ "$(wc -l <"$row_csv")" != 2 ]]; then
      echo "expected one measured row for $lane $width $operation" >&2
      exit 1
    fi
    validate_measured_row "$row_csv" "$required_row_nanos"
    if [[ "$first_row" == 1 ]]; then
      cp "$row_csv" "$trial_csv"
      first_row=0
    else
      tail -n 1 "$row_csv" >>"$trial_csv"
    fi
  done
done

# Publication checks require the full binary grid independently of emitted rows.
agreement_grid=()
if [[ "$development_only" == 0 ]]; then
  agreement_grid=(--widths)
  for width in "${widths[@]}"; do
    if ((width >= 4)); then
      agreement_grid+=("$width")
    fi
  done
fi
agreement_softfloat=0
agreement_python=0
agreement_flocq=0
for lane in "${lanes[@]}"; do
  case "$lane" in
    softfloat-reference) agreement_softfloat=1 ;;
    cpython-float64) agreement_python=1 ;;
    flocq-reference) agreement_flocq=1 ;;
  esac
done
python3 "$root/benchmarks/scripts/verify_binary_agreement.py" \
  "$output/raw" \
  "$output/environment/binary-agreement.txt" \
  --softfloat "$agreement_softfloat" \
  --python "$agreement_python" \
  --python-has-fma "$python_has_fma" \
  --flocq "$agreement_flocq" \
  --trials "$runs" \
  --agreement-iterations "$agreement_iterations" \
  --operations "${operations[@]}" \
  --requested-matrix "$requested_matrix" \
  "${agreement_grid[@]}"

date -u +%Y-%m-%dT%H:%M:%SZ >"$output/environment/finish-time-utc.txt"
cp /proc/loadavg "$output/environment/loadavg-after.txt"

export MPLCONFIGDIR="$build_dir/matplotlib"
mkdir -p "$MPLCONFIGDIR"
python3 "$root/benchmarks/plots/format_comparison.py" \
  "$output/raw" "$output/plots"

{
  echo "timestampUTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "runs=$runs"
  echo "profile=$profile"
  echo "measurementMethod=$measurement_method"
  echo "minimumPublicationTrials=$minimum_publication_runs"
  echo "minimumPublicationNanos=$minimum_publication_nanos"
  echo "developmentOnly=$development_only"
  if [[ "$development_only" == 0 ]]; then
    echo "publicationReadiness=eligible"
  else
    echo "publicationReadiness=development-only"
  fi
  echo "widths=${widths[*]}"
  echo "operations=${operations[*]}"
  echo "lanes=${lanes[*]}"
  echo "warmupIterations=$warmup_iterations"
  echo "agreementIterations=$agreement_iterations"
  echo "iterationsOverride=${FORMAT_COMPARE_ITERATIONS:-adaptive}"
  echo "calibratedRows=$calibrate"
  echo "targetMeasuredNanos=$target_nanos"
  echo "benchmarkCPU=${benchmark_cpu:-unpinned}"
  echo "leanBenchmark=$benchmark"
  echo "selectionMatrix=$selection_matrix"
  echo "mpfrBenchmark=$mpfr_benchmark"
  echo "nativeBenchmark=$native_benchmark"
  echo "includeSoftFloat=$include_softfloat"
  if [[ "$include_softfloat" == 1 ]]; then
    echo "softfloatRepository=$softfloat_repository"
    echo "softfloatCommit=$softfloat_commit"
    echo "softfloatLicense=BSD-3-Clause"
    echo "softfloatBenchmark=$softfloat_benchmark"
    echo "softfloatBuildJobs=$softfloat_build_jobs"
  fi
  echo "includePython=$include_python"
  if [[ "$include_python" == 1 ]]; then
    echo "pythonBenchmark=$python_benchmark"
    echo "pythonVersion=$(python3 --version 2>&1)"
    echo "pythonImplementation=$(
      python3 -c 'import platform; print(platform.python_implementation())'
    )"
    echo "pythonFloatMantissaBits=$(
      python3 -c 'import sys; print(sys.float_info.mant_dig)'
    )"
    echo "pythonFloatObjectBytes=$(
      python3 -c 'import sys; print(sys.getsizeof(0.0))'
    )"
    echo "pythonHasMathFma=$python_has_fma"
    echo "pythonBenchmarkSha256=$(sha256sum "$python_benchmark" | awk '{print $1}')"
  fi
  echo "plotBrand=FloatLib"
  echo "compiler=$("$cc" --version | head -n 1)"
  echo "cflags=${cflags[*]}"
  echo "mpfr=$(pkg-config --modversion mpfr)"
  echo "includeFlocq=$include_flocq"
  if [[ "$include_flocq" == 1 ]]; then
    echo "flocqImage=$flocq_image"
    echo "flocqVersion=4.2.2"
    echo "flocqExtraction=OCaml Zarith"
    echo "flocqUnsupportedWidths=4 5 7"
    echo "flocqWidthConstraint=prec < emax (BinarySingleNaN.Prec_lt_emax)"
    echo "flocqRunner=$flocq_runner"
    echo "flocqAgreementCacheMode=fresh-campaign-shared-prefix"
    echo "flocqAgreementCacheBinarySha256=$flocq_binary_sha256"
    echo "flocqAgreementCacheKey=compiledBinarySha256,totalBits,precision,emax,operation,agreementIterations"
    echo "flocqAgreementPrefixComputation=once per executable/format/operation; shared by calibration and trials"
    if [[ "$flocq_runner" == external-binary ]]; then
      echo "flocqSuppliedBinary=$flocq_external_binary"
      echo "flocqSuppliedBinarySha256=$(
        sha256sum "$flocq_external_binary" | awk '{print $1}'
      )"
    fi
  fi
  echo "includeUniversal=$include_universal"
  if [[ "$include_universal" == 1 ]]; then
    echo "universalRepository=$universal_repository"
    echo "universalCommit=$universal_commit"
    echo "universalLicense=MIT"
    echo "universalCompiler=$("$cxx" --version | head -n 1)"
    echo "universalCxxFlags=${universal_cxxflags[*]}"
    echo "universalConformanceSha256=$(
      sha256sum "$output/environment/external-posit-conformance.csv" |
        awk '{print $1}'
    )"
    echo "universalBinariesSha256=$(
      sha256sum "$build_dir"/universal-posit-* |
        sha256sum | awk '{print $1}'
    )"
    echo "positVectorsSha256=$(
      sha256sum "$build_dir"/posit-vectors-*.csv |
        sha256sum | awk '{print $1}'
    )"
  fi
  echo "leanVersion=$(cd "$root" && floatlib_benchmark_lake env lean --version | head -n 1)"
  echo "matplotlibVersion=$(python3 -c 'import matplotlib; print(matplotlib.__version__)')"
  echo "uname=$(uname -a)"
  echo "cpuCount=$(getconf _NPROCESSORS_ONLN)"
  echo "leanBenchmarkBytes=$(stat -c %s "$benchmark")"
  echo "selectionMatrixBytes=$(stat -c %s "$selection_matrix")"
  echo "mpfrBenchmarkBytes=$(stat -c %s "$mpfr_benchmark")"
  echo "nativeBenchmarkBytes=$(stat -c %s "$native_benchmark")"
  echo "benchmarkBinarySha256=$(sha256sum "$benchmark" | awk '{print $1}')"
  echo "selectionMatrixBinarySha256=$(
    sha256sum "$selection_matrix" | awk '{print $1}'
  )"
  echo "selectionMatrixCsvSha256=$(
    sha256sum "$output/environment/backend-selection.csv" | awk '{print $1}'
  )"
  echo "mpfrBinarySha256=$(sha256sum "$mpfr_benchmark" | awk '{print $1}')"
  echo "nativeBinarySha256=$(sha256sum "$native_benchmark" | awk '{print $1}')"
  if [[ "$include_softfloat" == 1 ]]; then
    echo "softfloatBenchmarkBytes=$(stat -c %s "$softfloat_benchmark")"
    echo "softfloatBinarySha256=$(
      sha256sum "$softfloat_benchmark" | awk '{print $1}'
    )"
  fi
  if [[ "$include_flocq" == 1 ]]; then
    echo "flocqBenchmarkBytes=$(stat -c %s "$flocq_build_dir/flocq_format_bench")"
    echo "flocqBenchmarkSha256=$(
      sha256sum "$flocq_build_dir/flocq_format_bench" | awk '{print $1}'
    )"
  fi
  if git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "gitCommit=$(git -C "$root" rev-parse HEAD)"
    echo "gitDirtyFiles=$(git -C "$root" status --short | wc -l)"
  fi
  if git -C "$root/.lake/packages/mathlib" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "mathlibCommit=$(git -C "$root/.lake/packages/mathlib" rev-parse HEAD)"
  fi
  source_tree_hash="$(
    cd "$root"
    # We want this provenance hash to work in the same minimal image that runs
    # the timings. `find`, `sort`, and `sha256sum` are runner dependencies;
    # developer conveniences such as `rg` are not.
    {
      find FloatLib -type f -print0
      printf '%s\0' lakefile.lean lean-toolchain lake-manifest.json
    } | sort -zu | xargs -0 sha256sum | sha256sum | awk '{print $1}'
  )"
  echo "leanSourceAndBuildConfigHash=$source_tree_hash"
  for generated_c in \
    "$FLOATLIB_BUILD_DIR/ir/FloatLib/Floats/Formats/Posit/Configured/Plan/Dispatch.c" \
    "$FLOATLIB_BUILD_DIR/ir/FloatLibBenchmarks/Public/FormatComparison.c"; do
    if [[ -f "$generated_c" ]]; then
      relative="${generated_c#"$FLOATLIB_BUILD_DIR/ir/"}"
      echo "generatedCBytes[$relative]=$(stat -c %s "$generated_c")"
      echo "generatedCSha256[$relative]=$(sha256sum "$generated_c" | awk '{print $1}')"
    fi
  done
  echo "rawDataSha256=$(python3 - "$output/raw" <<'PY'
import hashlib
import sys
from pathlib import Path

root = Path(sys.argv[1])
digest = hashlib.sha256()
for path in sorted(candidate for candidate in root.rglob("*") if candidate.is_file()):
    digest.update(path.relative_to(root).as_posix().encode("utf-8"))
    digest.update(b"\0")
    digest.update(path.read_bytes())
    digest.update(b"\0")
print(digest.hexdigest())
PY
)"
  (
    cd "$root"
    sha256sum \
      benchmarks/lean/FloatLibBenchmarks/Support/ExactWorkload.lean \
      benchmarks/lean/FloatLibBenchmarks/Public/FormatComparison.lean \
      benchmarks/lean/FloatLibBenchmarks/Public/SelectionMatrix.lean \
      benchmarks/lean/FloatLibBenchmarks/Public/PositVectors.lean \
      benchmarks/c/exact_format_mpfr.c \
      benchmarks/c/exact_format_native.c \
      benchmarks/c/softfloat_ieee.c \
      benchmarks/c/benchmark_mpfr_protocol.h \
      benchmarks/c/benchmark_protocol.h \
      benchmarks/cpp/universal_posit.cpp \
      benchmarks/python/cpython_float.py \
      benchmarks/plots/format_comparison.py \
      benchmarks/scripts/format-comparison.sh \
      benchmarks/scripts/verify_binary_agreement.py \
      tests/oracles/write_result_manifest.py
    if [[ "$include_flocq" == 1 ]]; then
      sha256sum \
        benchmarks/rocq/Dockerfile \
        benchmarks/rocq/FlocqKernel.v \
        benchmarks/rocq/flocq_format_bench.ml \
        benchmarks/rocq/monotonic_clock.c
    fi
  )
} >"$output/metadata.txt"

python3 "$root/tests/oracles/write_result_manifest.py" "$output"

echo "$output"
