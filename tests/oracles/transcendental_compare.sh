#!/usr/bin/env bash

# Bounded FloatLib transcendental comparisons against MPFR and optional public libm providers.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

usage() {
  cat <<'EOF'
usage: tests/oracles/transcendental_compare.sh [OPTIONS]

Options:
  --output-dir DIR       Result directory (default: a fresh /tmp directory)
  --random-count N       Random cases per format, 0..256 (default: 32)
  --jobs N               Parallel jobs for optional external builds (default: 8)
  --core-math-root DIR   Build the 14 relevant CORE-MATH source files
  --core-math-lib FILE   Use an existing CORE-MATH shared library
  --openlibm-root DIR    Build OpenLibm with its Makefile
  --openlibm-lib FILE    Use an existing OpenLibm shared library
  --rlibm-root DIR       Build RLIBM's supported binary32 functions
  --rlibm-lib FILE       Use an existing RLIBM shared library
  -h, --help             Show this help

The *_ROOT options may also be supplied as CORE_MATH_ROOT, OPENLIBM_ROOT, and
RLIBM_ROOT environment variables. Library options take precedence over roots.
EOF
}

output_dir=""
random_count=32
jobs="${JOBS:-8}"
core_math_root="${CORE_MATH_ROOT:-}"
core_math_lib=""
openlibm_root="${OPENLIBM_ROOT:-}"
openlibm_lib=""
rlibm_root="${RLIBM_ROOT:-}"
rlibm_lib=""

while (($# > 0)); do
  case "$1" in
    --output-dir)
      output_dir="${2:?--output-dir requires a value}"
      shift 2
      ;;
    --random-count)
      random_count="${2:?--random-count requires a value}"
      shift 2
      ;;
    --jobs)
      jobs="${2:?--jobs requires a value}"
      shift 2
      ;;
    --core-math-root)
      core_math_root="${2:?--core-math-root requires a value}"
      shift 2
      ;;
    --core-math-lib)
      core_math_lib="${2:?--core-math-lib requires a value}"
      shift 2
      ;;
    --openlibm-root)
      openlibm_root="${2:?--openlibm-root requires a value}"
      shift 2
      ;;
    --openlibm-lib)
      openlibm_lib="${2:?--openlibm-lib requires a value}"
      shift 2
      ;;
    --rlibm-root)
      rlibm_root="${2:?--rlibm-root requires a value}"
      shift 2
      ;;
    --rlibm-lib)
      rlibm_lib="${2:?--rlibm-lib requires a value}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      printf 'unknown option: %s\n' "$1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ ! "$random_count" =~ ^[0-9]+$ ]] || ((random_count > 256)); then
  printf '%s\n' '--random-count must be an integer from 0 through 256' >&2
  exit 2
fi
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  printf '%s\n' '--jobs must be a positive integer' >&2
  exit 2
fi
if ! command -v pkg-config >/dev/null 2>&1 ||
    ! pkg-config --atleast-version=4.1.0 mpfr; then
  printf '%s\n' 'MPFR 4.1.0 or newer is required.' >&2
  exit 1
fi

cc="${CC:-cc}"
if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'C compiler not found: %s\n' "$cc" >&2
  exit 1
fi
cxx="${CXX:-c++}"
if [[ -n "$rlibm_root" ]] && ! command -v "$cxx" >/dev/null 2>&1; then
  printf 'C++ compiler not found: %s\n' "$cxx" >&2
  exit 1
fi

build_dir="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-transcendentals-build.XXXXXX")"
trap 'rm -rf "$build_dir"' EXIT
if [[ -z "$output_dir" ]]; then
  output_dir="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-transcendentals-results.XXXXXX")"
else
  mkdir -p "$output_dir"
  output_dir="$(cd "$output_dir" && pwd)"
fi

read -r -a mpfr_cflags <<<"$(pkg-config --cflags mpfr)"
read -r -a mpfr_libs <<<"$(pkg-config --libs mpfr)"
mpfr_oracle="$build_dir/transcendental_mpfr"
"$cc" -O2 -std=c11 -Wall -Wextra -Werror \
  "${mpfr_cflags[@]}" "$root/tests/oracles/transcendental_mpfr.c" \
  "${mpfr_libs[@]}" -o "$mpfr_oracle"

python3 -B "$root/tests/oracles/transcendental_test.py"

vectors="$output_dir/vectors.tsv"
references="$output_dir/mpfr.tsv"
mpfr_log="$output_dir/mpfr.stderr.log"
floatlib_acquire_build_lock
if (
  cd "$root/tests"
  lake -f "$root/tests/oracles/Transcendental/lakefile.lean" \
    --packages="$root/tests/lake-manifest.json" \
    -R -KbuildDir="$FLOATLIB_BUILD_DIR" \
    exe transcendentalEmitter "$random_count"
) >"$vectors"; then
  emitter_status=0
else
  emitter_status=$?
fi
floatlib_release_build_lock
if ((emitter_status != 0)); then
  exit "$emitter_status"
fi
"$mpfr_oracle" <"$vectors" >"$references" 2>"$mpfr_log"

count_rows() {
  awk 'NF && substr($0, 1, 1) != "#" { count += 1 } END { print count + 0 }' "$1"
}

expected_cases=$((7 * (37 + random_count + 38 + random_count)))
vector_cases="$(count_rows "$vectors")"
reference_cases="$(count_rows "$references")"
if ((vector_cases != expected_cases || reference_cases != expected_cases)); then
  printf 'incomplete transcendental corpus: vectors=%s references=%s expected=%s\n' \
    "$vector_cases" "$reference_cases" "$expected_cases" >&2
  exit 1
fi

if [[ -z "$core_math_lib" && -n "$core_math_root" ]]; then
  core_math_root="$(cd "$core_math_root" && pwd)"
  core_math_lib="$build_dir/libcoremath-transcendentals.so"
  core_sources=()
  for operation in exp log sin cos sinh cosh tanh; do
    core_sources+=(
      "$core_math_root/src/binary32/$operation/${operation}f.c"
      "$core_math_root/src/binary64/$operation/$operation.c"
    )
  done
  for source in "${core_sources[@]}"; do
    if [[ ! -f "$source" ]]; then
      printf 'missing CORE-MATH source: %s\n' "$source" >&2
      exit 1
    fi
  done
  printf '%s\n' 'Building the selected CORE-MATH functions...' >&2
  "$cc" -O3 -std=gnu11 -fPIC -shared "${core_sources[@]}" -lm \
    -o "$core_math_lib"
fi

if [[ -z "$openlibm_lib" && -n "$openlibm_root" ]]; then
  openlibm_root="$(cd "$openlibm_root" && pwd)"
  printf 'Building OpenLibm with %s jobs...\n' "$jobs" >&2
  make --no-print-directory -s -C "$openlibm_root" -j "$jobs"
  openlibm_lib="$openlibm_root/libopenlibm.so"
fi

if [[ -z "$rlibm_lib" && -n "$rlibm_root" ]]; then
  rlibm_root="$(cd "$rlibm_root" && pwd)"
  rlibm_lib="$build_dir/librlibm-transcendentals.so"
  printf '%s\n' 'Building RLIBM binary32 exp/log/sinh/cosh...' >&2
  # RLIBM deliberately divides by zero to produce a domain-error NaN in log.
  # Its public-looking functions have C++ linkage in the pinned source tree;
  # the small bridge gives the Python reporter stable, unmangled entry points.
  "$cxx" -O3 -std=c++17 -Wno-div-by-zero -fPIC -shared \
    -I"$rlibm_root/include" \
    "$rlibm_root/source/float/exp.cpp" \
    "$rlibm_root/source/float/log.cpp" \
    "$rlibm_root/source/float/sinh.cpp" \
    "$rlibm_root/source/float/cosh.cpp" \
    "$root/tests/oracles/rlibm_bridge.cpp" \
    -lm -o "$rlibm_lib"
fi

providers_dir="$output_dir/providers"
mkdir -p "$providers_dir"
archive_provider() {
  local name=$1
  local source=$2
  local destination="$providers_dir/$name.so"
  if [[ ! -f "$source" ]]; then
    printf 'provider library not found: %s\n' "$source" >&2
    exit 1
  fi
  cp -f "$source" "$destination"
  printf '%s\n' "$destination"
}

if [[ -n "$core_math_lib" ]]; then
  core_math_lib="$(archive_provider core-math "$core_math_lib")"
fi
if [[ -n "$openlibm_lib" ]]; then
  openlibm_lib="$(archive_provider openlibm "$openlibm_lib")"
fi
if [[ -n "$rlibm_lib" ]]; then
  rlibm_lib="$(archive_provider rlibm "$rlibm_lib")"
fi

git_revision() {
  local directory=$1
  if [[ -n "$directory" ]] &&
      git -C "$directory" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$directory" rev-parse HEAD
  else
    printf '%s\n' 'not-recorded'
  fi
}

provenance="$output_dir/provenance.tsv"
{
  printf 'floatlib_revision\t%s\n' "$(git_revision "$root")"
  if git -C "$root" diff --quiet --ignore-submodules -- &&
      [[ -z "$(git -C "$root" status --porcelain --untracked-files=normal)" ]]; then
    printf '%s\n' $'floatlib_worktree\tclean'
  else
    printf '%s\n' $'floatlib_worktree\tdirty'
  fi
  printf 'compiler\t%s\n' "$("$cc" --version | head -n 1)"
  printf '%s\n' $'mpfr_compile_flags\t-O2 -std=c11 -Wall -Wextra -Werror'
  printf 'mpfr_version\t%s\n' "$(pkg-config --modversion mpfr)"
  printf 'python_version\t%s\n' "$(python3 --version 2>&1)"
  printf 'random_count_per_format\t%s\n' "$random_count"
  printf 'core_math_revision\t%s\n' "$(git_revision "$core_math_root")"
  printf 'openlibm_revision\t%s\n' "$(git_revision "$openlibm_root")"
  printf 'rlibm_revision\t%s\n' "$(git_revision "$rlibm_root")"
} >"$provenance"

report_args=(
  --input "$references"
  --output-dir "$output_dir"
  --expected-random-count "$random_count"
  --provenance "$provenance"
)
if [[ -n "$core_math_lib" ]]; then
  report_args+=(--core-math-lib "$core_math_lib")
fi
if [[ -n "$openlibm_lib" ]]; then
  report_args+=(--openlibm-lib "$openlibm_lib")
fi
if [[ -n "$rlibm_lib" ]]; then
  report_args+=(--rlibm-lib "$rlibm_lib")
fi

python3 -B "$root/tests/oracles/transcendental_report.py" "${report_args[@]}"
printf 'details: %s\n' "$output_dir/details.tsv"
printf 'machine-readable summary: %s\n' "$output_dir/summary.json"
