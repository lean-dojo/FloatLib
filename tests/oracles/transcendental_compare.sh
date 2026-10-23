#!/usr/bin/env bash

# Gate FloatLib's transcendental functions against MPFR, with optional public libm observations.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

usage() {
  cat <<'EOF'
usage: tests/oracles/transcendental_compare.sh [OPTIONS]

Options:
  --output-dir DIR             Result directory (default: a fresh directory under TMPDIR)
  --random-count N             Random inputs and pow pairs per format, 0..4096 (default: 32)
  --slow                       Add the slow corpus tier and every binary16 and bfloat16 code
  --jobs N                     Parallel emitter and MPFR shards, and jobs for optional external
                               builds (default: 8)
  --known-failures FILE        Known-failures list (default: the checked-in list)
  --write-known-failures FILE  Also write this run's mismatches as a known-failures list
  --census FILE                Coverage census (default: the checked-in census)
  --require-census NAME        Fail unless this run reproduces census entry NAME
  --write-census NAME          Also record this run's coverage in the census as entry NAME
  --core-math-root DIR         Build the 14 relevant CORE-MATH source files
  --core-math-lib FILE         Use an existing CORE-MATH shared library
  --openlibm-root DIR          Build OpenLibm with its Makefile
  --openlibm-lib FILE          Use an existing OpenLibm shared library
  --rlibm-root DIR             Build RLIBM's supported binary32 functions
  --rlibm-lib FILE             Use an existing RLIBM shared library
  -h, --help                   Show this help

The command fails when FloatLib differs from MPFR on a case that the known-failures list does
not name, when a listed case now matches or fails differently, on any value mismatch in a domain
FloatLib declares correctly rounded, and when the run's requests differ from those the census
records for its random count, tier and exhaustive16 setting (--slow sets both). The census records
the default run, the release run (--random-count 256) and the qualification run (--slow
--random-count 256), which must also exercise every listed case; after changing the emitter or
the corpus, rerun the three with --write-census default, release and qualification. Other
invocations leave coverage unchecked, unless --require-census names the entry they must match.
The *_ROOT options may also be supplied as CORE_MATH_ROOT, OPENLIBM_ROOT, and RLIBM_ROOT
environment variables. Library options take precedence over roots.
EOF
}

output_dir=""
random_count=32
slow=0
jobs="${JOBS:-8}"
known_failures="$root/tests/oracles/data/transcendental-known-failures.tsv"
write_known_failures=""
census="$root/tests/oracles/data/transcendental-census.json"
require_census=""
write_census=""
# Relative to the repository root, so the manifest records no local path.
corpus="tests/oracles/data/transcendental-hard-cases.tsv"
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
    --slow)
      slow=1
      shift
      ;;
    --jobs)
      jobs="${2:?--jobs requires a value}"
      shift 2
      ;;
    --known-failures)
      known_failures="${2:?--known-failures requires a value}"
      shift 2
      ;;
    --write-known-failures)
      write_known_failures="${2:?--write-known-failures requires a value}"
      shift 2
      ;;
    --census)
      census="${2:?--census requires a value}"
      shift 2
      ;;
    --require-census)
      require_census="${2:?--require-census requires a value}"
      shift 2
      ;;
    --write-census)
      write_census="${2:?--write-census requires a value}"
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

# The emitter reports the count in canonical decimal, so strip leading zeros before comparing;
# the length test keeps oversized numbers out of shell arithmetic.
if [[ "$random_count" =~ ^[0-9]+$ ]]; then
  random_count="${random_count#"${random_count%%[!0]*}"}"
  random_count="${random_count:-0}"
fi
if [[ ! "$random_count" =~ ^[0-9]+$ ]] || ((${#random_count} > 4)) ||
    ((random_count > 4096)); then
  printf '%s\n' '--random-count must be an integer from 0 through 4096' >&2
  exit 2
fi
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  printf '%s\n' '--jobs must be a positive integer' >&2
  exit 2
fi
if [[ ! -f "$known_failures" ]]; then
  printf 'known-failures list not found: %s\n' "$known_failures" >&2
  exit 2
fi
if [[ -z "$write_census" && ! -f "$census" ]]; then
  printf 'census not found: %s\n' "$census" >&2
  exit 2
fi
if [[ -n "$write_census" && ! "$write_census" =~ ^[a-z][a-z0-9-]*$ ]]; then
  printf 'invalid census entry name: %s\n' "$write_census" >&2
  exit 2
fi
if ! command -v pkg-config >/dev/null 2>&1 ||
    ! pkg-config --atleast-version=4.1.0 mpfr; then
  printf '%s\n' 'MPFR 4.1.0 or newer is required.' >&2
  exit 1
fi

# With the revision, these digests fingerprint a modified worktree, as check.sh does for release
# runs: the tracked changes, and the untracked files that Git does not ignore, by name and
# content. They are taken before the run writes anything, so an output directory inside the
# worktree does not enter them. They identify the sources only if nothing edits the worktree
# during the run, and they archive nothing.
worktree_diff_digest=not-recorded
untracked_digest=not-recorded
if git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  worktree_diff_digest="$(git -C "$root" diff --binary HEAD | sha256sum | cut -d ' ' -f 1)" ||
    worktree_diff_digest=not-recorded
  untracked_digest="$(
    git -C "$root" ls-files -z --others --exclude-standard |
      LC_ALL=C sort -z |
      xargs -0 -r sha256sum -- |
      sha256sum |
      cut -d ' ' -f 1
  )" || untracked_digest=not-recorded
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

FLOATLIB_TRANSCENDENTAL_ORACLE="$mpfr_oracle" \
  python3 -B "$root/tests/oracles/transcendental_test.py"

floatlib_acquire_build_lock
if (
  cd "$root/tests"
  lake -f "$root/tests/oracles/Transcendental/lakefile.lean" \
    --packages="$root/tests/lake-manifest.json" \
    -R -KbuildDir="$FLOATLIB_BUILD_DIR" \
    build transcendentalEmitter
) >&2; then
  emitter_status=0
else
  emitter_status=$?
fi
floatlib_release_build_lock
if ((emitter_status != 0)); then
  exit "$emitter_status"
fi
emitter="$(floatlib_build_path bin/transcendentalEmitter)"

tier=default
exhaustive16=false
if ((slow)); then
  tier=slow
  exhaustive16=true
fi
emitter_args=(--random-count "$random_count" --hard "$corpus" --tier "$tier")
if ((slow)); then
  emitter_args+=(--exhaustive16)
fi

# Each shard evaluates every jobs-th request in FloatLib and pipes it straight into MPFR.
references="$output_dir/references.tsv"
shard_dir="$build_dir/shards"
mkdir -p "$shard_dir"
pids=()
for ((shard = 0; shard < jobs; shard++)); do
  (
    set -o pipefail
    "$emitter" "${emitter_args[@]}" --shard "$shard/$jobs" 2>"$shard_dir/$shard.emitter.log" |
      "$mpfr_oracle" >"$shard_dir/$shard.tsv" 2>"$shard_dir/$shard.log"
  ) &
  pids+=("$!")
done
shard_failures=0
for ((shard = 0; shard < jobs; shard++)); do
  if ! wait "${pids[$shard]}"; then
    printf 'transcendental shard %s failed:\n' "$shard" >&2
    cat "$shard_dir/$shard.emitter.log" "$shard_dir/$shard.log" >&2
    shard_failures=$((shard_failures + 1))
  fi
done
if ((shard_failures != 0)); then
  exit 1
fi
for ((shard = 0; shard < jobs; shard++)); do
  cat "$shard_dir/$shard.tsv"
done >"$references"

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
  printf 'floatlib_worktree_diff_sha256\t%s\n' "$worktree_diff_digest"
  printf 'floatlib_untracked_sha256\t%s\n' "$untracked_digest"
  printf 'compiler\t%s\n' "$("$cc" --version | head -n 1)"
  printf '%s\n' $'mpfr_compile_flags\t-O2 -std=c11 -Wall -Wextra -Werror'
  printf 'mpfr_version\t%s\n' "$(pkg-config --modversion mpfr)"
  printf 'python_version\t%s\n' "$(python3 --version 2>&1)"
  printf 'random_count_per_format\t%s\n' "$random_count"
  printf 'tier\t%s\n' "$tier"
  printf 'shards\t%s\n' "$jobs"
  printf 'corpus_sha256\t%s\n' "$(sha256sum "$root/$corpus" | cut -d ' ' -f 1)"
  printf 'known_failures_sha256\t%s\n' "$(sha256sum "$known_failures" | cut -d ' ' -f 1)"
  if [[ -f "$census" ]]; then
    printf 'census_sha256\t%s\n' "$(sha256sum "$census" | cut -d ' ' -f 1)"
  else
    printf '%s\n' $'census_sha256\tnone'
  fi
  printf 'core_math_revision\t%s\n' "$(git_revision "$core_math_root")"
  printf 'openlibm_revision\t%s\n' "$(git_revision "$openlibm_root")"
  printf 'rlibm_revision\t%s\n' "$(git_revision "$rlibm_root")"
} >"$provenance"

# The report checks the emitter's manifest against the options given here, so an emitter that
# misreports its invocation cannot select another census entry or none.
report_args=(
  --input "$references"
  --output-dir "$output_dir"
  --known-failures "$known_failures"
  --census "$census"
  --provenance "$provenance"
  --expect-manifest "random-count $random_count"
  --expect-manifest "tier $tier"
  --expect-manifest "exhaustive16 $exhaustive16"
  --expect-manifest "hard $corpus"
)
if [[ -n "$require_census" ]]; then
  report_args+=(--require-census "$require_census")
fi
if [[ -n "$write_known_failures" ]]; then
  report_args+=(--write-known-failures "$write_known_failures")
fi
if [[ -n "$write_census" ]]; then
  report_args+=(--write-census "$write_census")
fi
if [[ -n "$core_math_lib" ]]; then
  report_args+=(--core-math-lib "$core_math_lib")
fi
if [[ -n "$openlibm_lib" ]]; then
  report_args+=(--openlibm-lib "$openlibm_lib")
fi
if [[ -n "$rlibm_lib" ]]; then
  report_args+=(--rlibm-lib "$rlibm_lib")
fi

if python3 -B "$root/tests/oracles/transcendental_report.py" "${report_args[@]}"; then
  report_status=0
else
  report_status=$?
fi
printf 'mismatches: %s\n' "$output_dir/mismatches.tsv"
printf 'details: %s\n' "$output_dir/details.tsv"
printf 'machine-readable summary: %s\n' "$output_dir/summary.json"
exit "$report_status"
