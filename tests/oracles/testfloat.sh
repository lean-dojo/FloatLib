#!/usr/bin/env bash

# We use Berkeley TestFloat for the IEEE operations where its published
# generator overlaps our model, with Berkeley SoftFloat as its implementation:
# https://github.com/ucb-bar/berkeley-testfloat-3
# https://github.com/ucb-bar/berkeley-softfloat-3
#
# Third-party source, generated vectors, build products, and logs stay outside
# the repository. The default remains modest; a dedicated evaluator can opt
# into more workers explicitly.

set -euo pipefail

ROOT="$(
  cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd
)"

SOFTFLOAT_REVISION="a0c6494cdc11865811dec815d5c0049fba9d82a8"
TESTFLOAT_REVISION="a9c849f1b0eb0264b626d9686ffae167d996e3be"
SOFTFLOAT_URL="https://github.com/ucb-bar/berkeley-softfloat-3.git"
TESTFLOAT_URL="https://github.com/ucb-bar/berkeley-testfloat-3.git"

profile="${TESTFLOAT_PROFILE:-full}"
level="${TESTFLOAT_LEVEL:-1}"
seed="${TESTFLOAT_SEED:-1}"
workers="${TESTFLOAT_WORKERS:-}"
cpu_set="${TESTFLOAT_CPU_SET:-none}"
allow_huge_level2="${TESTFLOAT_ALLOW_HUGE_LEVEL2:-false}"
cache_root="${TESTFLOAT_CACHE_ROOT:-${TMPDIR:-/tmp}/floatlib-testfloat-upstream}"
timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
results="${TESTFLOAT_RESULTS:-${TMPDIR:-/tmp}/floatlib-testfloat-results-$timestamp}"

usage() {
  cat <<'EOF'
usage: tests/oracles/testfloat.sh [OPTIONS]

Options:
  --profile smoke|core|full  smoke test, full non-FMA matrix, or complete matrix
  --level 1|2               TestFloat generation level (default: 1)
  --seed N                  deterministic TestFloat seed (default: 1)
  --workers N               pipelines (default: available CPUs, capped at 8)
  --cpu-set LIST            taskset CPU list; "none" inherits affinity (default)
  --allow-huge-level2       permit core/full level-2 campaigns
  --cache DIR               external SoftFloat/TestFloat source and build cache
  --results DIR             new output directory for logs and summaries
  -h, --help                show this help

The default full level-1 campaign contains 175 format/operation/mode combinations.
EOF
}

while (($#)); do
  case "$1" in
    --profile|--level|--seed|--workers|--cpu-set|--cache|--results)
      if (($# < 2)) || [[ -z "$2" || "$2" == --* || "$2" == -h ]]; then
        printf '%s requires a value\n' "$1" >&2
        exit 2
      fi
      ;;
  esac
  case "$1" in
    --profile)
      profile="$2"
      shift 2
      ;;
    --level)
      level="$2"
      shift 2
      ;;
    --seed)
      seed="$2"
      shift 2
      ;;
    --workers)
      workers="$2"
      shift 2
      ;;
    --cpu-set)
      cpu_set="$2"
      shift 2
      ;;
    --allow-huge-level2)
      allow_huge_level2=true
      shift
      ;;
    --cache)
      cache_root="$2"
      shift 2
      ;;
    --results)
      results="$2"
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

case "$profile" in
  smoke|core|full) ;;
  *)
    printf 'invalid profile: %s\n' "$profile" >&2
    exit 2
    ;;
esac

case "$level" in
  1|2) ;;
  *)
    printf 'invalid TestFloat level: %s\n' "$level" >&2
    exit 2
    ;;
esac

if [[ "$level" == "2" && "$profile" != "smoke" && "$allow_huge_level2" != "true" ]]; then
  printf '%s\n' \
    'core/full level 2 requires --allow-huge-level2.' \
    'TestFloat generates 1,851,438,185,872 vectors for one binary128 FMA mode alone.' \
    'Use the smoke profile for a bounded level-2 check or opt in deliberately.' >&2
  exit 2
fi

if [[ -e "$results" ]]; then
  printf 'results path already exists; choose a new directory: %s\n' "$results" >&2
  exit 2
fi

if [[ "$cpu_set" != "none" ]]; then
  if ! command -v taskset >/dev/null 2>&1; then
    printf 'taskset is required for --cpu-set; use --cpu-set none to disable affinity\n' >&2
    exit 2
  fi
  if ! taskset -pc "$cpu_set" "$$" >/dev/null 2>&1; then
    printf 'invalid or unavailable CPU list: %s\n' "$cpu_set" >&2
    exit 2
  fi
fi
# Respect lower nproc limits without letting OpenMP settings enlarge the CPU allowance.
available_cpus="$(nproc)"
affinity_cpus="$(env -u OMP_NUM_THREADS -u OMP_THREAD_LIMIT nproc)"
if ((available_cpus > affinity_cpus)); then
  available_cpus="$affinity_cpus"
fi
if [[ -z "$workers" ]]; then
  workers="$available_cpus"
  if ((workers > 8)); then
    workers=8
  fi
fi
if [[ ! "$seed" =~ ^[0-9]+$ ]] ||
    [[ ! "$workers" =~ ^[1-9][0-9]*$ ]] ||
    ((${#workers} > ${#available_cpus})) ||
    ((workers > available_cpus)); then
  printf 'seed must be nonnegative and workers must be between 1 and %s inside the selected affinity\n' \
    "$available_cpus" >&2
  exit 2
fi
build_jobs="${TESTFLOAT_BUILD_JOBS:-$workers}"
if [[ ! "$build_jobs" =~ ^[1-9][0-9]*$ ]] ||
    ((${#build_jobs} > ${#available_cpus})) ||
    ((build_jobs > available_cpus)); then
  printf 'TESTFLOAT_BUILD_JOBS must be between 1 and %s: %s\n' \
    "$available_cpus" "$build_jobs" >&2
  exit 2
fi

if ! python3 -c 'import matplotlib' >/dev/null 2>&1; then
  printf '%s\n' \
    'Matplotlib is required to render the TestFloat conformance report.' >&2
  exit 2
fi
mkdir -p "$cache_root" "$results/logs"

ensure_checkout() {
  local url=$1
  local revision=$2
  local directory=$3

  if [[ ! -d "$directory/.git" ]]; then
    git clone --filter=blob:none "$url" "$directory"
  fi
  git -C "$directory" fetch --depth 1 origin "$revision"
  git -C "$directory" checkout --detach "$revision"
  local actual
  actual="$(git -C "$directory" rev-parse HEAD)"
  if [[ "$actual" != "$revision" ]]; then
    printf 'revision mismatch in %s: expected %s, found %s\n' \
      "$directory" "$revision" "$actual" >&2
    exit 2
  fi
  local status
  status="$(
    git -C "$directory" status \
      --porcelain=v1 --untracked-files=all --ignored=matching
  )"
  if [[ -n "$status" ]]; then
    printf 'upstream checkout is not completely clean: %s\n' "$directory" >&2
    printf '%s\n' "$status" >&2
    exit 2
  fi
}

softfloat_source="$cache_root/sources/berkeley-softfloat-3"
testfloat_source="$cache_root/sources/berkeley-testfloat-3"
mkdir -p "$cache_root/sources"
ensure_checkout "$SOFTFLOAT_URL" "$SOFTFLOAT_REVISION" "$softfloat_source"
ensure_checkout "$TESTFLOAT_URL" "$TESTFLOAT_REVISION" "$testfloat_source"

# TestFloat's Makefile expects SoftFloat in a sibling directory. Creating both
# trees from Git archives gives every invocation fresh object files while
# retaining that upstream layout.
build_root="$(mktemp -d "$cache_root/build.XXXXXXXX")"
softfloat_root="$build_root/berkeley-softfloat-3"
testfloat_root="$build_root/berkeley-testfloat-3"
mkdir -p "$softfloat_root" "$testfloat_root"
git -C "$softfloat_source" archive "$SOFTFLOAT_REVISION" |
  tar -x -C "$softfloat_root"
git -C "$testfloat_source" archive "$TESTFLOAT_REVISION" |
  tar -x -C "$testfloat_root"

make -C "$softfloat_root/build/Linux-x86_64-GCC" -j "$build_jobs"
make -C "$testfloat_root/build/Linux-x86_64-GCC" -j "$build_jobs" testfloat_gen

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"
floatlib_test_lake build oracle

generator="$testfloat_root/build/Linux-x86_64-GCC/testfloat_gen"
checker="$(floatlib_build_path bin/oracle)"
manifest="$results/campaigns.tsv"
: >"$manifest"

emit_case() {
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$@" >>"$manifest"
}

emit_four_modes() {
  local kind=$1
  local source=$2
  local operation=$3
  local exactness=$4
  emit_case "$kind" "$source" "$operation" rnear_even near_even "$exactness"
  emit_case "$kind" "$source" "$operation" rminMag minMag "$exactness"
  emit_case "$kind" "$source" "$operation" rmin min "$exactness"
  emit_case "$kind" "$source" "$operation" rmax max "$exactness"
}

emit_conversion_matrix() {
  local destination
  for destination in f32 f64 f128; do
    emit_case conversion f16 "$destination" rnear_even near_even none
  done
  emit_case conversion bf16 f32 rnear_even near_even none
  for destination in bf16 f16; do
    emit_four_modes conversion f32 "$destination" none
  done
  emit_case conversion f32 f64 rnear_even near_even none
  emit_case conversion f32 f128 rnear_even near_even none
  for destination in f16 f32; do
    emit_four_modes conversion f64 "$destination" none
  done
  emit_case conversion f64 f128 rnear_even near_even none
  for destination in f16 f32 f64; do
    emit_four_modes conversion f128 "$destination" none
  done
}

if [[ "$profile" == "smoke" ]]; then
  emit_case operation f16 add rnear_even near_even none
  emit_case operation f32 sqrt rmax max none
  emit_case conversion f32 bf16 rnear_even near_even none
else
  for format in f16 f32 f64 f128; do
    for operation in add sub mul div sqrt; do
      emit_four_modes operation "$format" "$operation" none
    done
    emit_case operation "$format" rem rnear_even near_even none
    emit_four_modes operation "$format" roundToInt exact
    for operation in eq le lt eq_signaling le_quiet lt_quiet; do
      emit_case operation "$format" "$operation" rnear_even near_even none
    done
  done
  emit_conversion_matrix
  if [[ "$profile" == "full" ]]; then
    for format in f16 f32 f64 f128; do
      emit_four_modes operation "$format" mulAdd none
    done
  fi
fi

run_campaign() {
  set -euo pipefail
  local line=$1
  local kind source operation generator_mode checker_mode exactness
  IFS=$'\t' read -r kind source operation generator_mode checker_mode exactness <<<"$line"

  local function_name checker_operation
  if [[ "$kind" == "conversion" ]]; then
    function_name="${source}_to_${operation}"
    checker_operation="to_${operation}"
  else
    function_name="${source}_${operation}"
    checker_operation="$operation"
  fi

  local label="${source}_${checker_operation}_${checker_mode}"
  local log="$results/logs/$label.log"
  local options=(-level "$level" -seed "$seed" "-$generator_mode" -tininessafter)
  if [[ "$exactness" == "exact" ]]; then
    options+=(-exact)
  fi

  if ! "$generator" "${options[@]}" "$function_name" |
      "$checker" testfloat "$source" "$checker_operation" "$checker_mode" 10 >"$log" 2>&1; then
    printf 'FAILED %s\n' "$label" >&2
    sed -n '1,80p' "$log" >&2
    printf 'reproduce: %q' "$generator" >&2
    printf ' %q' "${options[@]}" "$function_name" >&2
    printf ' | %q testfloat %q %q %q 10\n' \
      "$checker" "$source" "$checker_operation" "$checker_mode" >&2
    return 1
  fi
  tail -n 1 "$log"
}
export results generator checker level seed
export -f run_campaign

# xargs exits 123 when any campaign fails. Record that instead of stopping here so the
# completeness check and the summary below still describe the whole run.
xargs_status=0
xargs -r -d '\n' -P "$workers" -n 1 bash -c 'run_campaign "$1"' _ \
  <"$manifest" >"$results/results.txt" || xargs_status=$?

campaign_failed=0
if [[ "$xargs_status" -ne 0 ]]; then
  printf 'one or more TestFloat campaigns failed (xargs status %s)\n' "$xargs_status" >&2
  campaign_failed=1
fi

expected_campaigns="$(wc -l <"$manifest")"
completed_campaigns="$(wc -l <"$results/results.txt")"
if [[ "$completed_campaigns" != "$expected_campaigns" ]]; then
  printf 'incomplete TestFloat campaign: completed %s of %s rows\n' \
    "$completed_campaigns" "$expected_campaigns" >&2
  campaign_failed=1
fi

fma_campaigns="$(
  awk -F '\t' '
    $1 == "operation" && $3 == "mulAdd" { count += 1 }
    END { print count + 0 }
  ' "$manifest"
)"
bf16_arithmetic_campaigns="$(
  awk -F '\t' '
    $1 == "operation" && $2 == "bf16" { count += 1 }
    END { print count + 0 }
  ' "$manifest"
)"

{
  printf 'profile=%s\n' "$profile"
  printf 'level=%s\n' "$level"
  printf 'seed=%s\n' "$seed"
  printf 'fma_campaigns=%s\n' "$fma_campaigns"
  printf 'bf16_arithmetic_campaigns=%s\n' "$bf16_arithmetic_campaigns"
  printf 'workers=%s\n' "$workers"
  printf 'build_jobs=%s\n' "$build_jobs"
  printf 'cpu_set=%s\n' "$cpu_set"
  printf 'softfloat_revision=%s\n' "$SOFTFLOAT_REVISION"
  printf 'testfloat_revision=%s\n' "$TESTFLOAT_REVISION"
  printf 'lean_revision=%s\n' "$(git -C "$ROOT" rev-parse HEAD)"
  printf 'lean_build_dir=%s\n' "$FLOATLIB_BUILD_DIR"
  printf 'compiler=%s\n' "$(gcc --version | sed -n '1p')"
  printf 'host=%s\n' "$(uname -srmo)"
  printf 'worktree_diff_sha256=%s\n' "$(
    git -C "$ROOT" diff --binary HEAD | sha256sum | awk '{print $1}'
  )"
} >"$results/metadata.txt"
git -C "$ROOT" status --short >"$results/worktree-status.txt"

awk '
  {
    campaigns += 1
    for (i = 1; i <= NF; i++) {
      split($i, pair, "=")
      if (pair[1] == "cases") cases += pair[2]
      if (pair[1] == "value_mismatches") values += pair[2]
      if (pair[1] == "flag_mismatches") flags += pair[2]
      if (pair[1] == "parse_errors") parses += pair[2]
    }
  }
  END {
    printf "campaigns=%d cases=%d value_mismatches=%d flag_mismatches=%d parse_errors=%d\n",
      campaigns, cases, values, flags, parses
  }
' "$results/results.txt" | tee "$results/summary.txt"

python3 "$ROOT/tests/oracles/testfloat_report.py" \
  --results "$results" \
  --profile "$profile" \
  --level "$level" \
  --seed "$seed"

python3 "$ROOT/tests/oracles/conformance_plot.py" \
  "$results/campaigns.csv" \
  "$results/conformance" \
  --group-column format \
  --group-column operation \
  --group-label 'format=Source format' \
  --group-label 'operation=Operation' \
  --cases-column cases \
  --mismatch-column value_mismatches \
  --mismatch-column flag_mismatches \
  --mismatch-column parse_errors \
  --title 'Berkeley TestFloat conformance' \
  --subtitle "Profile $profile, level $level, seed $seed"

printf 'results=%s\n' "$results"

if [[ "$campaign_failed" -ne 0 ]]; then
  printf 'TestFloat run finished with failures; see %s/logs\n' "$results" >&2
  exit 1
fi
