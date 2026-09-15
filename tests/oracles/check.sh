#!/usr/bin/env bash

# Run every maintained external comparison and the native boundary check sequentially.

set -euo pipefail

root="$(
  cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd
)"
cd "$root"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

profile="quick"
workers=""
cpu_set="none"
timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
results="${TMPDIR:-/tmp}/floatlib-external-validation-$timestamp"
cache_root="${FLOATLIB_EXTERNAL_CACHE_ROOT:-${TMPDIR:-/tmp}/floatlib-external-upstream-$timestamp}"

# Release-only sources are pinned here because this runner is the reproducible
# campaign boundary. Individual adapters still verify the revision they are
# given before they execute it.
softposit_url="https://gitlab.com/cerlane/SoftPosit.git"
softposit_revision="17d5628185b31828b10c1f910c9bf65737e83640"
core_math_url="https://gitlab.inria.fr/core-math/core-math.git"
core_math_revision="68b034fbe9512781352d28f2dc9795c1686fe8e9"
openlibm_url="https://github.com/JuliaMath/openlibm.git"
openlibm_revision="5fe399749f9276eaa0b8403e507470da05cbbb3f"
rlibm_url="https://github.com/rutgers-apl/rlibm.git"
rlibm_revision="8533ec0db38b2f3ab55c1b296ddaec80d578e251"

usage() {
  cat <<'EOF'
usage: tests/oracles/check.sh [OPTIONS]

Options:
  --profile quick|release  quick checks or all maintained comparisons (default: quick)
  --workers N              workers per suite (default: available CPUs, capped at 8)
  --cpu-set LIST           taskset CPU list; "none" inherits affinity (default)
  --results DIR            write logs and results to a new directory
  -h, --help               show this help

Suites run one at a time. Release adds the extended IEEE, SoftPosit, and
elementary-function comparisons and checks their adapters.
EOF
}

while (($#)); do
  case "$1" in
    --profile|--workers|--cpu-set|--results)
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
    --workers)
      workers="$2"
      shift 2
      ;;
    --cpu-set)
      cpu_set="$2"
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
  quick|release) ;;
  *)
    printf 'invalid profile: %s\n' "$profile" >&2
    exit 2
    ;;
esac
if [[ -e "$results" ]]; then
  printf 'results path already exists: %s\n' "$results" >&2
  exit 2
fi
if [[ "$cpu_set" != "none" ]]; then
  if ! command -v taskset >/dev/null 2>&1; then
    printf '%s\n' 'taskset is required; use --cpu-set none to disable affinity.' >&2
    exit 2
  fi
  if ! taskset -pc "$cpu_set" "$$" >/dev/null 2>&1; then
    printf 'invalid or unavailable CPU list: %s\n' "$cpu_set" >&2
    exit 2
  fi
fi
# Keep lower nproc limits used by the adapters, but do not let OpenMP settings
# enlarge the process's CPU allowance.
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
if ! [[ "$workers" =~ ^[1-9][0-9]*$ ]] ||
    ((${#workers} > ${#available_cpus})) ||
    ((workers > available_cpus)); then
  printf 'workers must be between 1 and %s inside the selected affinity: %s\n' \
    "$available_cpus" "$workers" >&2
  exit 2
fi

mkdir -p "$results/logs"
summary="$results/summary.tsv"
printf '%s\n' $'suite\tstatus\tseconds\tlog' >"$summary"

{
  printf 'timestamp_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'head_revision=%s\n' "$(git rev-parse HEAD)"
  printf 'profile=%s\n' "$profile"
  printf 'workers=%s\n' "$workers"
  printf 'cpu_set=%s\n' "$cpu_set"
  printf 'floatlib_build_dir=%s\n' "$FLOATLIB_BUILD_DIR"
  printf 'worktree_diff_sha256=%s\n' "$(
    git diff --binary HEAD |
      sha256sum |
      awk '{print $1}'
  )"
} >"$results/metadata.txt"
git status --short >"$results/worktree-status.txt"

failures=0
run_suite() {
  local success_status=pass
  if [[ "${1:-}" == "--success-status" ]]; then
    success_status="${2:?--success-status requires a label}"
    shift 2
  fi
  local suite=$1
  shift
  local log="$results/logs/$suite.log"
  local started finished status code
  started="$(date +%s)"
  printf '\n== %s ==\n' "$suite"
  set +e
  (set -e; "$@") 2>&1 | tee "$log"
  code=$?
  set -e
  finished="$(date +%s)"
  if ((code == 0)); then
    status="$success_status"
  else
    status="fail($code)"
    failures=$((failures + 1))
  fi
  printf '%s\t%s\t%s\t%s\n' \
    "$suite" "$status" "$((finished - started))" "logs/$suite.log" >>"$summary"
}

ensure_pinned_checkout() {
  local url=$1
  local revision=$2
  local directory=$3

  if [[ ! -d "$directory/.git" ]]; then
    git clone --filter=blob:none "$url" "$directory"
  fi
  git -C "$directory" fetch --depth 1 origin "$revision"
  git -C "$directory" checkout --detach "$revision"
  if [[ "$(git -C "$directory" rev-parse HEAD)" != "$revision" ]]; then
    printf 'revision mismatch in %s\n' "$directory" >&2
    return 2
  fi
  local status
  status="$(
    git -C "$directory" status \
      --porcelain=v1 --untracked-files=all --ignored=matching
  )"
  if [[ -n "$status" ]]; then
    printf 'upstream checkout is not completely clean: %s\n' "$directory" >&2
    printf '%s\n' "$status" >&2
    return 2
  fi
}

run_testfloat() {
  local testfloat_profile=smoke
  if [[ "$profile" == "release" ]]; then
    testfloat_profile=full
  fi
  tests/oracles/testfloat.sh \
    --profile "$testfloat_profile" \
    --level 1 \
    --seed 1 \
    --workers "$workers" \
    --cpu-set "$cpu_set" \
    --cache "$cache_root/testfloat" \
    --results "$results/01-testfloat"
}

run_format_standards() {
  local maximum_width=8
  if [[ "$profile" == "release" ]]; then
    maximum_width=16
  fi
  FORMAT_STANDARDS_RESULTS="$results/02-format-standards" \
  FORMAT_STANDARDS_P3109_MAX_WIDTH="$maximum_width" \
  FORMAT_STANDARDS_WORKERS="$workers" \
  FORMAT_STANDARDS_CPU_SET="$cpu_set" \
  FORMAT_STANDARDS_CACHE_ROOT="$cache_root/format-standards" \
    tests/oracles/format-standards.sh
}

run_arb() {
  floatlib_test_lake exe check arb
}

run_native_fpu() {
  floatlib_test_lake exe check native
}

run_binary16_rows() {
  local operation left_word
  local -a left_words=(
    0x0000 0x8000                # signed zeros
    0x0001 0x8001 0x03ff 0x0400  # subnormals and the smallest normal
    0x3555 0x3c00 0x3c01 0xbc00  # ordinary normals and adjacent values
    0x7bff 0xfbff                # largest finite magnitudes
    0x7c00 0xfc00 0x7e01 0x7c01  # infinities and quiet/signaling NaNs
  )
  # At this shard count each left word is paired with every binary16 right word.
  for operation in add mul; do
    for left_word in "${left_words[@]}"; do
      tests/oracles/binary16-exhaustive.sh "$operation" "$((left_word))" 65536
    done
  done
}

run_adapter_unit_tests() {
  python3 -B -m unittest \
    tests/oracles/ibm_fpgen_test.py \
    tests/oracles/smt_fp_test.py \
    tests/oracles/transcendental_test.py \
    tests/oracles/verify_release_evidence_test.py
  floatlib_test_lake build oracle
  python3 -B tests/oracles/softposit_protocol_test.py \
    "$(floatlib_build_path bin/oracle)"
}

run_testfloat_level2_smoke() {
  tests/oracles/testfloat.sh \
    --profile smoke \
    --level 2 \
    --seed 1 \
    --workers "$workers" \
    --cpu-set "$cpu_set" \
    --cache "$cache_root/testfloat" \
    --results "$results/08-testfloat-level2-smoke"
}

run_ibm_fpgen() {
  tests/oracles/ibm_fpgen.sh \
    --cache "$cache_root/ibm-fpgen" \
    --results "$results/09-ibm-fpgen"
}

run_smt() {
  tests/oracles/smt_fp.sh \
    --seed 1592614637 \
    --random-per-format 256 \
    --timeout 1800 \
    --results "$results/10-smt-qf-fp"
}

run_softposit() {
  local source="$cache_root/softposit"
  local suite_results="$results/11-softposit"
  local manifest="$suite_results/campaigns.tsv"
  mkdir -p "$suite_results/logs" "$suite_results/status"
  ensure_pinned_checkout "$softposit_url" "$softposit_revision" "$source"

  printf '%s\n' $'family\tbits\toperation\tmode\tcount' >"$manifest"
  local bits operation
  for bits in 2 3 4 5 6 7 8; do
    for operation in add sub mul div fma sqrt rint eq le lt; do
      printf 'px2\t%s\t%s\texhaustive\t0\n' "$bits" "$operation" >>"$manifest"
    done
  done
  for bits in {9..16} 32; do
    for operation in add sub mul div fma sqrt rint eq le lt; do
      printf 'px2\t%s\t%s\tsampled\t131072\n' "$bits" "$operation" >>"$manifest"
    done
  done
  for operation in add sub mul div fma sqrt rint eq le lt; do
    printf 'p32\t32\t%s\tsampled\t131072\n' "$operation" >>"$manifest"
  done

  run_softposit_cell() {
    set -euo pipefail
    local line=$1
    local family bits operation mode count
    IFS=$'\t' read -r family bits operation mode count <<<"$line"
    local label="${family}-${bits}-${operation}-${mode}"
    local log="$suite_results/logs/$label.log"
    local status_file="$suite_results/status/$label.tsv"
    local arguments=(
      --softposit-dir "$source"
      --family "$family"
      --bits "$bits"
      --op "$operation"
      --seed 1592614637
    )
    if [[ "$mode" == exhaustive ]]; then
      arguments+=(--exhaustive)
    else
      arguments+=(--sampled "$count")
    fi

    local status=pass
    if ! SOFTPOSIT_BUILD_JOBS=1 tests/oracles/softposit.sh \
        "${arguments[@]}" >"$log" 2>&1; then
      status=fail
    fi
    local result cases mismatches
    result="$(grep '^RESULT oracle=softposit ' "$log" | tail -1 || true)"
    cases="$(awk -v text="$result" 'BEGIN {
      split(text, fields, " ")
      for (field in fields) {
        split(fields[field], pair, "=")
        if (pair[1] == "cases") print pair[2]
      }
    }')"
    mismatches="$(awk -v text="$result" 'BEGIN {
      split(text, fields, " ")
      for (field in fields) {
        split(fields[field], pair, "=")
        if (pair[1] == "mismatches") print pair[2]
      }
    }')"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$family" "$bits" "$operation" "$mode" "$status" \
      "${cases:-0}" "${mismatches:-1}" "logs/$label.log" >"$status_file"
    [[ "$status" == pass ]]
  }
  export source suite_results
  export -f run_softposit_cell

  local xargs_status=0
  tail -n +2 "$manifest" |
    xargs -r -d '\n' -P "$workers" -n 1 \
      bash -c 'run_softposit_cell "$1"' _ || xargs_status=$?

  local summary_csv="$suite_results/summary.csv"
  printf '%s\n' 'family,bits,operation,mode,status,cases,mismatches,log' \
    >"$summary_csv"
  sort "$suite_results"/status/*.tsv |
    tr '\t' ',' >>"$summary_csv"
  python3 tests/oracles/conformance_plot.py \
    "$summary_csv" "$suite_results/conformance" \
    --group-column bits \
    --group-column operation \
    --group-label 'bits=Posit width' \
    --group-label 'operation=Operation' \
    --cases-column cases \
    --mismatch-column mismatches \
    --status-column status \
    --title 'SoftPosit differential checks' \
    --subtitle 'Exhaustive at 2–8 bits; deterministic samples at 16 and 32 bits'
  if ((xargs_status != 0)); then
    return 1
  fi
  if ! awk -F, \
      'NR > 1 && $5 != "pass" { failed = 1 } END { exit failed }' \
      "$summary_csv"; then
    return 1
  fi
}

run_transcendentals() {
  local source_root="$cache_root/transcendentals"
  local core_math_root="$source_root/core-math"
  local openlibm_root="$source_root/openlibm"
  local rlibm_root="$source_root/rlibm"
  mkdir -p "$source_root"
  ensure_pinned_checkout "$core_math_url" "$core_math_revision" "$core_math_root"
  ensure_pinned_checkout "$openlibm_url" "$openlibm_revision" "$openlibm_root"
  ensure_pinned_checkout "$rlibm_url" "$rlibm_revision" "$rlibm_root"
  tests/oracles/transcendental_compare.sh \
    --output-dir "$results/12-transcendentals" \
    --random-count 256 \
    --jobs "$workers" \
    --core-math-root "$core_math_root" \
    --openlibm-root "$openlibm_root" \
    --rlibm-root "$rlibm_root"
}

if [[ "$profile" == release ]]; then
  run_suite "00-adapter-unit-tests" run_adapter_unit_tests
fi
run_suite "01-testfloat" run_testfloat
run_suite "02-format-standards" run_format_standards
run_suite "03-mpfr-primitives" tests/oracles/mpfr.sh primitives
run_suite "04-mpfr-reductions" tests/oracles/mpfr.sh reductions
run_suite "05-arb" run_arb
run_suite "06-native-fpu" run_native_fpu
run_suite "07-binary16-mpfr-rows" run_binary16_rows
if [[ "$profile" == release ]]; then
  run_suite "08-testfloat-level2-smoke" run_testfloat_level2_smoke
  run_suite "09-ibm-fpgen" run_ibm_fpgen
  run_suite "10-smt-qf-fp" run_smt
  run_suite "11-softposit" run_softposit
  run_suite \
    --success-status observational-complete \
    "12-transcendentals" \
    run_transcendentals
fi

export MPLCONFIGDIR="$results/.matplotlib"
mkdir -p "$MPLCONFIGDIR"
if python3 tests/oracles/render_release_result.py "$summary" "$results"; then
  printf '%s\n' 'status=rendered' >"$results/rendering-status.txt"
else
  printf '%s\n' 'status=failed' >"$results/rendering-status.txt"
  failures=$((failures + 1))
fi
rm -rf -- "$MPLCONFIGDIR"

python3 tests/oracles/write_result_manifest.py "$results"

cat "$results/summary.md"
printf 'results=%s\n' "$results"
if ((failures != 0)); then
  printf '%d comparison or boundary check(s) failed\n' "$failures" >&2
  exit 1
fi
