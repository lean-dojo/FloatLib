#!/usr/bin/env bash

# Run the pinned IBM FPgen ieee754-test-suite through FloatLib's existing
# TestFloat-compatible checker. Generated streams and third-party sources stay
# outside the repository by default.

set -euo pipefail

ROOT="$(
  cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd
)"
ADAPTER="$ROOT/tests/oracles/ibm_fpgen.py"
PINNED_REVISION="12e883a0c7b826976a8f1243318ac4b7626a0ffc"
PINNED_URL="https://github.com/sergev/ieee754-test-suite.git"

timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
cache_root="${IBM_FPGEN_CACHE_ROOT:-${TMPDIR:-/tmp}/floatlib-ibm-fpgen-upstream}"
results="${IBM_FPGEN_RESULTS:-${TMPDIR:-/tmp}/floatlib-ibm-fpgen-$timestamp}"
suite=""
count_only=false
maximum_reports=10

usage() {
  cat <<'EOF'
usage: tests/oracles/ibm_fpgen.sh [OPTIONS]

Options:
  --suite DIR       use an existing checkout at the pinned revision
  --cache DIR       checkout cache used when --suite is omitted
  --results DIR     new results directory for streams, maps, and logs
  --count-only      validate and count vectors without building or running Lean
  --dry-run         alias for --count-only
  --reports N       maximum mismatch reports per checker group (default: 10)
  -h, --help        show this help

The default run checks the binary32 semantic overlap: arithmetic, fused
multiply-add, square root, 2008 min/max operations, sign operations,
classifications, and f32-to-f64/f128 casts in the four IEEE rounding
directions supported by FloatLib's checker. Nearest-away rows, NaN rows whose
sign was discarded, IBM's legacy quiet-NaN-first exception cases, and
non-after-rounding underflow conventions are counted explicitly as unsupported.
EOF
}

while (($#)); do
  case "$1" in
    --suite)
      suite="${2:?--suite requires a directory}"
      shift 2
      ;;
    --cache)
      cache_root="${2:?--cache requires a directory}"
      shift 2
      ;;
    --results)
      results="${2:?--results requires a directory}"
      shift 2
      ;;
    --count-only|--dry-run)
      count_only=true
      shift
      ;;
    --reports)
      maximum_reports="${2:?--reports requires a number}"
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

if [[ ! "$maximum_reports" =~ ^[0-9]+$ ]]; then
  printf -- '--reports must be a nonnegative integer: %s\n' "$maximum_reports" >&2
  exit 2
fi

ensure_pinned_checkout() {
  local directory=$1
  if [[ ! -d "$directory/.git" ]]; then
    git clone --filter=blob:none "$PINNED_URL" "$directory"
  fi
  if [[ -n "$(git -C "$directory" status --porcelain=v1 --untracked-files=all --ignored)" ]]; then
    printf 'local files prevent revision verification: %s\n' "$directory" >&2
    exit 2
  fi
  git -C "$directory" fetch --depth 1 origin "$PINNED_REVISION"
  git -C "$directory" checkout --detach "$PINNED_REVISION"
}

if [[ -z "$suite" ]]; then
  suite="$cache_root/ieee754-test-suite"
  mkdir -p "$cache_root"
  ensure_pinned_checkout "$suite"
fi

if [[ ! -d "$suite/.git" ]]; then
  printf 'suite is not a Git checkout: %s\n' "$suite" >&2
  exit 2
fi
actual_revision="$(git -C "$suite" rev-parse HEAD)"
if [[ "$actual_revision" != "$PINNED_REVISION" ]]; then
  printf 'suite revision mismatch: expected %s, found %s\n' \
    "$PINNED_REVISION" "$actual_revision" >&2
  exit 2
fi
if [[ -n "$(git -C "$suite" status --porcelain=v1 --untracked-files=all --ignored)" ]]; then
  printf 'suite has local or ignored files: %s\n' "$suite" >&2
  exit 2
fi

if [[ "$count_only" == "true" ]]; then
  exec python3 "$ADAPTER" --suite "$suite" --count-only
fi

if [[ -e "$results" ]]; then
  printf 'results path already exists: %s\n' "$results" >&2
  exit 2
fi

python3 "$ADAPTER" --suite "$suite" --output "$results"
{
  printf 'revision=%s\n' "$actual_revision"
  printf 'remote=%s\n' "$PINNED_URL"
  printf 'worktree=clean\n'
} >"$results/upstream-provenance.env"
(
  cd "$suite"
  git ls-files -z -- '*.fptest' | sort -z | xargs -0 sha256sum
) >"$results/upstream-files.sha256"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"
floatlib_test_lake build oracle
checker="$(floatlib_build_path bin/oracle)"

oracle_results="$results/oracle-results.tsv"
printf 'group\tcases\tstatus\tresult\tlog\n' >"$oracle_results"
failed=0

while IFS=$'\t' read -r group format operation rounding cases stream_file map_file; do
  if [[ "$group" == "group" ]]; then
    continue
  fi
  log="$results/$group.oracle.log"
  if "$checker" testfloat "$format" "$operation" "$rounding" "$maximum_reports" \
      <"$results/$stream_file" >"$log" 2>&1; then
    status=pass
  else
    status=fail
    failed=1
  fi
  result_line="$(grep '^RESULT ' "$log" | tail -1 || true)"
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$group" "$cases" "$status" "$result_line" "$(basename "$log")" >>"$oracle_results"
  printf '%-34s %s (%s cases)\n' "$group" "$status" "$cases"
done <"$results/groups.tsv"

printf 'IBM FPgen results: %s\n' "$results"
exit "$failed"
