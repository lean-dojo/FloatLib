#!/usr/bin/env bash

# We compare our low-bit decoders with the actual published sources, not
# locally copied tables:
# ONNX float8: https://onnx.ai/onnx/technical/float8.html
# P3109 public tables: https://github.com/P3109/Public

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

p3109_revision="34f5964d9bb2382b2665d15467fc3517b990b308"
p3109_url="https://github.com/P3109/Public.git"
cache_root="${FORMAT_STANDARDS_CACHE_ROOT:-${TMPDIR:-/tmp}/floatlib-format-standards}"
results="${FORMAT_STANDARDS_RESULTS:-}"
if [[ -n "$results" && -e "$results" ]]; then
  printf 'results path already exists: %s\n' "$results" >&2
  exit 2
fi
maximum_width="${FORMAT_STANDARDS_P3109_MAX_WIDTH:-16}"
workers="${FORMAT_STANDARDS_WORKERS:-}"
cpu_set="${FORMAT_STANDARDS_CPU_SET:-none}"

if ! [[ "$maximum_width" =~ ^[0-9]+$ ]] ||
    ((maximum_width < 3 || maximum_width > 16)); then
  printf 'FORMAT_STANDARDS_P3109_MAX_WIDTH must be between 3 and 16: %s\n' \
    "$maximum_width" >&2
  exit 2
fi
if [[ "$cpu_set" != "none" ]]; then
  if ! command -v taskset >/dev/null 2>&1; then
    printf '%s\n' \
      'taskset is required for FORMAT_STANDARDS_CPU_SET; use "none" to disable affinity.' >&2
    exit 2
  fi
  if ! taskset -pc "$cpu_set" "$$" >/dev/null 2>&1; then
    printf 'invalid or unavailable FORMAT_STANDARDS_CPU_SET: %s\n' "$cpu_set" >&2
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
if ! [[ "$workers" =~ ^[1-9][0-9]*$ ]] ||
    ((${#workers} > ${#available_cpus})) ||
    ((workers > available_cpus)); then
  printf 'FORMAT_STANDARDS_WORKERS must be between 1 and %s inside the selected affinity: %s\n' \
    "$available_cpus" "$workers" >&2
  exit 2
fi

if ! python3 -c 'import onnx, numpy, matplotlib' >/dev/null 2>&1; then
  printf '%s\n' \
    'ONNX, NumPy, and Matplotlib are required for the low-bit reference report.' >&2
  exit 2
fi
if [[ -n "$results" ]]; then
  mkdir -p "$results"
else
  results="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-format-standards-results.XXXXXXXX")"
fi
mkdir -p "$cache_root"

p3109_source="$cache_root/p3109-public"
if [[ ! -d "$p3109_source/.git" ]]; then
  git clone --filter=blob:none "$p3109_url" "$p3109_source"
fi
git -C "$p3109_source" fetch --depth 1 origin "$p3109_revision"
git -C "$p3109_source" checkout --detach "$p3109_revision"
if [[ "$(git -C "$p3109_source" rev-parse HEAD)" != "$p3109_revision" ]]; then
  printf '%s\n' 'P3109 checkout revision mismatch' >&2
  exit 2
fi
p3109_status="$(
  git -C "$p3109_source" status \
    --porcelain=v1 --untracked-files=all --ignored=matching
)"
if [[ -n "$p3109_status" ]]; then
  printf 'P3109 checkout is not completely clean: %s\n' "$p3109_source" >&2
  printf '%s\n' "$p3109_status" >&2
  exit 2
fi

floatlib_test_lake build oracle
emitter="$(floatlib_build_path bin/oracle)"

summary="$results/summary.csv"
printf '%s\n' 'oracle,status,formats,cases,mismatches' >"$summary"
python3 "$root/tests/oracles/reference_oracles.py" \
  --emitter "$emitter" onnx |
  tee -a "$summary"

p3109_shards="$results/p3109-shards"
mkdir "$p3109_shards"
export emitter maximum_width p3109_shards p3109_source root
seq 3 "$maximum_width" |
  xargs -P "$workers" -n 1 bash -c '
    width="$1"
    python3 "$root/tests/oracles/reference_oracles.py" \
      --emitter "$emitter" p3109 \
      --source "$p3109_source" \
      --minimum-width "$width" \
      --maximum-width "$width" >"$p3109_shards/$width.csv"
  ' _
awk -F, '
  {
    formats += $3
    cases += $4
    mismatches += $5
  }
  END {
    status = mismatches == 0 ? "pass" : "fail"
    printf "P3109 4.0.3 value tables,%s,%d,%d,%d\n",
      status, formats, cases, mismatches
  }
' "$p3109_shards"/*.csv | tee -a "$summary"

python3 - "$summary" "$results/summary.md" <<'PY'
import csv
import sys

source, destination = sys.argv[1:]
with open(source, newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream))
with open(destination, "w", encoding="utf-8") as stream:
    stream.write("| Oracle | Status | Formats | Cases | Mismatches |\n")
    stream.write("| --- | ---: | ---: | ---: | ---: |\n")
    for row in rows:
        stream.write(
            f"| {row['oracle']} | {row['status']} | "
            f"{int(row['formats']):,} | {int(row['cases']):,} | "
            f"{int(row['mismatches']):,} |\n"
        )
PY

python3 "$root/tests/oracles/conformance_plot.py" \
  "$summary" \
  "$results/conformance" \
  --group-column oracle \
  --group-label 'oracle=Independent oracle' \
  --cases-column cases \
  --mismatch-column mismatches \
  --status-column status \
  --title 'Published low-bit format conformance' \
  --subtitle "ONNX formats and P3109 tables through width $maximum_width"

{
  printf 'timestamp_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'lean_revision=%s\n' "$(git rev-parse HEAD)"
  printf 'p3109_revision=%s\n' "$p3109_revision"
  printf 'onnx_version=%s\n' "$(python3 -c 'import onnx; print(onnx.__version__)')"
  printf 'numpy_version=%s\n' "$(python3 -c 'import numpy; print(numpy.__version__)')"
  printf 'p3109_maximum_width=%s\n' "$maximum_width"
  printf 'workers=%s\n' "$workers"
  printf 'cpu_set=%s\n' "$cpu_set"
  printf 'worktree_diff_sha256=%s\n' "$(
    git diff --binary HEAD | sha256sum | awk '{print $1}'
  )"
} >"$results/metadata.txt"
git status --short >"$results/worktree-status.txt"

cat "$results/summary.md"
printf 'results=%s\n' "$results"
