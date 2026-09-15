#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
worker_index=${WORKER_INDEX:?WORKER_INDEX is required}
worker_count=${WORKER_COUNT:?WORKER_COUNT is required}
suite="core-math-rerun1-resume2-$worker_index"
result_dir="$campaign/results/$suite"
work_dir="/work/$suite"

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=%s\nstarted=%s\nnode=%s\nworker_index=%s\nworker_count=%s\n' \
  "$suite" "$started" "${NODE_NAME:-unknown}" "$worker_index" "$worker_count" \
  >"$result_dir/metadata.env"

finish() {
  status=$?
  finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
    | tee "$result_dir/status.env"
  exit "$status"
}
trap finish EXIT

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends \
  bash build-essential ca-certificates clang curl gcc g++ git \
  libgmp-dev libmpfr-dev libomp-dev make

git clone --no-tags https://gitlab.inria.fr/core-math/core-math.git \
  "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  68b034fbe9512781352d28f2dc9795c1686fe8e9
git -C "$work_dir/src" rev-parse HEAD

cd "$work_dir/src"
export OMP_NUM_THREADS="${CPU_LIMIT:-180}"

# The first campaign and its first continuation append a row only after a
# function finishes. We use every such row as a checkpoint, then redistribute
# only the functions that still have no completed result.
completed_rows="$work_dir/completed-rows.tsv"
: >"$completed_rows"
for prior in \
  "$campaign"/results/core-math-rerun1-shard-*/functions.tsv \
  "$campaign"/results/core-math-rerun1-resume-*/functions.tsv; do
  [ -f "$prior" ] || continue
  awk -F '\t' 'NF >= 3 { print $1 "\t" $2 "\t" $3 }' "$prior" \
    >>"$completed_rows"
done

python3 - "$completed_rows" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
outcomes = {}
for line_number, line in enumerate(path.read_text().splitlines(), start=1):
    family, function, status = line.split("\t")
    key = (family, function)
    previous = outcomes.setdefault(key, status)
    if previous != status:
        raise SystemExit(
            f"conflicting checkpoint at line {line_number}: "
            f"{key} has {previous!r} and {status!r}"
        )
path.write_text(
    "".join(
        f"{family}\t{function}\t{outcomes[(family, function)]}\n"
        for family, function in sorted(outcomes)
    )
)
PY

completed_keys="$work_dir/completed-keys.tsv"
cut -f1-2 "$completed_rows" >"$completed_keys"

remaining="$work_dir/remaining.tsv"
: >"$remaining"
while IFS= read -r makefile; do
  function=$(awk -F':=' \
    '/^FUNCTION_UNDER_TEST[[:space:]]*:=[[:space:]]*/ {
      gsub(/[[:space:]]/, "", $2); print $2; exit
    }' "$makefile")
  [ -n "$function" ] || continue
  family=${makefile#src/}
  family=${family%%/*}
  if ! grep -Fqx "$family	$function" "$completed_keys"; then
    printf '%s\t%s\t%s\n' "$family" "$function" "$makefile" >>"$remaining"
  fi
done < <(
  find src/binary16 src/binaryb16 src/binary32 src/binary64 \
    -mindepth 2 -maxdepth 2 -name Makefile -type f \
    | sort
)

completed_count=$(wc -l <"$completed_rows")
remaining_count=$(wc -l <"$remaining")
if ((completed_count + remaining_count != 169)); then
  printf 'CORE-MATH function inventory differs: %s complete + %s remaining\n' \
    "$completed_count" "$remaining_count" >&2
  exit 1
fi

mapfile -t assigned < <(
  awk -F '\t' -v worker="$worker_index" -v count="$worker_count" \
    '((NR - 1) % count) == worker' "$remaining"
)

printf 'completed_before_resume=%s\nremaining_before_resume=%s\nassigned_functions=%s\n' \
  "$completed_count" "$remaining_count" "${#assigned[@]}" \
  >>"$result_dir/metadata.env"
: >"$result_dir/functions.tsv"

failures=0
for row in "${assigned[@]}"; do
  IFS=$'\t' read -r family function makefile <<<"$row"
  if timeout 90m ./check.sh "$function"; then
    printf '%s\t%s\tPASS\n' "$family" "$function" \
      | tee -a "$result_dir/functions.tsv"
  else
    code=$?
    printf '%s\t%s\tFAIL(%s)\n' "$family" "$function" "$code" \
      | tee -a "$result_dir/functions.tsv"
    failures=$((failures + 1))
  fi
done

printf 'functions=%s\nfailures=%s\n' \
  "${#assigned[@]}" "$failures" >"$result_dir/summary.env"
test "$failures" -eq 0
