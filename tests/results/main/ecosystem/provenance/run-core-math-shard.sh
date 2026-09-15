#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
shard_index=${SHARD_INDEX:?SHARD_INDEX is required}
shard_count=${SHARD_COUNT:?SHARD_COUNT is required}
result_prefix=${RESULT_PREFIX:-core-math-shard}
suite="$result_prefix-$shard_index"
result_dir="$campaign/results/$suite"
work_dir="/work/$suite"

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=%s\nstarted=%s\nnode=%s\nshard_index=%s\nshard_count=%s\n' \
  "$suite" "$started" "${NODE_NAME:-unknown}" "$shard_index" "$shard_count" \
  > "$result_dir/metadata.env"

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

mapfile -t makefiles < <(
  find src/binary16 src/binaryb16 src/binary32 src/binary64 \
    -mindepth 2 -maxdepth 2 -name Makefile -type f \
    | sort \
    | awk -v shard="$shard_index" -v count="$shard_count" \
        '((NR - 1) % count) == shard'
)

printf 'assigned_functions=%s\n' "${#makefiles[@]}" \
  >> "$result_dir/metadata.env"
: > "$result_dir/functions.tsv"

failures=0
for makefile in "${makefiles[@]}"; do
  function=$(awk -F':=' \
    '/^FUNCTION_UNDER_TEST[[:space:]]*:=[[:space:]]*/ {
      gsub(/[[:space:]]/, "", $2); print $2; exit
    }' "$makefile")
  [ -n "$function" ] || continue
  family=${makefile#src/}
  family=${family%%/*}
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
  "${#makefiles[@]}" "$failures" > "$result_dir/summary.env"
test "$failures" -eq 0
