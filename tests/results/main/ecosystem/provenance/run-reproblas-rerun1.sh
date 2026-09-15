#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/reproblas-rerun1"
work_dir=/work/reproblas-rerun1
jobs=${JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=reproblas\nattempt=2\nstarted=%s\nnode=%s\njobs=%s\n' \
  "$started" "${NODE_NAME:-unknown}" "$jobs" > "$result_dir/metadata.env"

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
  bash build-essential ca-certificates git make perl python3.10 time

git clone --no-tags https://github.com/peterahrens/ReproBLAS.git \
  "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  dfb815058dd34b88caba2513cce63bc2e89f951f
test "$(git -C "$work_dir/src" rev-parse HEAD)" = \
  dfb815058dd34b88caba2513cce63bc2e89f951f

cd "$work_dir/src"
python3.10 --version

make PYTHON=python3.10 update
make -j"$jobs" PYTHON=python3.10
make PYTHON=python3.10 check
make PYTHON=python3.10 bench

# Upstream's current accuracy target references removed test classes. Run it
# for an auditable result, but do not turn that independent harness defect into
# a false library failure.
set +e
make PYTHON=python3.10 acc > "$result_dir/accuracy-target.log" 2>&1
acc_status=$?
set -e
printf 'accuracy_target_status=%s\n' "$acc_status" \
  > "$result_dir/component-status.env"
