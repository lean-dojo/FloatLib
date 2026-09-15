#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/exblas-rerun1"
work_dir=/work/exblas-rerun1
jobs=${JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=exblas\nattempt=2\nstarted=%s\nnode=%s\njobs=%s\n' \
  "$started" "${NODE_NAME:-unknown}" "$jobs" > "$result_dir/metadata.env"

finish() {
  status=$?
  finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
    | tee "$result_dir/status.env"
  exit "$status"
}
trap finish EXIT

# ExBLAS vendors a 2012 VectorClass snapshot and uses TBB's removed
# task_scheduler_init API. Reproduce its documented-era toolchain instead of
# patching the benchmark source.
sed -i \
  -e 's|archive.ubuntu.com|old-releases.ubuntu.com|g' \
  -e 's|security.ubuntu.com|old-releases.ubuntu.com|g' \
  /etc/apt/sources.list
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends \
  bash build-essential ca-certificates cmake g++-5 gcc-5 git libgmp-dev \
  libmpfr-dev libtbb-dev make time

git clone --no-tags https://github.com/riakymch/exblas.git "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  856130ebcfe906f519a623d57d1359e744e29042
test "$(git -C "$work_dir/src" rev-parse HEAD)" = \
  856130ebcfe906f519a623d57d1359e744e29042

export CC=gcc-5
export CXX=g++-5
export GMP_HOME=/usr
export MPFR_HOME=/usr

cmake -S "$work_dir/src" -B "$work_dir/build" \
  -DCMAKE_BUILD_TYPE=Release \
  -DEXBLAS_CPU=ON \
  -DEXBLAS_VS_MPFR=ON
cmake --build "$work_dir/build" -- -j"$jobs"

test_bin="$work_dir/build/src/cpu/blas1/test.exsum"
test -x "$test_bin"
{
  "$test_bin" 24
  "$test_bin" 24 2 0 n
  "$test_bin" 24 50 0 n
  "$test_bin" 24 1e+50 0 i
} | tee "$result_dir/exsum-tests.log"
test "$(grep -c 'ALL OK!' "$result_dir/exsum-tests.log")" -eq 4
