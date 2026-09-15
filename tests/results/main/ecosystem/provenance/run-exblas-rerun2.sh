#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/exblas-rerun2"
work_dir=/work/exblas-rerun2
jobs=${JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=exblas\nattempt=3\nstarted=%s\nnode=%s\njobs=%s\n' \
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
  bash build-essential ca-certificates cmake curl git libgmp-dev libmpfr-dev \
  make time

# The pinned ExBLAS revision requires the pre-oneTBB API. Use Intel's last
# classic-TBB release rather than modifying ExBLAS to a different scheduler.
curl -fsSL \
  https://github.com/uxlfoundation/oneTBB/releases/download/v2020.3/tbb-2020.3-lin.tgz \
  -o "$work_dir/tbb.tgz"
tar -xzf "$work_dir/tbb.tgz" -C "$work_dir"
tbb_root="$work_dir/tbb"
tbb_lib="$tbb_root/lib/intel64/gcc4.8"
test -f "$tbb_root/include/tbb/task_scheduler_init.h"
test -f "$tbb_lib/libtbb.so"

git clone --no-tags https://github.com/riakymch/exblas.git "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  856130ebcfe906f519a623d57d1359e744e29042
test "$(git -C "$work_dir/src" rev-parse HEAD)" = \
  856130ebcfe906f519a623d57d1359e744e29042

export GMP_HOME=/usr
export MPFR_HOME=/usr
export CPATH="$tbb_root/include:${CPATH:-}"
export LIBRARY_PATH="$tbb_lib:${LIBRARY_PATH:-}"
export LD_LIBRARY_PATH="$tbb_lib:${LD_LIBRARY_PATH:-}"

# GCC 6 made narrowing diagnostics in the bundled 2012 VectorClass snapshot
# fatal. The historical code intentionally encodes bit masks this way.
cmake -S "$work_dir/src" -B "$work_dir/build" \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_CXX_FLAGS=-Wno-narrowing \
  -DEXBLAS_CPU=ON \
  -DEXBLAS_VS_MPFR=ON
cmake --build "$work_dir/build" --parallel "$jobs"

test_bin="$work_dir/build/src/cpu/blas1/test.exsum"
test -x "$test_bin"
{
  "$test_bin" 24
  "$test_bin" 24 2 0 n
  "$test_bin" 24 50 0 n
  "$test_bin" 24 1e+50 0 i
} | tee "$result_dir/exsum-tests.log"
test "$(grep -c 'ALL OK!' "$result_dir/exsum-tests.log")" -eq 4
