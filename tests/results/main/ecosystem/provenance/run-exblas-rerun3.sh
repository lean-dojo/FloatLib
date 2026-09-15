#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_name=${RESULT_NAME:-exblas-rerun3}
work_name=${WORK_NAME:-exblas-rerun3}
attempt=${ATTEMPT:-4}
result_dir="$campaign/results/$result_name"
work_dir="/work/$work_name"
jobs=${JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=exblas\nattempt=%s\nstarted=%s\nnode=%s\njobs=%s\n' \
  "$attempt" "$started" "${NODE_NAME:-unknown}" "$jobs" \
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
  bash build-essential ca-certificates cmake curl git libgmp-dev libmpfr-dev \
  make time

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

# The bundled 2012 VectorClass used unsigned hexadecimal literals as signed
# int template arguments. Modern C++ rejects those out-of-range arguments.
# Verify the exact old text before changing only the literal spelling to the
# identical signed bit patterns. The resulting Git diff is retained.
vector_i="$work_dir/src/src/common/vectori256.h"
vector_f="$work_dir/src/src/common/vectorf256.h"
test "$(grep -c 'constant8i<80000000,0xFFFFFFFF,80000000,0xFFFFFFFF,80000000,0xFFFFFFFF,80000000,0xFFFFFFFF>()' "$vector_i")" -eq 1
test "$(grep -c 'constant8f<0x80000000,0x80000000,0x80000000,0x80000000,0x80000000,0x80000000,0x80000000,0x80000000>' "$vector_f")" -eq 1
test "$(grep -c 'constant8f<0,0x80000000,0,0x80000000,0,0x80000000,0,0x80000000>' "$vector_f")" -eq 1
perl -pi -e \
  's/constant8i<80000000,0xFFFFFFFF,80000000,0xFFFFFFFF,80000000,0xFFFFFFFF,80000000,0xFFFFFFFF>\(\)/constant8i<80000000,-1,80000000,-1,80000000,-1,80000000,-1>()/' \
  "$vector_i"
perl -pi -e \
  's/constant8f<0x80000000,0x80000000,0x80000000,0x80000000,0x80000000,0x80000000,0x80000000,0x80000000>/constant8f<(-2147483647-1),(-2147483647-1),(-2147483647-1),(-2147483647-1),(-2147483647-1),(-2147483647-1),(-2147483647-1),(-2147483647-1)>/' \
  "$vector_f"
perl -pi -e \
  's/constant8f<0,0x80000000,0,0x80000000,0,0x80000000,0,0x80000000>/constant8f<0,(-2147483647-1),0,(-2147483647-1),0,(-2147483647-1),0,(-2147483647-1)>/' \
  "$vector_f"
# These old headers carry CRLF endings and spaces before the carriage return.
# Normalize only the three modified lines; sed sees the carriage return as
# part of the pattern space, unlike the earlier Perl line-ending expression.
sed -i \
  '/constant8i<80000000,-1,80000000,-1,80000000,-1,80000000,-1>/s/[[:space:]]*$//' \
  "$vector_i"
sed -i \
  '/constant8f<.*2147483647/s/[[:space:]]*$//' \
  "$vector_f"
git -C "$work_dir/src" diff --check
git -C "$work_dir/src" diff --binary >"$result_dir/applied-compatibility.patch"

export GMP_HOME=/usr
export MPFR_HOME=/usr
export CPATH="$tbb_root/include:${CPATH:-}"
export LIBRARY_PATH="$tbb_lib:${LIBRARY_PATH:-}"
export LD_LIBRARY_PATH="$tbb_lib:${LD_LIBRARY_PATH:-}"

cmake -S "$work_dir/src" -B "$work_dir/build" \
  -DCMAKE_BUILD_TYPE=Release \
  -DEXBLAS_CPU=ON \
  -DEXBLAS_VS_MPFR=ON
cmake --build "$work_dir/build" --parallel "$jobs"

test_bin="$work_dir/build/src/cpu/blas1/test.exsum"
test -x "$test_bin"

# The executable reports both the exact superaccumulator and several short
# floating-point expansions. Gate the property ExBLAS is designed to provide:
# exact-superaccumulator agreement with MPFR. Record the stricter composite
# verdict separately because the short expansions can lose information on the
# deliberately extreme exponent-spread workload.
printf 'case\texit_status\texact_superacc_mpfr\tall_expansions\n' \
  >"$result_dir/exsum-summary.tsv"
exact_failures=0
composite_passes=0
case_index=0
for arguments in \
  '24' \
  '24 2 0 n' \
  '24 50 0 n' \
  '24 1e+50 0 i'
do
  case_index=$((case_index + 1))
  case_log=$(printf '%s/exsum-case-%02d.log' "$result_dir" "$case_index")
  read -r -a argv <<<"$arguments"
  set +e
  "$test_bin" "${argv[@]}" >"$case_log" 2>&1
  case_status=$?
  set -e
  cat "$case_log"

  superacc=$(
    sed -n 's/^[[:space:]]*exsum with superacc = //p' "$case_log" | tail -1
  )
  mpfr=$(
    sed -n 's/^[[:space:]]*exsum with MPFR = //p' "$case_log" | tail -1
  )
  exact_result=fail
  if [[ -n "$superacc" && "$superacc" == "$mpfr" ]]; then
    exact_result=pass
  else
    exact_failures=$((exact_failures + 1))
  fi

  expansion_result=fail
  if grep -q 'ALL OK!' "$case_log"; then
    expansion_result=pass
    composite_passes=$((composite_passes + 1))
  fi
  printf '%s\t%s\t%s\t%s\n' \
    "$arguments" "$case_status" "$exact_result" "$expansion_result" \
    >>"$result_dir/exsum-summary.tsv"
done

printf 'exact_cases=4\nexact_failures=%s\ncomposite_passes=%s\n' \
  "$exact_failures" "$composite_passes" >"$result_dir/summary.env"
test "$exact_failures" -eq 0
