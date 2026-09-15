#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/verificarlo-rerun2"
work_dir=/work/verificarlo-rerun2
revision=c5d1bf798a5ec617c138aa5e6629e1923411d3c8
build_jobs=${BUILD_JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=verificarlo\nattempt=3\nstarted=%s\nnode=%s\nbuild_jobs=%s\n' \
  "$started" "${NODE_NAME:-unknown}" "$build_jobs" \
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
  autoconf automake autogen autotools-dev bash binutils bzip2 ca-certificates \
  clang-18 curl cython3 flang-18 gcc-13 g++-13 git libclang-rt-18-dev \
  libedit-dev libmpfr-dev libomp5-18 libomp-18-dev libtool libz-dev \
  llvm-18 llvm-18-dev make npm parallel python3 python3-dev python3-pip tzdata

update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-13 30
update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-13 30
update-alternatives --install /usr/bin/clang clang /usr/bin/clang-18 30
update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-18 30
if [[ -x /usr/bin/flang-18 ]]; then
  update-alternatives --install /usr/bin/flang flang /usr/bin/flang-18 30
elif [[ -x /usr/bin/flang-new-18 ]]; then
  update-alternatives --install /usr/bin/flang flang /usr/bin/flang-new-18 30
fi
update-alternatives \
  --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-18 30

npm install -g @bazel/bazelisk

git clone --no-tags --filter=blob:none \
  https://github.com/verificarlo/verificarlo.git "$work_dir/src"
git -C "$work_dir/src" checkout --detach "$revision"
test "$(git -C "$work_dir/src" rev-parse HEAD)" = "$revision"

cd "$work_dir/src"
git submodule update --init --recursive

cp Dockerfile "$result_dir/upstream-Dockerfile"
cp .github/workflows/docker-ci.yml "$result_dir/upstream-docker-ci.yml"

flang_option=--without-flang
if [[ -x /usr/lib/llvm-18/bin/flang ]]; then
  flang_option=--with-flang=/usr/lib/llvm-18/bin/flang
elif [[ -x /usr/lib/llvm-18/bin/flang-new ]]; then
  flang_option=--with-flang=/usr/lib/llvm-18/bin/flang-new
fi

./autogen.sh
./configure \
  --with-llvm="$(llvm-config-18 --prefix)" \
  "$flang_option"
cp config.log "$result_dir/config.log"

make -j"$build_jobs" install-interflop-stdlib
make -j"$build_jobs"
make install
ldconfig

# Verificarlo's stochastic tests size GNU Parallel from `nproc`. The release
# campaign reserves a large node for a clean environment, but the upstream CI
# runner exposes only a small CPU set. Restrict the test process to four CPUs
# so this rerun follows that part of the upstream protocol instead of launching
# 180 simultaneous stochastic comparisons.
test_cpu_list="$(
  python3 - <<'PY'
from pathlib import Path

raw = Path("/sys/fs/cgroup/cpuset.cpus.effective").read_text().strip()
cpus = []
for piece in raw.split(","):
    if "-" in piece:
        start, stop = map(int, piece.split("-", 1))
        cpus.extend(range(start, stop + 1))
    elif piece:
        cpus.append(int(piece))
if len(cpus) < 4:
    raise SystemExit(f"need four assigned CPUs, found {raw!r}")
print(",".join(map(str, cpus[:4])))
PY
)"
printf 'assigned_cpuset=%s\ntest_cpu_list=%s\n' \
  "$(cat /sys/fs/cgroup/cpuset.cpus.effective)" "$test_cpu_list" \
  >>"$result_dir/metadata.env"

{
  printf 'revision=%s\n' "$revision"
  printf 'gcc=%s\n' "$(gcc --version | head -n 1)"
  printf 'clang=%s\n' "$(clang --version | head -n 1)"
  printf 'llvm_config=%s\n' "$(llvm-config --version)"
  printf 'flang=%s\n' "$(flang --version | head -n 1)"
  printf 'python=%s\n' "$(python3 --version)"
  printf 'parallel=%s\n' "$(parallel --version | head -n 1)"
  printf 'uv=%s\n' "$(command -v uv || printf absent)"
} >"$result_dir/versions.env"

set +e
taskset --cpu-list "$test_cpu_list" \
  make installcheck 2>&1 | tee "$result_dir/installcheck.log"
installcheck_status=${PIPESTATUS[0]}
set -e

printf 'installcheck_status=%s\n' "$installcheck_status" \
  >"$result_dir/outcome.env"

if [[ "$installcheck_status" -ne 0 ]]; then
  set +e
  taskset --cpu-list "$test_cpu_list" bash -lc \
    'cd /work/verificarlo-rerun2/src/tests/test_newton_vprec && bash -x ./test.sh' \
    2>&1 | tee "$result_dir/newton-vprec.log"
  newton_status=${PIPESTATUS[0]}
  set -e
  printf 'newton_vprec_status=%s\n' "$newton_status" \
    >>"$result_dir/outcome.env"
fi

exit "$installcheck_status"
