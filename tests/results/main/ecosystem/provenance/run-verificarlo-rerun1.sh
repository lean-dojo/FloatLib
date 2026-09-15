#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/verificarlo-rerun1"
work_dir=/work/verificarlo-rerun1
jobs=${JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=verificarlo\nattempt=2\nstarted=%s\nnode=%s\njobs=%s\n' \
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
  autoconf automake autogen autotools-dev bash binutils bison build-essential \
  bzip2 ca-certificates clang-18 curl cython3 flex gcc-13 g++-13 git \
  libclang-rt-18-dev libedit-dev libmpfr-dev libomp-18-dev libtool libz-dev \
  llvm-18 llvm-18-dev make npm parallel python3 python3-pip python3-venv

npm install -g @bazel/bazelisk
python3 -m venv "$work_dir/venv"
source "$work_dir/venv/bin/activate"
python -m pip install --upgrade pip uv

git clone --no-tags https://github.com/verificarlo/verificarlo.git \
  "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  c5d1bf798a5ec617c138aa5e6629e1923411d3c8
test "$(git -C "$work_dir/src" rev-parse HEAD)" = \
  c5d1bf798a5ec617c138aa5e6629e1923411d3c8

cd "$work_dir/src"
git submodule update --init --recursive

# Configure and the test Makefiles invoke unversioned clang/clang++. Put the
# selected LLVM toolchain first instead of relying on Ubuntu's alternatives.
export PATH="/usr/lib/llvm-18/bin:$PATH"
clang --version
clang++ --version

./autogen.sh
CC=gcc-13 CXX=g++-13 ./configure \
  --with-llvm="$(llvm-config --prefix)" --without-flang
make -j"$jobs" install-interflop-stdlib
make -j"$jobs"
make install

# The first run installed the VPREC backend but tested before the dynamic
# loader knew about /usr/local/lib. Register it and keep the path explicit.
ldconfig
export LD_LIBRARY_PATH="/usr/local/lib:/usr/local/lib64:${LD_LIBRARY_PATH:-}"
ldconfig -p | grep libinterflop_vprec
command -v clang
command -v verificarlo

make installcheck
