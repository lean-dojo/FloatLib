#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
variant=${FLIT_VARIANT:?FLIT_VARIANT must be base, openmpi, or mpich}
result_dir="$campaign/results/flit-$variant-rerun1"
work_dir="/work/flit-$variant-rerun1"

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=flit\nvariant=%s\nstarted=%s\nnode=%s\n' \
  "$variant" "$started" "${NODE_NAME:-unknown}" > "$result_dir/metadata.env"

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
  bash bash-completion binutils build-essential ca-certificates clang \
  coreutils git hostname make python3 python3-dev python3-pip \
  python3-setuptools python3-toml sqlite3

case "$variant" in
  base) ;;
  openmpi)
    apt-get install -y --no-install-recommends libopenmpi-dev openmpi-bin
    ;;
  mpich)
    apt-get install -y --no-install-recommends libmpich-dev mpich
    ;;
  *)
    printf 'unknown FLiT variant: %s\n' "$variant" >&2
    exit 2
    ;;
esac

git clone --no-tags https://github.com/PRUNERS/FLiT.git "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  27b6061b9d2302fa8c3252fe770287bb4d07905b
test "$(git -C "$work_dir/src" rev-parse HEAD)" = \
  27b6061b9d2302fa8c3252fe770287bb4d07905b

cd "$work_dir/src"
python3 --version
g++ --version
clang++ --version
python3 - <<'PY'
import setuptools
import toml

print("setuptools:", setuptools.__version__)
print("toml:", toml.__version__)
PY

# Upstream CI builds test programs in parallel but runs the stateful test
# harness serially. Parallelizing `make check` races installation fixtures.
make -C tests -j"$(nproc)" build
make check

make install PREFIX="$work_dir/install"
export PATH="$work_dir/install/bin:$PATH"
flit --version

mkdir -p "$work_dir/litmus"
cd "$work_dir/litmus"
flit init --litmus-tests
make -j"$(nproc)"
make run
