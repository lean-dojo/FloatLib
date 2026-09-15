#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
variant=${FLIT_VARIANT:?FLIT_VARIANT must be base, openmpi, or mpich}
result_dir="$campaign/results/flit-$variant-rerun4"
work_dir="/work/flit-$variant-rerun4"

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=flit\nvariant=%s\nstarted=%s\nnode=%s\n' \
  "$variant" "$started" "${NODE_NAME:-unknown}" >"$result_dir/metadata.env"

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
    export OMPI_ALLOW_RUN_AS_ROOT=1
    export OMPI_ALLOW_RUN_AS_ROOT_CONFIRM=1
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

# FLiT builds its test programs in parallel, then runs the project checks
# before installing the command-line tool.
make -C tests -j"$(nproc)" build
make check

make install PREFIX="$work_dir/install"
export PATH="$work_dir/install/bin:$PATH"
flit --version

mkdir -p "$work_dir/litmus"
cd "$work_dir/litmus"
flit init --litmus-tests

# The generated file lists Intel's compiler even though this image does not
# provide it. We keep the GCC and Clang configurations that can actually run.
# Timing is off because this campaign checks numerical variability, not speed.
python3 - "$variant" <<'PY'
from pathlib import Path
import sys
import toml

variant = sys.argv[1]
path = Path("flit-config.toml")
config = toml.loads(path.read_text())
config["compiler"] = [
    compiler for compiler in config["compiler"]
    if compiler["binary"] in {"g++", "clang++"}
]
config["run"]["enable_mpi"] = variant != "base"
config["run"]["timing"] = False
path.write_text(toml.dumps(config))
PY

flit update
cp flit-config.toml "$result_dir/flit-config.toml"

# Each generated configuration writes its own files, so these runs can share
# the node safely. They do not produce timing measurements.
make -j"$(nproc)"
make -j"${FLIT_RUN_JOBS:-32}" run

shopt -s nullglob
binaries=(bin/*)
comparisons=(results/*-out-comparison.csv)
raw_outputs=(results/*-out)
expected_configurations=140

if ((${#binaries[@]} != expected_configurations)); then
  printf 'FLiT configuration count differs: expected %s, found %s\n' \
    "$expected_configurations" "${#binaries[@]}" >&2
  exit 1
fi
if ((${#comparisons[@]} != expected_configurations)); then
  printf 'FLiT comparison count differs: expected %s, found %s\n' \
    "$expected_configurations" "${#comparisons[@]}" >&2
  exit 1
fi
if ((${#raw_outputs[@]} != expected_configurations)); then
  printf 'FLiT raw-output count differs: expected %s, found %s\n' \
    "$expected_configurations" "${#raw_outputs[@]}" >&2
  exit 1
fi

# FLiT writes CSV results first. Importing them creates the database used by
# its reporting tools and gives us another artifact we can validate.
flit import --label "FloatLean $variant qualification" "${comparisons[@]}"
test "$(sqlite3 results.sqlite 'PRAGMA integrity_check;')" = "ok"

cp results.sqlite "$result_dir/results.sqlite"
cp -R --no-preserve=ownership results "$result_dir/results"
sqlite3 results.sqlite '.tables' >"$result_dir/sqlite-tables.txt"
sqlite3 results.sqlite '.schema' >"$result_dir/sqlite-schema.sql"
sqlite3 results.sqlite \
  "SELECT name FROM sqlite_master WHERE type = 'table' ORDER BY name;" \
  >"$result_dir/sqlite-table-names.txt"
grep -Fxq runs "$result_dir/sqlite-table-names.txt"
grep -Fxq tests "$result_dir/sqlite-table-names.txt"
printf 'flit_revision=%s\nvariant=%s\n' \
  "$(git -C "$work_dir/src" rev-parse HEAD)" "$variant" \
  >"$result_dir/versions.env"
printf 'configurations=%s\ncomparisons=%s\nraw_outputs=%s\n' \
  "${#binaries[@]}" "${#comparisons[@]}" "${#raw_outputs[@]}" \
  >"$result_dir/summary.env"
ls -la >"$result_dir/litmus-files.txt"
