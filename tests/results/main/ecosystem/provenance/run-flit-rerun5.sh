#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
variant=${FLIT_VARIANT:?FLIT_VARIANT must be base, openmpi, or mpich}
result_dir="$campaign/results/flit-$variant-rerun5"
work_dir="/work/flit-$variant-rerun5"

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

# We use FLiT's own build and test sequence before installing its command-line
# tool. That keeps this qualification tied to the upstream project rather than
# to a smaller local substitute.
make -C tests -j"$(nproc)" build
make check

make install PREFIX="$work_dir/install"
export PATH="$work_dir/install/bin:$PATH"
flit --version

mkdir -p "$work_dir/litmus"
cd "$work_dir/litmus"
flit init --litmus-tests

# The generated configuration mentions Intel's compiler, which is not present
# in this image. We keep every GCC and Clang configuration that can actually
# run. Timing is disabled because this campaign checks numerical variation
# across compiler choices; it is not a compiler-speed benchmark.
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

# FLiT gives each generated configuration its own files, so compilation and
# comparison can safely share this node.
make -j"$(nproc)"
make -j"${FLIT_RUN_JOBS:-32}" run

shopt -s nullglob
binaries=(bin/*)
comparisons=(results/*-out-comparison.csv)
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
for comparison in "${comparisons[@]}"; do
  if [[ ! -s "$comparison" ]]; then
    printf 'FLiT produced an empty comparison CSV: %s\n' "$comparison" >&2
    exit 1
  fi
done

# In FLiT's generated Makefile, `*-out` is an intermediate prerequisite of
# `*-out-comparison.csv`; GNU Make removes that intermediate after success.
# FLiT's own documentation imports the final CSVs, so those CSVs and the
# resulting SQLite database are the durable artifacts we retain.
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
printf 'configurations=%s\ncomparison_csvs=%s\nimported_database=%s\n' \
  "${#binaries[@]}" "${#comparisons[@]}" "1" \
  >"$result_dir/summary.env"
ls -la >"$result_dir/litmus-files.txt"
