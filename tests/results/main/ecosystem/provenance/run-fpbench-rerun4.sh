#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/fpbench-rerun4"
work_dir=/work/fpbench-rerun4

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=fpbench\nattempt=5\nstarted=%s\nnode=%s\n' \
  "$started" "${NODE_NAME:-unknown}" > "$result_dir/metadata.env"

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
  bash build-essential ca-certificates curl gcc g++ gfortran git \
  libc-bin libmpfr6 libmpfr-dev nodejs ocaml-nox python3 time z3

installer=/tmp/racket-9.3.sh
curl -fsSL \
  https://download.racket-lang.org/installers/9.3/racket-9.3-x86_64-linux-cs.sh \
  -o "$installer"
bash "$installer" --unix-style --dest /opt/racket --create-dir
export PATH="/opt/racket/bin:$PATH"
test "$(racket --version)" = 'Welcome to Racket v9.3 [cs].'

git clone --no-tags --filter=blob:none \
  https://github.com/FPBench/FPBench.git "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  a6621d5f86276859bc01cc7b9c238dee73ff5dbe
test "$(git -C "$work_dir/src" rev-parse HEAD)" = \
  a6621d5f86276859bc01cc7b9c238dee73ff5dbe

git clone --no-tags https://github.com/herbie-fp/generic-flonum.git \
  "$work_dir/generic-flonum"
git -C "$work_dir/generic-flonum" checkout --detach \
  e2226376ed7b9bb543ec21606327d52e4077818a
test "$(git -C "$work_dir/generic-flonum" rev-parse HEAD)" = \
  e2226376ed7b9bb543ec21606327d52e4077818a

export PLTUSERHOME="$work_dir/racket-home"
cd "$work_dir/src"
raco pkg install --no-docs --auto --name generic-flonum \
  "$work_dir/generic-flonum"
raco pkg install --no-docs --deps fail --name fpbench "$work_dir/src"

# These are the maintained targets exercised by FPBench's own workflow at the
# pinned revision. In particular, `filter-test` currently invokes the
# evaluator test; we run it exactly as upstream does and audit the standalone
# filter script separately below.
make raco-test
make export-test transform-test toolserver-test evaluate-test filter-test tensor-test
make c-sanity c-test
make smtlib2-sanity smtlib2-test
make python-sanity python-test

set +e
tests/scripts/test-filter.sh >"$result_dir/filter-standalone.log" 2>&1
filter_status=$?
set -e

cp tests/scripts/test-filter.out.txt "$result_dir/filter.expected.raw.txt"
printf 'upstream_ci_targets=pass\nstandalone_filter_status=%s\n' \
  "$filter_status" >"$result_dir/outcome.env"

cat >"$result_dir/README.txt" <<'EOF'
The pinned FPBench workflow target named `filter-test` calls
`test-evaluate.sh`, not `test-filter.sh`. The maintained workflow targets
passed. We also ran the standalone filter script so this archive does not hide
that discrepancy; its raw status and output are recorded in outcome.env and
filter-standalone.log.
EOF

printf 'fpbench_revision=%s\ngeneric_flonum_revision=%s\nracket=%s\n' \
  "$(git rev-parse HEAD)" \
  "$(git -C "$work_dir/generic-flonum" rev-parse HEAD)" \
  "$(racket --version)" >"$result_dir/versions.env"
printf '%s\n' benchmarks/*.fpcore | wc -l \
  >"$result_dir/fpcore-benchmark-count.txt"
