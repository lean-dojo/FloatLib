#!/usr/bin/env bash
# Standard-suite driver: one suite after the other. No server or JavaScript tooling is used.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
if (( $# == 0 )); then
  printf 'Usage: benchmarks/suites/run.sh {fpbench|fpbench-tools|inequalities|correct-rounding|testfloat|selftest|capabilities}...\n'
  exit 2
fi
commit="$(git rev-parse HEAD)"
out="${FLOATLIB_SUITE_RESULTS:-$root/benchmarks/suites/results/$commit}"
mkdir -p "$out" "$out/tmp" "$out/cache"
export TMPDIR="$out/tmp" XDG_CACHE_HOME="$out/cache" PYTHONDONTWRITEBYTECODE=1
threads="${FLOATLIB_SUITE_THREADS:-8}"
export LEAN_NUM_THREADS="$threads" OMP_NUM_THREADS="$threads" OPENBLAS_NUM_THREADS="$threads" MKL_NUM_THREADS="$threads"
export FLOATLIB_BUILD_DIR="${FLOATLIB_BUILD_DIR:-$root/.lake/build}"
for suite in "$@"; do
  case "$suite" in fpbench|fpbench-tools|inequalities|correct-rounding|testfloat|selftest|capabilities) ;;
    *) printf 'Unknown suite: %s\n' "$suite" >&2; exit 2;; esac
done
# With FLOATLIB_SUITE_SLICE the driver checks the host's memory and CPU, and moves itself into a
# scope of that systemd user slice with a memory cap, at nice 19 and under an outer timeout.
slice="${FLOATLIB_SUITE_SLICE:-}"
if [[ -n "$slice" ]] && ! grep -qF "$slice" /proc/self/cgroup; then
  free -g | tee "$out/resources.txt"
  mpstat 5 1 | tee -a "$out/resources.txt"
  available="$(free -g | awk '/^Mem:/ {print $7}')"
  idle="$(awk '/^Average:/ && $2 == "all" {print $NF}' "$out/resources.txt")"
  if (( available < 400 )) || ! awk -v idle="$idle" 'BEGIN {exit !(idle >= 30)}'; then
    printf 'Resource gate refused launch: %s GB available, %s%% idle\n' "$available" "$idle"
    exit 75
  fi
  exec systemd-run --user --scope -q --slice="$slice" \
    -p MemoryMax="${FLOATLIB_SUITE_MEMORY:-16G}" -p MemorySwapMax=0 nice -n 19 \
    /usr/bin/time -v -o "$out/resources.time" \
    timeout --signal=TERM --kill-after=20 "${FLOATLIB_SUITE_JOB_TIMEOUT:-540}" \
    bash "$0" "$@"
fi
source tests/lib/lake.sh
for suite in "$@"; do
  mkdir -p "$out/$suite"
  if [[ "$suite" == correct-rounding || "$suite" == testfloat ]]; then
    python3 benchmarks/suites/configure.py
    if [[ "$suite" == testfloat ]]; then
      python3 benchmarks/testfloat/adapter.py
      target=suiteTestFloat
    else
      target=suiteCorrectRounding
    fi
    floatlib_lake_in "$root/benchmarks/suites" build "$target"
  fi
  if [[ "$suite" == fpbench-tools ]]; then
    floatlib_lake env python3 benchmarks/fpbench/tools.py "$out/$suite"
  elif [[ "$suite" == selftest || "$suite" == capabilities ]]; then
    floatlib_lake env python3 "benchmarks/suites/$suite.py" "$out/$suite"
  else
    floatlib_lake env python3 "benchmarks/$suite/run.py" "$out/$suite"
  fi
done
