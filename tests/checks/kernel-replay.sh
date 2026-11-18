#!/usr/bin/env bash

# Replay every declaration of the library in Lean's kernel, one module per process.
#
# usage: tests/checks/kernel-replay.sh [MODULE-PREFIX...]
#
# For every library module (every `.lean` file under `FloatLib/` and `FloatLib.lean`, or those
# whose name starts with a given prefix) this starts `tests/checks/KernelReplay.lean`, which
# checks the constants the compiled module adds once more with the kernel, in the environment of
# its imports. The library has to be built. KERNEL_REPLAY_JOBS processes run at a time (default
# 4); one process needs up to 6 GB, and the whole library takes about an hour of processor time
# (four minutes with sixteen processes on a 96-thread machine).

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

jobs="${KERNEL_REPLAY_JOBS:-4}"
work="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-replay.XXXXXX")"
trap 'rm -rf -- "$work"' EXIT

{
  echo FloatLib
  find FloatLib -name '*.lean' | sed -e 's/\.lean$//' -e 's|/|.|g'
} | LC_ALL=C sort > "$work/all"
if (( $# > 0 )); then
  for prefix in "$@"; do
    grep -E "^${prefix//./\\.}(\\.|\$)" "$work/all" || true
  done | LC_ALL=C sort -u > "$work/modules"
else
  cp "$work/all" "$work/modules"
fi
count="$(wc -l < "$work/modules")"
(( count > 0 )) || { printf 'kernel replay: no module matches %s\n' "$*" >&2; exit 1; }
printf 'kernel replay: %s modules, %s at a time\n' "$count" "$jobs"

export REPLAY_SCRIPT="$ROOT/tests/checks/KernelReplay.lean" REPLAY_WORK="$work"
floatlib_lake env xargs -a "$work/modules" -P "$jobs" -I{} sh -c '
  if lean --run "$REPLAY_SCRIPT" "$1" > "$REPLAY_WORK/$1.out" 2>&1; then
    cat "$REPLAY_WORK/$1.out" >> "$REPLAY_WORK/passed"
  else
    { printf "FAILED %s\n" "$1"; sed "s/^/    /" "$REPLAY_WORK/$1.out"; } >> "$REPLAY_WORK/failed"
  fi' sh {} || true

passed=0
[[ -f "$work/passed" ]] && passed="$(grep -c '^replayed ' "$work/passed" || true)"
constants=0
[[ -f "$work/passed" ]] && constants="$(awk '/^replayed / { sum += $(NF - 1) } END { print sum + 0 }' "$work/passed")"
if [[ -f "$work/failed" ]]; then
  cat "$work/failed" >&2
  printf 'kernel replay failed: %s of %s modules replayed\n' "$passed" "$count" >&2
  exit 1
fi
[[ "$passed" -eq "$count" ]] || { printf 'kernel replay: %s of %s modules reported\n' "$passed" "$count" >&2; exit 1; }
printf 'kernel replay passed: %s modules, %s constants\n' "$passed" "$constants"
