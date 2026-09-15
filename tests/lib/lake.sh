#!/usr/bin/env bash

# Shared Lake invocation for repository scripts.
#
# Source files and durable results remain in the checkout. Compiler artifacts use a per-worktree
# directory under the system temporary directory by default; callers may select another location
# with FLOATLIB_BUILD_DIR.

FLOATLIB_ROOT="$(
  cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd
)"
FLOATLIB_WORKTREE_KEY="$(
  printf '%s' "$FLOATLIB_ROOT" | cksum | awk '{print $1}'
)"
FLOATLIB_BUILD_DIR="${FLOATLIB_BUILD_DIR:-${TMPDIR:-/tmp}/floatlib-build-$FLOATLIB_WORKTREE_KEY}"
if [[ "$FLOATLIB_BUILD_DIR" != /* ]]; then
  FLOATLIB_BUILD_DIR="$FLOATLIB_ROOT/$FLOATLIB_BUILD_DIR"
fi
FLOATLIB_BUILD_DIR="${FLOATLIB_BUILD_DIR%/}"
export FLOATLIB_BUILD_DIR
FLOATLIB_BUILD_LOCK="${FLOATLIB_BUILD_DIR}.lock"

floatlib_acquire_build_lock() {
  local owner=""
  local reported=0

  mkdir -p "$(dirname "$FLOATLIB_BUILD_LOCK")"
  until ln -s "$$" "$FLOATLIB_BUILD_LOCK" 2>/dev/null; do
    owner="$(readlink "$FLOATLIB_BUILD_LOCK" 2>/dev/null || true)"
    if [[ "$owner" =~ ^[0-9]+$ ]] && ! kill -0 "$owner" 2>/dev/null; then
      if [[ "$(readlink "$FLOATLIB_BUILD_LOCK" 2>/dev/null || true)" == "$owner" ]]; then
        rm -f "$FLOATLIB_BUILD_LOCK"
      fi
      continue
    fi
    if [[ "$reported" -eq 0 ]]; then
      printf 'waiting for Lake build lock held by process %s\n' "${owner:-unknown}" >&2
      reported=1
    fi
    sleep 0.1
  done
}

floatlib_release_build_lock() {
  if [[ "$(readlink "$FLOATLIB_BUILD_LOCK" 2>/dev/null || true)" == "$$" ]]; then
    rm -f "$FLOATLIB_BUILD_LOCK"
  fi
}

floatlib_lake_in() {
  # `buildDir` is a configuration option read while Lake elaborates `lakefile.lean`.
  # Reconfigure once for each root/build-directory pair, then reuse that configuration in this
  # process and its children. Re-running `-R` for every build, executable, and checker forces Lake
  # to inspect every dependency checkout repeatedly.
  local workspace="${1:?a Lake workspace directory is required}"
  shift
  workspace="$(cd "$workspace" && pwd)" || return
  local configuration="$workspace:$FLOATLIB_BUILD_DIR"
  local status
  local reconfigure=0

  floatlib_acquire_build_lock
  if [[ "${FLOATLIB_LAKE_CONFIGURED_FOR:-}" == "$configuration" ]]; then
    if (cd "$workspace" && "${LAKE:-lake}" -KbuildDir="$FLOATLIB_BUILD_DIR" "$@"); then
      status=0
    else
      status=$?
    fi
  else
    reconfigure=1
    if (cd "$workspace" && "${LAKE:-lake}" -R -KbuildDir="$FLOATLIB_BUILD_DIR" "$@"); then
      status=0
    else
      status=$?
    fi
  fi
  floatlib_release_build_lock

  if [[ "$status" -eq 0 && "$reconfigure" -eq 1 ]]; then
    export FLOATLIB_LAKE_CONFIGURED_FOR="$configuration"
  fi
  return "$status"
}

floatlib_lake() {
  floatlib_lake_in "$PWD" "$@"
}

floatlib_test_lake() {
  floatlib_lake_in "$FLOATLIB_ROOT/tests" "$@"
}

floatlib_benchmark_lake() {
  floatlib_lake_in "$FLOATLIB_ROOT/benchmarks" "$@"
}

floatlib_build_path() {
  local relative_path="${1:?a build-relative path is required}"
  printf '%s/%s\n' "$FLOATLIB_BUILD_DIR" "${relative_path#/}"
}
