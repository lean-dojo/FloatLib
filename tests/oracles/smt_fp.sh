#!/usr/bin/env bash

# Run the bounded SMT-LIB QF_FP differential adapter. The internal mode is used
# by the Python driver to execute the standalone Lean stream runner while
# retaining the repository's local-build-directory policy.

set -euo pipefail

ROOT="$(
  cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd
)"

if [[ "${1:-}" == "--lean-runner" ]]; then
  shift
  # shellcheck source=tests/lib/lake.sh
  source "$ROOT/tests/lib/lake.sh"
  SMT_FP_WORKSPACE="${TMPDIR:-/tmp}/floatlib-smt-fp-workspace-$FLOATLIB_WORKTREE_KEY"
  mkdir -p "$SMT_FP_WORKSPACE"
  ln -sfn "$ROOT/tests/oracles/SMTFP/lakefile.lean" "$SMT_FP_WORKSPACE/lakefile.lean"
  ln -sfn "$ROOT/lean-toolchain" "$SMT_FP_WORKSPACE/lean-toolchain"
  export FLOATLIB_ROOT="$ROOT"
  floatlib_lake_in "$SMT_FP_WORKSPACE" \
    --file "$SMT_FP_WORKSPACE/lakefile.lean" \
    build smtFpRunner >&2
  "$FLOATLIB_BUILD_DIR/bin/smtFpRunner" "$@"
  exit $?
fi

exec python3 "$ROOT/tests/oracles/smt_fp.py" --lean-runner "$0" "$@"
