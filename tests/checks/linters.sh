#!/usr/bin/env bash

# Keep the library and the tests free of linter warnings.
#
# Lake prints a warning and goes on. This check builds every module the linters read with
# `--wfail`, which turns a warning into a failure, also one that Lake replays from an earlier
# build. The linters are the `linterOptions` of `lakefile.lean` and `tests/lakefile.lean`.
# `lake lint` then runs the Batteries environment linters and `docBlameThm` on every lint root.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

fail() {
  printf 'linter check failed: %s\n' "$*" >&2
  exit 1
}

# The library: `import FloatLib` and the opt-in entry points, as `lake lint` reads them.
mapfile -t lint_roots < <(
  awk '/^def lintRoots/ { inside = 1 } inside { print } inside && /\]/ { exit }' lakefile.lean |
    grep -oE '"FloatLib[A-Za-z0-9_.]*"' |
    tr -d '"'
)
[[ "${#lint_roots[@]}" -gt 0 ]] || fail "lakefile.lean passes no module to the linter"

# The tests: the test library, the oracle support library, and the root module of every
# executable. A `+Module` target elaborates the module without linking the executable.
mapfile -t test_targets < <(
  {
    grep -oE '^lean_lib [A-Za-z0-9_]+' tests/lakefile.lean | awk '{ print $2 }'
    grep -oE 'root := `[A-Za-z0-9_.]+' tests/lakefile.lean | sed 's/.*`/+/'
  } | LC_ALL=C sort -u
)
[[ "${#test_targets[@]}" -gt 0 ]] || fail "tests/lakefile.lean declares no target"

floatlib_lake build --wfail "${lint_roots[@]}"
floatlib_test_lake build --wfail "${test_targets[@]}"
floatlib_lake lint
