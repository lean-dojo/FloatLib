#!/usr/bin/env bash

# Keep the library and the tests free of linter warnings.
#
# Lake prints a warning and goes on. This check builds every module the linters read with
# `--wfail`, which turns a warning into a failure, also one that Lake replays from an earlier
# build. The linters are the `linterOptions` of `lakefile.lean` and `tests/lakefile.lean`.
# A module that loads no package does not load Mathlib's source linters, so each of these is
# elaborated once more with `Mathlib.Init` imported.
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

# The modules that load no package (`core-only.py`): the `weak.` options of `lakefile.lean` do
# nothing for a linter that a module does not import. A copy of each, with `Mathlib.Init` as one
# more import, is elaborated with the options that Lake gives a file of this workspace, and any
# message fails the check.
copies="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-linters.XXXXXX")"
trap 'rm -rf "$copies"' EXIT
mapfile -t package_free < <(python3 tests/checks/core-only.py)
for module in "${package_free[@]}"; do
  copy="$copies/$module.lean"
  awk '{ print } /^module$/ && !done { print "public meta import Mathlib.Init"; done = 1 }' \
    "${module//.//}.lean" > "$copy"
  grep -qx 'public meta import Mathlib.Init' "$copy" || fail "$module has no module line"
  floatlib_lake setup-file "$copy" > "$copies/setup.json"
  messages="$(floatlib_lake env lean --setup "$copies/setup.json" "$copy" 2>&1)" ||
    fail "$module does not elaborate with Mathlib.Init imported: $messages"
  [[ -z "$messages" ]] || fail "$module under Mathlib's source linters: $messages"
done

floatlib_lake lint
