#!/usr/bin/env bash

# Elaborate the plain files of the checks: Lean files that do not start with `module`.
#
# The library and its tests are modules, and a module does not load the bodies of the private
# declarations of its imports. A plain file does, so a tactic can behave differently in one.
# `tests/checks/PlainFile.lean` holds statements that have to come out the same in both kinds
# of file. It is elaborated here in the library's environment, and any message fails the check.
# The library has to be built.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

for file in tests/checks/PlainFile.lean; do
  if grep -qx 'module' "$file"; then
    printf 'plain-file check failed: %s starts with `module`\n' "$file" >&2
    exit 1
  fi
  if ! messages="$(floatlib_lake env lean "$file" 2>&1)" || [[ -n "$messages" ]]; then
    printf '%s\n' "$messages" >&2
    printf 'plain-file check failed: %s does not elaborate without a message\n' "$file" >&2
    exit 1
  fi
done
printf '%s\n' 'Plain-file check passed.'
