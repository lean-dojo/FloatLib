#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

bash tests/checks/version-pins.sh

floatlib_lake build
floatlib_test_lake test
floatlib_lake lint

if [[ "${FLOATLIB_RUN_INDEPENDENT_CHECKER:-0}" == "1" ]]; then
  # Replay compiled FloatLib declarations through Lean's kernel after elaboration. Loading the
  # dependency environments can require hundreds of GiB, so ordinary development runs opt in.
  floatlib_lake env leanchecker FloatLib
else
  printf '%s\n' \
    'Skipping kernel replay; set FLOATLIB_RUN_INDEPENDENT_CHECKER=1 to run leanchecker.'
fi

"$ROOT/tests/checks/architecture.sh"
"$ROOT/tests/checks/public-api-docs.sh"
"$ROOT/tests/checks/trust-surface.sh"

if command -v python3 >/dev/null 2>&1 &&
    python3 -c 'import flint' >/dev/null 2>&1; then
  floatlib_test_lake exe check arb
else
  printf '%s\n' \
    'Skipping optional Arb-backed checks: install python-flint to enable them.'
fi

printf '%s\n' \
  'FloatLib verification passed. Website validation is a separate final release step.'
