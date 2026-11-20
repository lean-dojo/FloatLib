#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

python3 tests/checks/publication-privacy.py
bash tests/checks/version-pins.sh
python3 tests/checks/doc-links.py

"$ROOT/tests/checks/linters.sh"
floatlib_test_lake test
"$ROOT/tests/checks/plain-file.sh"

if [[ "${FLOATLIB_RUN_INDEPENDENT_CHECKER:-0}" == "1" ]]; then
  # Give every compiled declaration of the library to Lean's kernel once more, one module per
  # process. It takes about an hour of processor time, so ordinary development runs opt in.
  "$ROOT/tests/checks/kernel-replay.sh"
else
  printf '%s\n' \
    'Skipping kernel replay; set FLOATLIB_RUN_INDEPENDENT_CHECKER=1 to run it.'
fi

"$ROOT/tests/checks/architecture.sh"
"$ROOT/tests/checks/public-api-docs.sh"
"$ROOT/tests/checks/trust-surface.sh"
python3 tests/checks/source-screen.py --check tests/checks/source-screen.txt

if command -v python3 >/dev/null 2>&1 &&
    python3 -c 'import flint' >/dev/null 2>&1; then
  floatlib_test_lake exe check arb
else
  printf '%s\n' \
    'Skipping optional Arb-backed checks: install python-flint to enable them.'
fi

printf '%s\n' \
  'FloatLib verification passed. Website validation is a separate final release step.'
