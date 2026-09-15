#!/usr/bin/env bash

# Run the checks that make a checked-in result set publishable.
#
# The site can only support its performance and conformance claims when both
# result bundles are present. Check that first so a release never succeeds by
# quietly omitting the evidence.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# Reusing the ordinary development build is convenient, but it can retain
# compiled modules after their source files have been renamed or removed. We
# want the independent checker to inspect this checkout, not yesterday's
# module graph, so a release begins with a clean FloatLib build. Dependency
# packages keep their separate shared cache.
#
# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

require_bundle() {
  local bundle=$1
  if [[ ! -d "$bundle" ]]; then
    printf 'release verification: missing result bundle: %s\n' "$bundle" >&2
    exit 1
  fi
  if [[ ! -f "$bundle/MANIFEST.tsv" ]]; then
    printf 'release verification: missing bundle manifest: %s/MANIFEST.tsv\n' \
      "$bundle" >&2
    exit 1
  fi
}

require_bundle "$root/tests/results/main"
require_bundle "$root/benchmarks/results/main"

bash benchmarks/scripts/verify-main-result.sh
bash tests/oracles/verify-main-result.sh

floatlib_lake clean floatlib

# Build and test the library before the website reuses its compiled
# environment. The opt-in checker is part of a release even though it is too
# expensive for the ordinary development loop.
FLOATLIB_RUN_INDEPENDENT_CHECKER=1 bash tests/verify.sh

bash site/build.sh --require-clean

printf '%s\n' 'FloatLib release verification passed.'
