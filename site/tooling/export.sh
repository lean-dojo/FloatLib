#!/usr/bin/env bash
# Export the proof-map data for the FloatLib site: site/content/phases.json plus the built
# library in, site/data/nodes.json out. See site/tooling/README.md.
#
# Usage: site/tooling/export.sh [--skip-lean]
#
# FLOATLIB_BUILD_DIR selects the Lake build directory; when unset, tests/lib/lake.sh supplies
# the per-checkout default that every other repository script uses.
# The Lean step builds the imports selected in content/phases.json, including the optional
# binary transcendental and unchecked host APIs, then exports the imported environment.

set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$root"

source "$root/tests/lib/lake.sh"

exec python3 site/tooling/export_atlas.py "$@"
