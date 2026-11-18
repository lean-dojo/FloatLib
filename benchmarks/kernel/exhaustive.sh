#!/usr/bin/env bash
# Kernel time to check two statements about all 65,536 pairs of E4M3 encodings.
#
# usage: benchmarks/kernel/exhaustive.sh
#
# Type-checks `Exhaustive.lean` once and prints, for each of its two theorems, the time Lean's
# kernel spent on the loop over the pairs and the axioms the theorem depends on.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

cd "$root"
floatlib_lake env timeout --kill-after=10 900 lean -Dprofiler=true -Dprofiler.threshold=1000 \
  "$here/Exhaustive.lean" 2>&1 | grep -E "type checking took|depends on axioms|error" |
  sed 's/^/KEXHAUSTIVE /'
