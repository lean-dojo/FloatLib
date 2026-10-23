#!/usr/bin/env bash

# Check fused multiply-add of every operand triple of the eight-bit formats `ieee 4 3` and E5M2
# in all six rounding directions against the exact reference of
# tests/FloatLibTests/Regression/BinaryInterchange/RoundingDirections.lean. The 201,326,592
# cases split into SHARD_COUNT shards by the first operand; run the shards in parallel.

set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 SHARD_INDEX SHARD_COUNT" >&2
  exit 2
fi

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

floatlib_test_lake build check >&2
"$(floatlib_build_path bin/check)" fma-exhaustive "$1" "$2"
