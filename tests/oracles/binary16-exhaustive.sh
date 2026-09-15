#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "usage: $0 {add|mul} SHARD_INDEX SHARD_COUNT" >&2
  exit 2
fi

operation=$1
shard_index=$2
shard_count=$3

case "$operation" in
  add|mul) ;;
  *)
    echo "unknown operation: $operation" >&2
    exit 2
    ;;
esac

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/floatlib-binary16.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT
# shellcheck source=tests/lib/lake.sh
source "$repo_root/tests/lib/lake.sh"

cc=${CC:-cc}
if ! command -v pkg-config >/dev/null 2>&1 ||
    ! pkg-config --atleast-version=4.1.0 mpfr; then
  printf '%s\n' 'MPFR 4.1.0 or newer is required for exhaustive binary16 validation.' >&2
  exit 1
fi
if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'C compiler not found: %s\n' "$cc" >&2
  exit 1
fi
read -r -a mpfr_cflags <<<"$(pkg-config --cflags mpfr)"
read -r -a mpfr_libs <<<"$(pkg-config --libs mpfr)"

"$cc" -O3 -std=c11 -Wall -Wextra -Werror \
  "${mpfr_cflags[@]}" \
  "$repo_root/tests/oracles/binary16_mpfr_oracle.c" \
  "${mpfr_libs[@]}" \
  -o "$build_dir/binary16_mpfr_oracle"

(
  cd "$repo_root"
  floatlib_test_lake build oracle >&2
  "$(floatlib_build_path bin/oracle)" binary16 \
    "$operation" "$shard_index" "$shard_count"
) | "$build_dir/binary16_mpfr_oracle" \
  "$operation" "$shard_index" "$shard_count"
