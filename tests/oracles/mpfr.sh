#!/usr/bin/env bash

# Cross-check primitive operations and exact reductions with independent MPFR programs.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

suite="${1:-all}"

case "$suite" in
  all|primitives|reductions) ;;
  *)
    printf 'usage: %s [all|primitives|reductions]\n' "$0" >&2
    exit 2
    ;;
esac

cc="${CC:-cc}"
if ! command -v pkg-config >/dev/null 2>&1 ||
    ! pkg-config --atleast-version=4.1.0 mpfr; then
  printf '%s\n' 'MPFR 4.1.0 or newer is required.' >&2
  exit 1
fi
if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'C compiler not found: %s\n' "$cc" >&2
  exit 1
fi

build_dir="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-mpfr.XXXXXX")"
trap 'rm -rf "$build_dir"' EXIT

read -r -a mpfr_cflags <<<"$(pkg-config --cflags mpfr)"
read -r -a mpfr_libs <<<"$(pkg-config --libs mpfr)"

run_oracle() {
  local name="$1"
  local source="$2"
  local oracle="$build_dir/${name}_mpfr_oracle"

  "$cc" -O2 -std=c11 -Wall -Wextra -Werror \
    "${mpfr_cflags[@]}" "$source" "${mpfr_libs[@]}" -o "$oracle"
  "$(floatlib_build_path bin/oracle)" "$name" | "$oracle"
}

floatlib_test_lake build oracle >&2

if [[ "$suite" == all || "$suite" == primitives ]]; then
  run_oracle primitives \
    "$root/tests/oracles/primitive_mpfr_oracle.c"
fi

if [[ "$suite" == all || "$suite" == reductions ]]; then
  run_oracle reductions \
    "$root/tests/oracles/reduction_mpfr_oracle.c"
fi
