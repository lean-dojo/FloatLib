#!/usr/bin/env bash
set -euo pipefail

# Check one block of the exhaustive binary16/bfloat16 arithmetic or binary32 square-root campaign.
#
# A `pairs` block holds the 2^24 ordered operand pairs whose first operand lies in
# [256*BLOCK, 256*BLOCK + 255], so blocks 0..255 cover all 2^32 pairs of one operation and
# direction. A `sqrt` block holds the 2^22 binary32 encodings from 2^22*BLOCK, so blocks 0..1023
# cover every input. FloatLib writes the value and five flags of every case, and the reference
# compares them with Berkeley SoftFloat and an MPFR emulation of the format. With --mpfx-dir the
# reference is also built against an MPFX checkout and compares its engines with FloatLib.

usage() {
  echo "usage: $0 --softfloat-dir DIR [--mpfx-dir DIR] pairs f16|bf16 add|sub|mul|div MODE BLOCK" >&2
  echo "       $0 --softfloat-dir DIR [--mpfx-dir DIR] sqrt f32 sqrt MODE BLOCK" >&2
  echo "MODE is near_even, minMag, min, or max; DIR is a SoftFloat 3 checkout built in" >&2
  echo "build/Linux-x86_64-GCC (tests/oracles/testfloat.sh builds the pinned revision)." >&2
}

softfloat_dir="${SOFTFLOAT_DIR:-}"
mpfx_dir="${MPFX_DIR:-}"
arguments=()
while (($#)); do
  case "$1" in
    --softfloat-dir) (($# >= 2)) || { usage; exit 2; }; softfloat_dir="$2"; shift 2 ;;
    --mpfx-dir) (($# >= 2)) || { usage; exit 2; }; mpfx_dir="$2"; shift 2 ;;
    --help|-h) usage; exit 0 ;;
    *) arguments+=("$1"); shift ;;
  esac
done
((${#arguments[@]} == 5)) || { usage; exit 2; }
kind="${arguments[0]}" format="${arguments[1]}" operation="${arguments[2]}"
mode="${arguments[3]}" block="${arguments[4]}"
case "$kind" in
  pairs) count=16777216 ;;
  sqrt) count=4194304 ;;
  *) usage; exit 2 ;;
esac
start=$((block * count))

softfloat_library="$softfloat_dir/build/Linux-x86_64-GCC/softfloat.a"
if [[ -z "$softfloat_dir" || ! -f "$softfloat_library" ]]; then
  printf 'SoftFloat library not found under %s\n' "${softfloat_dir:-<unset>}" >&2
  exit 1
fi

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-exhaustive16.XXXXXX")"
trap 'rm -rf "$work"' EXIT
# shellcheck source=tests/lib/lake.sh
source "$repo_root/tests/lib/lake.sh"

compile=(
  "${CXX:-c++}" -std=c++20 -O2 -Wall -Wextra
  -I "$softfloat_dir/source/include" -I "$softfloat_dir/build/Linux-x86_64-GCC"
)
sources=("$script_dir/exhaustive16_reference.cpp")
if [[ -n "$mpfx_dir" ]]; then
  compile+=(-DFLOATLIB_WITH_MPFX -I "$mpfx_dir/include")
  sources+=("$mpfx_dir/src/flags.cpp")
fi
"${compile[@]}" "${sources[@]}" "$softfloat_library" -lmpfr -lgmp -o "$work/reference"

(
  cd "$repo_root"
  floatlib_benchmark_lake build execFloatExhaustive >&2
  "$(floatlib_build_path bin/execFloatExhaustive)" \
    "$kind" "$format" "$operation" "$mode" "$start" "$count" "$work/block.bin"
)
"$work/reference" "$kind" "$format" "$operation" "$mode" "$start" "$count" "$work/block.bin"
