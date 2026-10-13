#!/usr/bin/env bash
set -euo pipefail

# Compare MPFX with FloatLib on one format, operation, and operand set in all four IEEE directions.
#
# FloatLib's results and flags come from `execFloatOracleList`; mpfx_list.cpp evaluates MPFX's
# hardware round-to-odd and error-free-transformation engines in the double container and, when
# the format fits, the float container. Operands and results stay in WORK for classify.py.

usage() {
  echo "usage: $0 --mpfx-dir DIR --work DIR EXPONENT_BITS FRACTION_BITS OP SET COUNT" >&2
  echo "OP is add, sub, mul, div, sqrt, or fma; SET is random, unit, or tiny (see operands.py)." >&2
}

mpfx_dir="${MPFX_DIR:-}"
work=""
arguments=()
while (($#)); do
  case "$1" in
    --mpfx-dir) (($# >= 2)) || { usage; exit 2; }; mpfx_dir="$2"; shift 2 ;;
    --work) (($# >= 2)) || { usage; exit 2; }; work="$2"; shift 2 ;;
    --help|-h) usage; exit 0 ;;
    *) arguments+=("$1"); shift ;;
  esac
done
((${#arguments[@]} == 5)) && [[ -n "$mpfx_dir" && -n "$work" ]] || { usage; exit 2; }
exponent_bits="${arguments[0]}" fraction_bits="${arguments[1]}"
operation="${arguments[2]}" operand_set="${arguments[3]}" count="${arguments[4]}"
format="e${exponent_bits}m${fraction_bits}"
base="$format.$operation.$operand_set"

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../../.." && pwd)"
# shellcheck source=tests/lib/lake.sh
source "$repo_root/tests/lib/lake.sh"
mkdir -p "$work/cases" "$work/out"

if [[ ! -x "$work/mpfx_list" ]]; then
  "${CXX:-c++}" -std=c++20 -O2 -march=native -DNDEBUG -I "$mpfx_dir/include" \
    "$script_dir/mpfx_list.cpp" "$mpfx_dir/src/flags.cpp" -o "$work/mpfx_list"
fi
(cd "$repo_root" && floatlib_benchmark_lake build execFloatOracleList >&2)
oracle="$(floatlib_build_path bin/execFloatOracleList)"

[[ -s "$work/cases/$base.in" ]] ||
  python3 -I "$script_dir/operands.py" "$exponent_bits" "$fraction_bits" \
    "$operation" "$operand_set" "$count" 20261013 > "$work/cases/$base.in"
containers=(double)
((exponent_bits <= 8 && fraction_bits <= 21)) && containers+=(float)
for mode in near_even minMag min max; do
  floatlib="$work/out/$base.$mode.floatlib"
  [[ -s "$floatlib" ]] || "$oracle" "$format" "$operation" "$mode" "$work/cases/$base.in" > "$floatlib"
  for container in "${containers[@]}"; do
    for engine in hw eft; do
      "$work/mpfx_list" "$format" "$container" "$engine" "$operation" "$mode" \
        "$work/cases/$base.in" "$floatlib" | tee "$work/out/$base.$mode.$container.$engine.txt" |
        grep '^RESULT'
    done
  done
done
