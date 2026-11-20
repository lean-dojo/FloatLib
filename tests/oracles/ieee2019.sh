#!/usr/bin/env bash
# The operations of IEEE 754-2019 that FloatLib added in 2026-11, against brute force on a small
# format and against other implementations.
#
# usage: tests/oracles/ieee2019.sh [COUNT] [SEED]
#
#   COUNT  cases of each kind that the references generate (default 20000)
#   SEED   seed of the generators (default 20261116)
#
# 1. `oracle ieee2019 exhaustive`: the binary operations of clauses 9.4 to 9.7 on every pair of
#    encodings of a six-bit format and the payload operations on every encoding of a ten-bit
#    format, against results computed by brute force from the definitions.
# 2. `oracle ieee2019 formatOf`: the formatOf operations of clause 5.4.1 in the six rounding
#    directions, against the operations of one format on every pair of encodings of the six-bit
#    format, and across three formats against the rounded exact rational result.
# 3. `oracle ieee2019 check`: decimal addition, subtraction, multiplication (the specification
#    and the kernel path), the extrema, the decimal reductions `sum`, `sumAbs`, `sumSquare`
#    and `dot`, the decimal scaled products, and the decimal reductions from left to right in
#    an accumulator format against Python's `decimal` (libmpdec); the augmented
#    operations, sumAbs, sumSquare and scaledProd on binary64 against exact rational arithmetic
#    in Python; getPayload, setPayload and setPayloadSignaling on binary32 and binary64 against
#    the C library (glibc 2.25 or later).
#
# 4. With IEEE2019_PACKAGES set to a directory that holds the Python package `mpmath` (for
#    example the target of `pip install --target DIR mpmath`): the recommended functions of
#    clause 9.2 on binary formats, value and flags, against `mpmath` at high precision. Every
#    encoding of five eight-bit formats (an IEEE one, OCP E5M2 and E4M3, ONNX E4M3FNUZ and
#    E5M2FNUZ) and of the four-bit E2M1 for the functions of one operand, `rootn` and `pown`,
#    every pair of a six-bit format and of E2M1 for those of two, 50 * COUNT / 1000
#    pseudo-random pairs of each eight-bit format, and COUNT / 1000 pseudo-random operands of
#    binary16, binary32 and binary64 for each function, in the five rounding directions. The
#    small formats are about 430,000 cases whatever COUNT is. Then the decimal functions of
#    clause 9.2 against `mpmath`, COUNT / 1000 operands for each function in each of decimal32,
#    decimal64 and decimal128: the total functions with their flags in the five rounding
#    directions, and the certified functions to nearest-even. A certified function returns a
#    result only when an enclosure settles it: a case without a result is counted in a group
#    `dfun-unsettled` and is not a failure. Without the variable this part is skipped with a
#    notice.
#
# The oracle runs in Lean's interpreter, so no executable has to be linked. Every `RESULT` line
# reports the cases and the failures of one group, and the script fails when a group has one.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

count="${1:-20000}"
seed="${2:-20261116}"
work="$(mktemp -d "${TMPDIR:-/tmp}/ieee2019.XXXXXX")"
trap 'rm -rf "$work"' EXIT

oracle() {
  (cd "$root/tests" && floatlib_test_lake env lean --run "$root/tests/OracleIEEE2019.lean" "$@")
}

status=0
oracle exhaustive || status=1
oracle formatOf || status=1

for kind in decimal extrema augmented reductions decimal-reductions decimal-scaled \
    decimal-ordered; do
  python3 -I "$here/ieee2019/reference.py" "$kind" "$count" "$seed" >> "$work/cases"
done
"${CC:-cc}" -O1 -o "$work/payload" "$here/ieee2019/payload.c" -lm
"$work/payload" "$count" "$seed" >> "$work/cases"
if [[ -n "${IEEE2019_PACKAGES:-}" ]]; then
  python3 -I "$here/ieee2019/functions.py" "$IEEE2019_PACKAGES" "$(( count / 1000 ))" "$seed" \
    >> "$work/cases"
  python3 -I "$here/ieee2019/decimal_functions.py" "$IEEE2019_PACKAGES" "$(( count / 1000 ))" \
    "$seed" >> "$work/cases"
else
  echo "IEEE2019_PACKAGES is not set: the functions of clause 9.2 are not compared with mpmath" >&2
fi
oracle check < "$work/cases" || status=1
exit "$status"
