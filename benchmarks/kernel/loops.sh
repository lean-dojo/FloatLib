#!/usr/bin/env bash
# Kernel time to check three statements about loops of 1,000 floating-point steps.
#
# usage: benchmarks/kernel/loops.sh [REPS]
#
# For each loop of `Loops.lean` this type-checks the theorem that the loop's result has a given
# encoding, REPS times (default 3), by `decide +kernel` on the public operations (`public`) and
# by `float_decide` (`kernel`). It prints the time Lean's kernel spent on each theorem and the
# axioms the theorem depends on. `FlocqConversion.v` states the same three results in Coq.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

reps="${1:-3}"
work="$(mktemp -d "${TMPDIR:-/tmp}/kernel-loops.XXXXXX")"
trap 'rm -rf "$work"' EXIT

cd "$root"
floatlib_lake env lean -o "$work/Loops.olean" "$here/Loops.lean"

# name statement
cases=(
  "sumTenth|KernelPath.toNat (sumTenth 1000) = 1120403331"
  "sum64|KernelPath.toNat (sum64 1000) = 13851123079082828159"
  "dot64|KernelPath.toNat (dot64 1000) = 4676214714831268436"
)

for entry in "${cases[@]}"; do
  name="${entry%%|*}"
  statement="${entry#*|}"
  for path_name in kernel public; do
    if [[ "$path_name" == kernel ]]; then
      proof="float_decide [$name]"
    else
      proof="unfold $name; decide +kernel"
    fi
    file="$work/${name}_$path_name.lean"
    {
      echo "import Loops"
      echo "open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange"
      echo "open FloatLibBenchmarks.KernelLoops"
      echo "set_option maxRecDepth 1000000"
      echo "set_option profiler true"
      echo "set_option profiler.threshold 20"
      echo "theorem bench : $statement := by"
      echo "  $proof"
      echo "#print axioms bench"
    } > "$file"
    for run in $(seq "$reps"); do
      result="$(floatlib_lake env bash -c \
        "LEAN_PATH=\"$work:\$LEAN_PATH\" timeout --kill-after=10 900 lean \"$file\"" 2>&1 |
        grep -E "type checking took|depends on axioms|error" | tr '\n' ' ')"
      echo "KLOOP $name $path_name run $run: $result"
    done
  done
done
