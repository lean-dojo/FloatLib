#!/usr/bin/env bash
# Kernel time of the operations beyond the six arithmetic ones, as a Markdown table: outcomes
# with status flags, comparisons, the total order, classification, integral rounding, conversion
# to an integer and to the exact rational value, casts and literals.
#
# usage: benchmarks/kernel/extras.sh [COUNT] [REPS] [FORMAT...]
#
#   COUNT   operand triples or literals per cell (default 16)
#   REPS    repetitions, the fastest is reported (default 3)
#   FORMAT  any of binary32 binary64 (default both)
#
# Each row is one term, reduced by Lean's kernel twice (`Harness.lean`): as written, through the
# public operations (`public`), and after the rewrite that `float_decide` applies (`kernel`).
# The cast rows are the reference cast `Model.cast` into the next narrower format, between a
# decode and a store. A cell is (time of the fold over the table - time of a fold that only
# reads and stores its first operand) / COUNT.
# An outcome row evaluates the delivered value, the comparison of its flags with a record and
# the comparison of its ternary value with a constant, as a statement about an outcome does.
# Operands are normal numbers. The square root and the last five operand rows take positive
# operands.
# Results go to `benchmarks/results/kernel/extras.{log,md}` unless KERNEL_BENCH_OUT names another
# directory. KERNEL_BENCH_TIMEOUT (seconds, default 600) bounds each format.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

count="${1:-16}"
reps="${2:-3}"
shift $(( $# < 2 ? $# : 2 ))
formats=("$@")
if [[ ${#formats[@]} -eq 0 ]]; then formats=(binary32 binary64); fi
out="${KERNEL_BENCH_OUT:-$root/benchmarks/results/kernel}"
work="$(mktemp -d "${TMPDIR:-/tmp}/kernel-extras.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir -p "$out"
log="$out/extras.log"
: > "$log"

# type expWidth fracWidth bias narrowerType
layout() {
  case "$1" in
    binary32) echo "Binary32 8 23 127 Binary16" ;;
    binary64) echo "Binary64 11 52 1023 Binary32" ;;
    *) echo "unknown format $1" >&2; exit 2 ;;
  esac
}

cd "$root"
floatlib_lake env lean -o "$work/Harness.olean" "$here/Harness.lean"

for format in "${formats[@]}"; do
  read -r type ew fw bias narrow <<<"$(layout "$format")"
  cell="$work/Cell_$format.lean"
  {
    cat <<EOF
import FloatLib.Floats.Formats.BinaryInterchange.Configured
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
import Harness
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLibBenchmarks.KernelReduction
set_option maxRecDepth 1000000

def ofB (bits : Nat) : $type := ExecFloat.Binary.ofNatBits bits
def toB (value : $type) : Nat := ExecFloat.Binary.toNatBits value
def toN (value : $narrow) : Nat := ExecFloat.Binary.toNatBits value

/-- Fold a natural-number observation of three operands over a table. -/
def observe (op : $type → $type → $type → Nat) (table : List (Nat × Nat × Nat)) : Nat :=
  table.foldl (fun acc t => Nat.add acc (op (ofB t.1) (ofB t.2.1) (ofB t.2.2))) 0

/-- Fold a natural-number observation over the first \`n\` indices. -/
def indices (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => Nat.add acc (f i)) 0

/--
An outcome as one number: the delivered value, and the two comparisons that a statement about
its flags and its ternary value makes.
-/
local macro "code% " o:term : term =>
  \`(let o := \$o; Nat.add (toB o.value)
      (Nat.add (decide (o.status = { inexact := true })).toNat (decide (o.ternary = .gt)).toNat))

/-- A rational number built without field operations, so that the kernel builds it cheaply. -/
local macro "ratio% " i:term : term => \`((mkRat (2 * (\$i : Nat) + 1) (3 * \$i + 7) : ℚ))
EOF
    table() { echo "(operandTable% $ew $fw $bias true true normal $1 $count)"; }
    rewriting=" rewriting [observe, indices, ofB, toB, toN]"
    # tag term
    bench() {
      echo "#kernel_bench \"$format $1 public\" $reps ($2)"
      echo "#kernel_bench \"$format $1 kernel\" $reps$rewriting ($2)"
    }
    operands() { bench "$1" "observe ($3) $(table "$2")"; }
    for kind in additive multiplicative fused root; do
      operands "noop-$kind" "$kind" 'fun x _ _ => toB x'
    done
    operands add-outcome additive \
      'fun x y _ => code% (ExecFloat.Binary.add x y (status := true))'
    operands sub-outcome additive \
      'fun x y _ => code% (ExecFloat.Binary.sub x y (status := true))'
    operands mul-outcome multiplicative \
      'fun x y _ => code% (ExecFloat.Binary.mul x y (status := true))'
    operands div-outcome multiplicative \
      'fun x y _ => code% (ExecFloat.Binary.div x y (status := true))'
    operands sqrt-outcome root 'fun x _ _ => code% (ExecFloat.Binary.sqrt x (status := true))'
    operands fma-outcome fused \
      'fun x y z => code% (ExecFloat.Binary.fma x y z (status := true))'
    operands roundToIntegral-outcome root \
      'fun x _ _ => code% (ExecFloat.Binary.roundToIntegral x .nearest (status := true))'
    operands less additive 'fun x y _ => (decide (x < y)).toNat'
    operands equal additive 'fun x y _ => (x == y).toNat'
    operands totalOrder additive 'fun x y _ => (ExecFloat.Binary.totalOrder x y).toNat'
    operands isNaN root 'fun x _ _ => (ExecFloat.Binary.isNaN x).toNat'
    operands roundToIntegral root \
      'fun x _ _ => toB (ExecFloat.Binary.roundToIntegral x .nearest)'
    operands toInt root 'fun x _ _ => ((x.toInt? (mode := .nearest)).getD 0).natAbs'
    operands toRat root 'fun x _ _ => ((ExecFloat.Binary.toRat? x).getD 0).den'
    operands cast root \
      'fun x _ _ => toN (ExecFloat.Binary.ofModel
        (Model.cast _ _ (ExecFloat.Binary.toModel x) .nearest))'
    operands cast-outcome root \
      'fun x _ _ => let o := Model.cast _ _ (ExecFloat.Binary.toModel x) .nearest (status := true);
        Nat.add (toN (ExecFloat.Binary.ofModel o.value))
          (Nat.add (decide (o.status = { inexact := true })).toNat
            (decide (o.ternary = .gt)).toNat)'
    bench noop-decimal "indices $count (fun i => i)"
    bench decimal "indices $count (fun i => toB (OfScientific.ofScientific (2 * i + 1) true 3))"
    bench noop-rational \
      "indices $count (fun i => let q := ratio% i; Nat.add q.num.natAbs q.den)"
    bench rational \
      "indices $count (fun i => toB (ExecFloat.Binary.ofRat (ratio% i) (mode := .up)))"
    bench rational-outcome \
      "indices $count (fun i => code% (ExecFloat.Binary.ofRat (ratio% i) (mode := .up)
        (status := true)))"
  } > "$cell"
  echo "== $format" | tee -a "$log"
  limit="${KERNEL_BENCH_TIMEOUT:-600}"
  floatlib_lake env bash -c \
    "LEAN_PATH=\"$work:\$LEAN_PATH\" timeout --kill-after=10 $limit lean \"$cell\"" \
    2>&1 | cut -c1-200 | tee -a "$log" || true
  status="${PIPESTATUS[0]}"
  if [[ "$status" -ne 0 ]]; then
    echo "KBENCH-FAILED $format: exit $status (124 means no result within $limit s)" | tee -a "$log"
  fi
done

awk -v n="$count" '
  $1 == "KBENCH" {
    f = $2; op = $3; path = $4; t = $5
    if (op ~ /^noop-/) { base[f, substr(op, 6), path] = t; next }
    kind = (op ~ /^(mul|div)-/) ? "multiplicative" : (op ~ /^fma-/) ? "fused" : \
      (op ~ /^(add|sub)-/ || op == "less" || op == "equal" || op == "totalOrder") ? "additive" : \
      (op == "decimal") ? "decimal" : (op ~ /^rational/) ? "rational" : "root"
    us[f, op, path] = (t - base[f, kind, path]) / n / 1000
    if (!(f in formatSeen)) { formatSeen[f] = 1; formats[++nf] = f }
    if (!(op in opSeen)) { opSeen[op] = 1; ops[++no] = op }
  }
  END {
    printf "| operation |"
    for (i = 1; i <= nf; i++) printf " %s public | %s kernel path |", formats[i], formats[i]
    print ""
    printf "| --- |"
    for (i = 1; i <= nf; i++) printf " ---: | ---: |"
    print ""
    for (j = 1; j <= no; j++) {
      printf "| %s |", ops[j]
      for (i = 1; i <= nf; i++) {
        m = split("public kernel", paths, " ")
        for (p = 1; p <= m; p++) {
          key = formats[i] SUBSEP ops[j] SUBSEP paths[p]
          if (key in us) printf " %.0f |", us[key]; else printf " n/a |"
        }
      }
      print ""
    }
  }' "$log" > "$out/extras.md"
echo "microseconds of kernel time per operation ($count per cell, fastest of $reps):"
cat "$out/extras.md"
