#!/usr/bin/env bash
# Kernel time of the operations of IEEE 754-2019 clauses 5 and 9 under their names in the
# standard, as two Markdown tables: the binary operations and the decimal operations.
#
# usage: benchmarks/kernel/ieee2019.sh [COUNT] [REPS] [FORMAT...]
#
#   COUNT   operand triples per cell (default 8)
#   REPS    repetitions, the fastest is reported (default 3)
#   FORMAT  any of e4f3 binary16 binary32 binary64 binary128 binary256 binary1024 binary4096
#           (e4f3 is the IEEE layout of eight bits with four exponent bits) and decimal32
#           decimal64 decimal128 (default all)
#
# Each row is one term, reduced by Lean's kernel twice (`Harness.lean`): as written (`public`),
# and after the rewrite that `float_decide` applies (`kernel`), which uses the rules tagged
# `@[kernel_optimize]`. A cell is (time of the fold over the table - time of a fold that only
# reads and stores its first operand) / COUNT, in microseconds. The decimal operands have full
# coefficients, so a decimal sum or product drops digits. A reduction takes three operands, and
# `dot`, `scaledProdSum` and `scaledProdDiff` two pairs. The conversions from character
# sequences read the text that the conversion to characters wrote for the operand.
#
# `setPayload` and `setPayloadSignaling` are applied to the integral part of an operand.
# `getPayload` reads a quiet NaN: for a binary format the operand with its exponent field and
# its quiet bit set, for a decimal format the NaN that `setPayload` built from the operand. The
# time of each preparation is subtracted.
#
# Results go to `benchmarks/results/kernel/ieee2019.{log,md}` unless KERNEL_BENCH_OUT names
# another directory. KERNEL_BENCH_TIMEOUT (seconds, default 900) bounds each format, and a
# format that does not finish is reported as a failure line in the log and as `n/a`.
#
# With KERNEL_BENCH_ROW_TIMEOUT (seconds) every row is reduced by its own Lean process with that
# limit, KERNEL_BENCH_JOBS of them at a time (default 1), so that a row that does not finish
# costs one cell and not the rest of its format. This is how the formats of 1,024 and 4,096
# bits are measured. KERNEL_BENCH_FUNCTION_ROW_TIMEOUT (seconds, default the row limit) is the
# limit of a row of the certified functions of clause 9.2, which take the longest.
# KERNEL_BENCH_ONLY is an extended regular expression: only the rows whose name it matches are
# measured, with the rows that give the time of the preparation.
#
# The formatOf rows round into binary32 from operands of the row's format. The rows `sumInOrder`
# to `sumAlong` are the reductions of clause 9.4 with one rounding at each addition, on the
# descriptor model, accumulated in the format of the row: three elements or pairs from left to
# right, and three elements along the order `x + (y + z)`.
#
# The rows of the recommended functions of clause 9.2 reduce the value that the function
# delivers to nearest-even. A binary operand has a magnitude between 1 and 2 and is scaled by
# 1/4 for the inverse sine, cosine and hyperbolic tangent and by 1/16 for `compound`; a decimal
# operand has its coefficient moved below one, and `acosh` is not measured for decimal formats.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

count="${1:-8}"
reps="${2:-3}"
shift $(( $# < 2 ? $# : 2 ))
formats=("$@")
if [[ ${#formats[@]} -eq 0 ]]; then
  formats=(e4f3 binary16 binary32 binary64 binary128 binary256 binary1024 binary4096
    decimal32 decimal64 decimal128)
fi
out="${KERNEL_BENCH_OUT:-$root/benchmarks/results/kernel}"
work="$(mktemp -d "${TMPDIR:-/tmp}/kernel-ieee2019.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir -p "$out"
log="$out/ieee2019.log"
: > "$log"

# exponentBits fractionBits bias
layout() {
  case "$1" in
    e4f3)       echo "4 3 7" ;;
    binary16)   echo "5 10 15" ;;
    binary32)   echo "8 23 127" ;;
    binary64)   echo "11 52 1023" ;;
    binary128)  echo "15 112 16383" ;;
    binary256)  echo "19 236 262143" ;;
    binary1024) echo "27 996 67108863" ;;
    binary4096) echo "35 4060 17179869183" ;;
    *) echo "unknown format $1" >&2; exit 2 ;;
  esac
}

cd "$root"
# The library's Lean environment is read once, so that a long measurement does not hold the
# build lock of `floatlib_lake`.
lean_environment="$(floatlib_lake env bash -c 'printf "%s\n%s\n" "$LEAN_PATH" "$(command -v lean)"')"
lean_path="$(sed -n 1p <<<"$lean_environment")"
lean="$(sed -n 2p <<<"$lean_environment")"
LEAN_PATH="$lean_path" "$lean" -o "$work/Harness.olean" "$here/Harness.lean"

only="${KERNEL_BENCH_ONLY:-}"
bench() {
  if [[ -n "$only" && "$1" != noop* && ! "$1" =~ $only ]]; then
    return
  fi
  echo "#kernel_bench \"$format $1 public\" $reps ($2)"
  echo "#kernel_bench \"$format $1 kernel\" $reps$rewriting ($2)"
}

for format in "${formats[@]}"; do
  cell="$work/Cell_$format.lean"
  if [[ "$format" == decimal* ]]; then
    {
      cat <<EOF2
import FloatLib.Floats.Formats.DecimalInterchange
import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Comparison
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Recommended.Runtime
import FloatLib.Tactic.FloatDecide
import Harness
open FloatLib.Floats.Formats.DecimalInterchange
open FloatLibBenchmarks.KernelReduction
set_option maxRecDepth 1000000

/-- A datum of the format with a full coefficient, from one pseudo-random word. -/
def datum (word : Nat) : Datum :=
  .finite (Nat.beq (Nat.mod word 2) 1)
    (Nat.mod (Nat.div word 2) (Nat.pow 10 (Format.$format).precision))
    (Int.negSucc (Nat.mod (Nat.div word 4) 16))

/-- One number of an outcome: its coefficient. -/
def codeOf (outcome : Outcome) : Nat :=
  Datum.casesOn (motive := fun _ => Nat) outcome.value (fun _ c _ => c) (fun _ => 0)
    (fun _ _ p => p)

/-- Fold a natural-number observation of two operands over a table. -/
def observe (op : Datum → Datum → Nat) (table : List (Nat × Nat × Nat)) : Nat :=
  table.foldl (fun acc t => Nat.add acc (op (datum t.1) (datum t.2.1))) 0

/-- A datum with its coefficient moved below one, the operand of the certified functions. -/
def small (x : Datum) : Datum :=
  Datum.casesOn (motive := fun _ => Datum) x
    (fun s c _ => .finite s c (Int.negSucc (Nat.pred (Format.$format).precision)))
    (fun s => .infinity s) (fun s t p => .nan s t p)

/-- The coefficient of a certified result, or zero when no result is returned. -/
def certified (result : Option Datum) : Nat :=
  Option.casesOn (motive := fun _ => Nat) result 0 (fun datum => codeOf { value := datum })
EOF2
      rewriting=" rewriting [observe]"
      table="(operandTable% 11 52 1023 true true normal additive $count)"
      row() { bench "$1" "observe ($2) $table"; }
      row noop 'fun x _ => codeOf { value := x }'
      for direction in TiesToEven:nearest TiesToAway:nearestAway TowardZero:towardZero \
          TowardPositive:up TowardNegative:down; do
        row "roundToIntegral${direction%%:*}" \
          "fun x _ => codeOf (Arithmetic.roundToIntegral .$format .${direction##*:} x)"
      done
      row roundToIntegralExact "fun x _ => codeOf (Arithmetic.roundToIntegralExact .$format .nearest x)"
      row nextUp "fun x _ => codeOf (Arithmetic.nextUp .$format x)"
      row nextDown "fun x _ => codeOf (Arithmetic.nextDown .$format x)"
      row remainder "fun x y => codeOf (Arithmetic.remainder .$format x y)"
      row quantize "fun x y => codeOf (Arithmetic.quantize .$format .nearest x y)"
      row quantum "fun x _ => codeOf (Arithmetic.quantum .$format x)"
      row scaleB "fun x _ => codeOf (Arithmetic.scale .$format .nearest x 3)"
      row logB "fun x _ => (Arithmetic.logB .$format x).value.natAbs"
      row addition "fun x y => codeOf (Arithmetic.add .$format .nearest x y)"
      row subtraction "fun x y => codeOf (Arithmetic.sub .$format .nearest x y)"
      row multiplication "fun x y => codeOf (Arithmetic.mul .$format .nearest x y)"
      row division "fun x y => codeOf (Arithmetic.div .$format .nearest x y)"
      row squareRoot "fun x _ => codeOf (Arithmetic.sqrt .$format .nearest (Datum.abs x))"
      row fusedMultiplyAdd "fun x y => codeOf (Arithmetic.fma .$format .nearest x y x)"
      row convertFromInt \
        "fun x _ => codeOf (Conversion.Integer.convertFromInt .$format .nearest (Int.ofNat (codeOf { value := x })))"
      for direction in TiesToEven:nearest TiesToAway:nearestAway TowardZero:towardZero \
          TowardPositive:up TowardNegative:down; do
        row "convertToInteger${direction%%:*}" \
          "fun x _ => (Conversion.Integer.convertToInteger (.signed 64) .${direction##*:} false x).value.natAbs"
        row "convertToIntegerExact${direction%%:*}" \
          "fun x _ => (Conversion.Integer.convertToInteger (.signed 64) .${direction##*:} true x).value.natAbs"
      done
      row "convertFormat" "fun x _ => codeOf (Conversion.convertFormat .decimal32 .nearest x)"
      row convertToDecimalCharacter "fun x _ => (Formatting.formatExact x).length"
      row convertFromDecimalCharacter \
        "fun x _ => codeOf (Formatting.parse .$format .nearest (Formatting.formatExact x))"
      row copy "fun x _ => codeOf { value := x.copy }"
      row negate "fun x _ => codeOf { value := x.negate }"
      row abs "fun x _ => codeOf { value := x.abs }"
      row copySign "fun x y => codeOf { value := x.copySign y }"
      row encodeDecimal "fun x _ => ((encodeDecimal .$format x).map BitVec.toNat).getD 0"
      row decodeDecimal \
        "fun x _ => codeOf { value := decodeDecimal .$format ((encodeDecimal .$format x).getD 0) }"
      row encodeBinary "fun x _ => ((encodeBinary .$format x).map BitVec.toNat).getD 0"
      row decodeBinary \
        "fun x _ => codeOf { value := decodeBinary .$format ((encodeBinary .$format x).getD 0) }"
      for predicate in Equal NotEqual Greater GreaterEqual Less LessEqual Unordered Ordered \
          LessUnordered NotGreater NotLess GreaterUnordered; do
        row "compareQuiet$predicate" "fun x y => (Datum.compareQuiet$predicate x y).value.toNat"
        if [[ "$predicate" != Unordered && "$predicate" != Ordered ]]; then
          row "compareSignaling$predicate" \
            "fun x y => (Datum.compareSignaling$predicate x y).value.toNat"
        fi
      done
      row class "fun x _ => (decide (x.classify .$format = .positiveNormal)).toNat"
      row isSignMinus "fun x _ => x.isSignMinus.toNat"
      row isNormal "fun x _ => (x.isNormal .$format).toNat"
      row isFinite "fun x _ => x.isFinite.toNat"
      row isZero "fun x _ => x.isZero.toNat"
      row isSubnormal "fun x _ => (x.isSubnormal .$format).toNat"
      row isInfinite "fun x _ => x.isInfinite.toNat"
      row isNaN "fun x _ => x.isNaN.toNat"
      row isSignaling "fun x _ => x.isSignaling.toNat"
      row radix "fun x _ => x.radix"
      row totalOrder "fun x y => (x.totalOrder y).toNat"
      row totalOrderMag "fun x y => (x.totalOrderMag y).toNat"
      row sameQuantum "fun x y => (x.sameQuantum y).toNat"
      row sum "fun x y => codeOf (Arithmetic.sum .$format .nearest #[x, y, x])"
      row dot "fun x y => (Arithmetic.dot .$format .nearest #[x, y] #[y, x]).toOption.elim 0 codeOf"
      row sumSquare "fun x y => codeOf (Arithmetic.sumSquare .$format .nearest #[x, y, x])"
      row sumAbs "fun x y => codeOf (Arithmetic.sumAbs .$format .nearest #[x, y, x])"
      for operation in minimum minimumNumber maximum maximumNumber minimumMagnitude \
          minimumMagnitudeNumber maximumMagnitude maximumMagnitudeNumber; do
        row "$operation" "fun x y => codeOf (Arithmetic.$operation .$format x y)"
      done
      row rSqrt "fun x _ => codeOf (Arithmetic.rSqrt .$format .nearest (Datum.abs x))"
      row hypot "fun x y => codeOf (Arithmetic.hypot .$format .nearest x y)"
      row pown "fun x _ => codeOf (Arithmetic.pown .$format .nearest x 5)"
      row rootn "fun x _ => codeOf (Arithmetic.rootn .$format .nearest x 3)"
      # The certified functions of clause 9.2 on operands of magnitude below one.
      for function in exp exp2 exp2m1 exp10 exp10m1 sin cos tan sinPi cosPi tanPi asin acos atan \
          asinPi acosPi atanPi sinh cosh tanh asinh atanh; do
        row "$function" \
          "fun x _ => certified (Transcendentals.Certified.$function .$format (small x))"
      done
      for function in log log2 log10 log2p1 log10p1; do
        row "$function" \
          "fun x _ => certified (Transcendentals.Certified.$function .$format (Datum.abs (small x)))"
      done
      row noop-payload "fun x _ => codeOf { value := Datum.setPayload .$format (Datum.abs x) }"
      row setPayload "fun x _ => codeOf { value := Datum.setPayload .$format (Datum.abs x) }"
      row setPayloadSignaling \
        "fun x _ => codeOf { value := Datum.setPayloadSignaling .$format (Datum.abs x) }"
      row getPayload \
        "fun x _ => codeOf { value := (Datum.setPayload .$format (Datum.abs x)).getPayload }"
    } > "$cell"
  else
    read -r ew fw bias <<<"$(layout "$format")"
    {
      cat <<EOF2
import FloatLib.Floats.Formats.BinaryInterchange.Configured
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Text.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
import FloatLib.Floats.Formats.BinaryInterchange.DType.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
import Harness
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLibBenchmarks.KernelReduction
set_option maxRecDepth 1000000

abbrev T := ExecFloat.Binary (exponentBits := $ew) (fractionBits := $fw)
def ofB (bits : Nat) : T := ExecFloat.Binary.ofNatBits bits
def toB (value : T) : Nat := ExecFloat.Binary.toNatBits value

/-- Fold a natural-number observation of three operands over a table. -/
def observe (op : T → T → T → Nat) (table : List (Nat × Nat × Nat)) : Nat :=
  table.foldl (fun acc t => Nat.add acc (op (ofB t.1) (ofB t.2.1) (ofB t.2.2))) 0

/-- The integral part of the magnitude of an operand, the preparation of the payload rows. -/
def integral (x : T) : T := ExecFloat.Binary.roundToIntegral (ExecFloat.Binary.abs x)

/-- An operand with its exponent field and its quiet bit set, the NaN that the \`getPayload\` row reads. -/
def quiet (x : T) : T :=
  ofB (Nat.lor (toB x)
    (Nat.add (Nat.mul (Nat.sub (Nat.pow 2 $ew) 1) (Nat.pow 2 $fw)) (Nat.pow 2 (Nat.sub $fw 1))))

/-- Head and tail of an augmented result as one number. -/
def augmented (outcome : AugmentedOutcome T) : Nat := Nat.add (toB outcome.head) (toB outcome.tail)

/-- Product and scale factor of a scaled product as one number. -/
def scaled (outcome : ScaledProduct T) : Nat :=
  Nat.add (toB outcome.product) outcome.scaleFactor.natAbs

/-- The same for a scaled product that may reject its operands. -/
def scaled? (outcome : Except FloatLib.Numerics.ReductionError (ScaledProduct T)) : Nat :=
  match outcome with
  | .ok value => scaled value
  | .error _ => 0

/-- A dot product that may reject its operands, as its encoding. -/
def dotted (outcome : Except FloatLib.Numerics.ReductionError T) : Nat :=
  match outcome with
  | .ok value => toB value
  | .error _ => 0

/-- The decoded operands of a reduction in the order they are added. -/
def terms (x y z : T) :=
  [ExecFloat.Binary.toModel x, ExecFloat.Binary.toModel y, ExecFloat.Binary.toModel z]

/-- A reduction accumulated in the format of the operand \`anchor\`, as the encoding of its result. -/
def inFormat {fmt : FloatFormat} (_anchor : Model fmt)
    (reduce : (acc out : FloatFormat) → Model out) : Nat :=
  (reduce fmt fmt).toNatBits

/-- A parsed value as its encoding. -/
def parsed (outcome : Except Model.ParseError T) : Nat :=
  match outcome with
  | .ok value => toB value
  | .error _ => 0

/-- The encoding of a binary32 value, the destination of the format conversion. -/
def toN (value : Binary32) : Nat := ExecFloat.Binary.toNatBits value

/-- A 64-bit integer from the encoding of an operand. -/
def fixed (x : T) : FloatLib.Numerics.Representations.FixedInt 64 :=
  FloatLib.Numerics.Representations.FixedInt.ofInt (Int.ofNat (toB x))

/-- Whether a conversion to a 64-bit integer succeeded. -/
def converted (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
    (FloatLib.Numerics.Representations.FixedInt 64)) : Nat :=
  match outcome with
  | .success _ _ => 1
  | .failure _ => 0
EOF2
      rewriting=" rewriting [observe, ofB, toB, toN, integral, quiet, augmented, scaled, scaled?, dotted, parsed, fixed, converted, terms, inFormat]"
      table="(operandTable% $ew $fw $bias true true normal additive $count)"
      row() { bench "$1" "observe ($2) $table"; }
      row noop 'fun x _ _ => toB x'
      for suffix in TiesToEven TiesToAway TowardZero TowardPositive TowardNegative; do
        row "roundToIntegral$suffix" "fun x _ _ => toB (ExecFloat.Binary.roundToIntegral$suffix x)"
      done
      row roundToIntegralExact 'fun x _ _ => toB (ExecFloat.Binary.roundToIntegralExact x).value'
      row nextUp 'fun x _ _ => toB (ExecFloat.Binary.nextUp x)'
      row nextDown 'fun x _ _ => toB (ExecFloat.Binary.nextDown x)'
      row remainder 'fun x y _ => toB (ExecFloat.Binary.remainder x y)'
      row scaleB 'fun x _ _ => toB (ExecFloat.Binary.scale x 3)'
      row logB 'fun x _ _ => toB (ExecFloat.Binary.logB x)'
      row addition 'fun x y _ => toB (x + y)'
      row subtraction 'fun x y _ => toB (x - y)'
      row multiplication 'fun x y _ => toB (x * y)'
      row division 'fun x y _ => toB (x / y)'
      row squareRoot 'fun x _ _ => toB (ExecFloat.sqrt (ExecFloat.Binary.abs x))'
      row fusedMultiplyAdd 'fun x y z => toB (ExecFloat.fma x y z)'
      for operation in Addition Subtraction Multiplication Division; do
        row "formatOf$operation" \
          "fun x y _ => toN (ExecFloat.Binary.ofModel (Model.formatOf$operation _ (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)).value)"
      done
      row formatOfFusedMultiplyAdd \
        'fun x y z => toN (ExecFloat.Binary.ofModel (Model.formatOfFusedMultiplyAdd _ (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel z)).value)'
      row convertFromInt \
        'fun x _ _ => toB (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _ (fixed x)))'
      for suffix in TiesToEven TiesToAway TowardZero TowardPositive TowardNegative; do
        row "convertToInteger$suffix" \
          "fun x _ _ => ((ExecFloat.Binary.convertToInteger$suffix x).getD 0).natAbs"
        row "convertToIntegerExact$suffix" \
          "fun x _ _ => converted (ExecDType.convertToIntegerExact$suffix (ExecFloat.Binary.toModel x))"
      done
      row convertFormat \
        'fun x _ _ => toN (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x) .nearest))'
      row convertToDecimalCharacter 'fun x _ _ => (ExecFloat.Binary.format x).length'
      row convertFromDecimalCharacter 'fun x _ _ => parsed (ExecFloat.Binary.parse (ExecFloat.Binary.format x))'
      row convertToHexCharacter 'fun x _ _ => (ExecFloat.Binary.format x (.hex)).length'
      row convertFromHexCharacter \
        'fun x _ _ => parsed (ExecFloat.Binary.parse (ExecFloat.Binary.format x (.hex)))'
      row copy 'fun x _ _ => toB (ExecFloat.Binary.copy x)'
      row negate 'fun x _ _ => toB (-x)'
      row abs 'fun x _ _ => toB (ExecFloat.Binary.abs x)'
      row copySign 'fun x y _ => toB (ExecFloat.Binary.copySign x y)'
      for predicate in Equal NotEqual Greater GreaterEqual Less LessEqual Unordered Ordered \
          LessUnordered NotGreater NotLess GreaterUnordered; do
        row "compareQuiet$predicate" \
          "fun x y _ => (ExecFloat.Binary.compareQuiet$predicate x y).value.toNat"
        if [[ "$predicate" != Unordered && "$predicate" != Ordered ]]; then
          row "compareSignaling$predicate" \
            "fun x y _ => (ExecFloat.Binary.compareSignaling$predicate x y).value.toNat"
        fi
      done
      row class 'fun x _ _ => (decide (ExecFloat.Binary.classify x = .positiveNormal)).toNat'
      row isSignMinus 'fun x _ _ => (ExecFloat.Binary.signBit x).toNat'
      for predicate in isNormal isFinite isZero isSubnormal isInfinite isNaN isSignaling isCanonical; do
        row "$predicate" "fun x _ _ => (ExecFloat.Binary.$predicate x).toNat"
      done
      row radix 'fun x _ _ => ExecFloat.Binary.radix x'
      row totalOrder 'fun x y _ => (ExecFloat.Binary.totalOrder x y).toNat'
      row totalOrderMag 'fun x y _ => (ExecFloat.Binary.totalOrderMag x y).toNat'
      row sum 'fun x y z => toB (ExecFloat.Binary.sum #[x, y, z])'
      row dot 'fun x y z => dotted (ExecFloat.Binary.dot #[x, y] #[y, z])'
      row sumSquare 'fun x y z => toB (ExecFloat.Binary.sumSquare #[x, y, z])'
      row sumAbs 'fun x y z => toB (ExecFloat.Binary.sumAbs #[x, y, z])'
      row scaledProd 'fun x y z => scaled (ExecFloat.Binary.scaledProd #[x, y, z])'
      row scaledProdSum 'fun x y z => scaled? (ExecFloat.Binary.scaledProdSum #[x, y] #[y, z])'
      row scaledProdDiff 'fun x y z => scaled? (ExecFloat.Binary.scaledProdDiff #[x, y] #[y, z])'
      row sumInOrder 'fun x y z => inFormat (ExecFloat.Binary.toModel x) fun acc out => Model.sumInOrder acc out (terms x y z)'
      row sumAbsInOrder 'fun x y z => inFormat (ExecFloat.Binary.toModel x) fun acc out => Model.sumAbsInOrder acc out (terms x y z)'
      row sumSquareInOrder \
        'fun x y z => inFormat (ExecFloat.Binary.toModel x) fun acc out => Model.sumSquareInOrder acc out (terms x y z)'
      row dotInOrder \
        'fun x y z => inFormat (ExecFloat.Binary.toModel x) fun acc out => Model.dotInOrder acc out ((terms x y z).zip (terms y z x))'
      row sumAlong \
        'fun x y z => inFormat (ExecFloat.Binary.toModel x) fun acc out => Model.sumAlong acc out (.node (.leaf (ExecFloat.Binary.toModel x)) (.node (.leaf (ExecFloat.Binary.toModel y)) (.leaf (ExecFloat.Binary.toModel z))))'
      row augmentedAddition 'fun x y _ => augmented (ExecFloat.Binary.augmentedAddition x y)'
      row augmentedSubtraction 'fun x y _ => augmented (ExecFloat.Binary.augmentedSubtraction x y)'
      row augmentedMultiplication \
        'fun x y _ => augmented (ExecFloat.Binary.augmentedMultiplication x y)'
      for operation in minimum minimumNumber maximum maximumNumber minimumMagnitude \
          minimumMagnitudeNumber maximumMagnitude maximumMagnitudeNumber; do
        row "$operation" "fun x y _ => toB (ExecFloat.Binary.$operation x y)"
      done
      row rSqrt 'fun x _ _ => toB (ExecFloat.Binary.rSqrt (ExecFloat.Binary.abs x))'
      row hypot 'fun x y _ => toB (ExecFloat.Binary.hypot x y)'
      row pown 'fun x _ _ => toB (ExecFloat.Binary.pown x 5)'
      row rootn 'fun x _ _ => toB (ExecFloat.Binary.rootn x 3)'
      # The recommended functions of clause 9.2, to nearest-even: the value of the outcome. The
      # operands have magnitudes between 1 and 2, scaled into the domain where it is smaller.
      for function in exp expm1; do
        row "$function" "fun x _ _ => toB (ExecFloat.Binary.CorrectlyRounded.$function x)"
      done
      for function in log logp1; do
        row "$function" \
          "fun x _ _ => toB (ExecFloat.Binary.CorrectlyRounded.$function (ExecFloat.Binary.abs x))"
      done
      for function in exp2 exp2m1 exp10 exp10m1 sin cos tan sinPi cosPi tanPi atan atanPi sinh \
          cosh tanh asinh; do
        row "$function" "fun x _ _ => toB (ExecFloat.Binary.CorrectlyRounded.$function x).value"
      done
      for function in log2 log10 log2p1 log10p1 acosh; do
        row "$function" \
          "fun x _ _ => toB (ExecFloat.Binary.CorrectlyRounded.$function (ExecFloat.Binary.abs x)).value"
      done
      for function in asin acos asinPi acosPi atanh; do
        row "$function" \
          "fun x _ _ => toB (ExecFloat.Binary.CorrectlyRounded.$function (ExecFloat.Binary.scale x (-2))).value"
      done
      row atan2 'fun x y _ => toB (ExecFloat.Binary.CorrectlyRounded.atan2 x y).value'
      row atan2Pi 'fun x y _ => toB (ExecFloat.Binary.CorrectlyRounded.atan2Pi x y).value'
      row powr \
        'fun x y _ => toB (ExecFloat.Binary.CorrectlyRounded.powr (ExecFloat.Binary.abs x) y).value'
      row compound \
        'fun x _ _ => toB (ExecFloat.Binary.CorrectlyRounded.compound (ExecFloat.Binary.scale x (-4)) 5).value'
      row noop-integral 'fun x _ _ => toB (integral x)'
      row setPayload 'fun x _ _ => toB (ExecFloat.Binary.setPayload (integral x))'
      row setPayloadSignaling 'fun x _ _ => toB (ExecFloat.Binary.setPayloadSignaling (integral x))'
      row noop-nan 'fun x _ _ => toB (quiet x)'
      row getPayload 'fun x _ _ => toB (ExecFloat.Binary.getPayload (quiet x))'
    } > "$cell"
  fi
  echo "== $format" | tee -a "$log"
  if [[ -n "${KERNEL_BENCH_ROW_TIMEOUT:-}" ]]; then
    rows="$work/rows_$format"
    mkdir -p "$rows"
    grep -v '^#kernel_bench ' "$cell" > "$rows/prelude"
    number=0
    while IFS= read -r line; do
      number=$((number + 1))
      { cat "$rows/prelude"; printf '%s\n' "$line"; } > "$(printf '%s/Row%04d.lean' "$rows" "$number")"
    done < <(grep '^#kernel_bench ' "$cell")
    # A row of a certified function of clause 9.2 has its own limit.
    function_rows='^#kernel_bench .*(CorrectlyRounded|Transcendentals\.Certified)\.'
    function_limit="${KERNEL_BENCH_FUNCTION_ROW_TIMEOUT:-$KERNEL_BENCH_ROW_TIMEOUT}"
    printf '%s\n' "$rows"/Row*.lean | LEAN_PATH="$work:$lean_path" \
      xargs -P "${KERNEL_BENCH_JOBS:-1}" -I{} bash -c \
        'limit="$1"; grep -qE "$5" "$3" && limit="$4"
         timeout --kill-after=10 "$limit" "$2" "$3" > "${3%.lean}.out" 2>&1; echo "$?" > "${3%.lean}.exit"' \
        _ "$KERNEL_BENCH_ROW_TIMEOUT" "$lean" {} "$function_limit" "$function_rows" || true
    for file in "$rows"/Row*.lean; do
      label="$(sed -n 's/^#kernel_bench "\([^"]*\)".*/\1/p' "$file")"
      if grep -q '^KBENCH ' "${file%.lean}.out"; then
        grep '^KBENCH ' "${file%.lean}.out" | cut -c1-200 | tee -a "$log"
      else
        limit="$KERNEL_BENCH_ROW_TIMEOUT"
        if grep -qE "$function_rows" "$file"; then limit="$function_limit"; fi
        echo "KBENCH-FAILED $label: exit $(cat "${file%.lean}.exit") (124 means no result within $limit s)" \
          | tee -a "$log"
      fi
    done
  else
    limit="${KERNEL_BENCH_TIMEOUT:-900}"
    LEAN_PATH="$work:$lean_path" timeout --kill-after=10 "$limit" "$lean" "$cell" \
      2>&1 | cut -c1-200 | tee -a "$log" || true
    status="${PIPESTATUS[0]}"
    if [[ "$status" -ne 0 ]]; then
      echo "KBENCH-FAILED $format: exit $status (124 means no result within $limit s)" | tee -a "$log"
    fi
  fi
done

awk -v n="$count" '
  $1 == "KBENCH" {
    f = $2; op = $3; path = $4; t = $5
    if (op ~ /^noop/) { base[f, op, path] = t; next }
    kind = ((op == "setPayload" || op == "setPayloadSignaling") && f !~ /^decimal/) ? "noop-integral" : \
      (op == "getPayload" && f !~ /^decimal/) ? "noop-nan" : \
      (op == "getPayload") ? "noop-payload" : "noop"
    us[f, op, path] = (t - base[f, kind, path]) / n / 1000
    group = (f ~ /^decimal/) ? "decimal" : "binary"
    if (!((group, f) in formatSeen)) { formatSeen[group, f] = 1; formats[group, ++nf[group]] = f }
    if (!((group, op) in opSeen)) { opSeen[group, op] = 1; ops[group, ++no[group]] = op }
  }
  function table(group,   i, j, p, key) {
    if (nf[group] == 0) return
    printf "| operation |"
    for (i = 1; i <= nf[group]; i++)
      printf " %s as written | %s with the rules |", formats[group, i], formats[group, i]
    print ""
    printf "| --- |"
    for (i = 1; i <= nf[group]; i++) printf " ---: | ---: |"
    print ""
    for (j = 1; j <= no[group]; j++) {
      printf "| %s |", ops[group, j]
      for (i = 1; i <= nf[group]; i++) {
        split("public kernel", paths, " ")
        for (p = 1; p <= 2; p++) {
          key = formats[group, i] SUBSEP ops[group, j] SUBSEP paths[p]
          if (key in us) printf " %.0f |", us[key]; else printf " n/a |"
        }
      }
      print ""
    }
    print ""
  }
  END { table("binary"); table("decimal") }' "$log" > "$out/ieee2019.md"
echo "microseconds of kernel time per operation ($count operand triples, fastest of $reps):"
cat "$out/ieee2019.md"
