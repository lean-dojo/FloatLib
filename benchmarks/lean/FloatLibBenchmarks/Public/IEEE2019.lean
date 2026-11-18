/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Power
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Predicates.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.BoundedParsing
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Runtime
import FloatLib.Floats.Formats.DecimalInterchange
import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Recommended.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Recommended.Runtime

/-!
# Compiled time of the operations of IEEE 754-2019

`execFloatIEEE2019` times, in compiled code, the operations of IEEE 754-2019 clauses 5 and 9
under their names in the standard: on the descriptor model of eight binary formats of 8 to
4,096 bits, and on decimal32, decimal64 and decimal128, where addition, subtraction and
multiplication are timed both by the specification and by the kernel path. The formatOf rows
round into binary32 from operands of the row's format. The decimal rows end with the 26
certified functions of §9.2 (`exp2` to `compound`).

`execFloatIEEE2019 functions FORMAT [COUNT [NAME]]` times the recommended functions of §9.2 in
one binary format instead: the 26 functions of one argument, `atan2`, `atan2Pi`, `powr` and
`compound`, or the one called `NAME`, and then of `exp`, `expm1`, `log`, `logp1`, `pow`, `rSqrt`,
`hypot`, `pown` and `rootn`. The first thirty round by exact comparisons and take milliseconds
to seconds, so a row is one pass over `COUNT` operands (eight by default), the faster of two
passes, or a single pass for fewer than four operands. The operands are those of the other
rows, of magnitude between 1/8 and 16, scaled into the domain where a function has one: by
1/16 for the inverse sine, cosine and hyperbolic tangent and for `compound`, and by 8 for the
inverse hyperbolic cosine.

Each row runs one operation over 64 deterministic operand triples, repeated until 20
milliseconds have passed, in five trials, and reports the fastest trial as nanoseconds for one
operation. The reductions take eight operands, so their time is for eight elements. The rows
`sumInOrder` to `sumAlong` are the reductions of §9.4 with one rounding at each addition
(`Reduction.Schedule`), accumulated in the format of the row, from left to right and along a
balanced association order. The output
is CSV: `radix,format,bits,operation,nanoseconds,checksum`. The checksum is the sum of the
results of one pass, which keeps the compiler from removing the work.
-/

open FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.Public.IEEE2019

/-- One step of a 64-bit xorshift generator. -/
def next (state : UInt64) : UInt64 :=
  let state := state ^^^ (state <<< 13)
  let state := state ^^^ (state >>> 7)
  state ^^^ (state <<< 17)

/-- `bits` pseudo-random bits and the generator state after drawing them. -/
def randomBits (bits : Nat) (state : UInt64) : Nat × UInt64 := Id.run do
  let mut value := 0
  let mut state := state
  for _ in [0:bits / 64 + 1] do
    state := next state
    value := value * 2 ^ 64 + state.toNat
  return (value % 2 ^ bits, state)

/--
`count` normal numbers of `fmt` with exponents within three of zero, random signs and random
fractions: magnitudes between 1/8 and 16.
-/
def operands (fmt : FloatFormat) (count : Nat) (seed : UInt64) : Array (Model fmt) := Id.run do
  let mut state := seed
  let mut values := #[]
  for _ in [0:count] do
    let (fraction, afterFraction) := randomBits fmt.fracWidth state
    state := next afterFraction
    let exponent := fmt.exponentBias + state.toNat % 7 - 3
    let sign := (state >>> 40).toNat % 2
    values := values.push
      (Model.ofNatBits (sign * 2 ^ (fmt.expWidth + fmt.fracWidth) + exponent * 2 ^ fmt.fracWidth +
        fraction))
  return values

/-- The fastest of five trials, as nanoseconds for one call, and the checksum of one pass. -/
def measure {α : Type} (values : Array α) (operation : α → α → α → Nat) : IO (Nat × Nat) := do
  let size := values.size
  let some first := values[0]? | return (0, 0)
  let pass (total : Nat) : Nat := Id.run do
    let mut total := total
    for index in [0:size] do
      total := total + operation (values.getD index first)
        (values.getD ((index + 1) % size) first) (values.getD ((index + 2) % size) first)
    return total
  let checksum := pass 0
  let mut best := 0
  for trial in [0:5] do
    let start ← IO.monoNanosNow
    let mut passes := 0
    let mut total := 0
    let mut elapsed := 0
    while elapsed < 20000000 do
      total := pass total
      passes := passes + 1
      elapsed := (← IO.monoNanosNow) - start
    -- The total is read so that the passes are not removed.
    if total == 0 && checksum != 0 then throw (IO.userError "an operation returned no result")
    let perCall := elapsed / (passes * size)
    if trial == 0 || perCall < best then best := perCall
  return (best, checksum)

/-- Print one CSV row. -/
def row {α : Type} (radix format : String) (bits : Nat) (name : String) (values : Array α)
    (operation : α → α → α → Nat) : IO Unit := do
  let (nanoseconds, checksum) ← measure values operation
  IO.println s!"{radix},{format},{bits},{name},{nanoseconds},{checksum % 1000000007}"

/-- Head and tail of an augmented result as one number. -/
def augmentedCode {fmt : FloatFormat} (outcome : AugmentedOutcome (Model fmt)) : Nat :=
  outcome.head.toNatBits + outcome.tail.toNatBits

/-- Product and scale factor of a scaled product as one number. -/
def scaledCode {fmt : FloatFormat} (outcome : ScaledProduct (Model fmt)) : Nat :=
  outcome.product.toNatBits + outcome.scaleFactor.natAbs

/-- The same for a scaled product that may reject its operands. -/
def scaledCode? {fmt : FloatFormat}
    (outcome : Except FloatLib.Numerics.ReductionError (ScaledProduct (Model fmt))) : Nat :=
  match outcome with
  | .ok value => scaledCode value
  | .error _ => 0

/-- Eight operands for a reduction, from three. -/
def eight {fmt : FloatFormat} (x y z : Model fmt) : Array (Model fmt) :=
  #[x, y, z, Model.neg x, Model.abs y, Model.neg z, x, y]

/-- The eight elements of `eight` under the balanced association order `((a b) (c d)) ((e f) (g h))`. -/
def pairwise {fmt : FloatFormat} (x y z : Model fmt) : FloatLib.Numerics.ReductionTree (Model fmt) :=
  .node (.node (.node (.leaf x) (.leaf y)) (.node (.leaf z) (.leaf (Model.neg x))))
    (.node (.node (.leaf (Model.abs y)) (.leaf (Model.neg z))) (.node (.leaf x) (.leaf y)))

/-- The rounding directions with the suffixes of the operation names. -/
def directions : List (String × Model.IEEERoundingMode) :=
  [("TiesToEven", .nearest), ("TiesToAway", .nearestAway), ("TowardZero", .towardZero),
    ("TowardPositive", .up), ("TowardNegative", .down)]

/-- The comparison predicates with the suffixes of the operation names. -/
def predicates : List (String × FloatLib.Numerics.IEEEComparison.Predicate) :=
  [("Equal", .equal), ("NotEqual", .notEqual), ("Greater", .greater),
    ("GreaterEqual", .greaterEqual), ("Less", .less), ("LessEqual", .lessEqual),
    ("Unordered", .unordered), ("Ordered", .ordered), ("LessUnordered", .lessUnordered),
    ("NotGreater", .notGreater), ("NotLess", .notLess), ("GreaterUnordered", .greaterUnordered)]

/-- All rows of one binary format. -/
def binaryRows (name : String) (fmt : FloatFormat) : IO Unit := do
  let values := operands fmt 64 0x9E3779B97F4A7C15
  let quiet : Array (Model fmt) := values.map fun x => Model.setPayload (Model.roundToIntegral (Model.abs x))
  let texts : Array String := values.map fun x => Model.format x
  let hexTexts : Array String := values.map fun x => Model.format x (.hex)
  let bits := fmt.expWidth + fmt.fracWidth + 1
  let timed := row (α := Model fmt) "binary" name bits
  let integer (x : Model fmt) : FloatLib.Numerics.Representations.FixedInt 64 :=
    FloatLib.Numerics.Representations.FixedInt.ofInt ((x.toNatBits % 1000003 : Nat) : Int)
  let converted (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Numerics.Representations.FixedInt 64)) : Nat :=
    match outcome with
    | .success _ _ => 1
    | .failure _ => 0
  let parsed (outcome : Except Model.ParseError (Model fmt)) : Nat :=
    match outcome with
    | .ok value => value.toNatBits
    | .error _ => 0
  -- Clause 5.3.1
  for (suffix, mode) in directions do
    timed s!"roundToIntegral{suffix}" values fun x _ _ => (Model.roundToIntegral x mode).toNatBits
  timed "roundToIntegralExact" values fun x _ _ => (Model.roundToIntegralExact x).value.toNatBits
  timed "nextUp" values fun x _ _ => (Model.nextUp x).toNatBits
  timed "nextDown" values fun x _ _ => (Model.nextDown x).toNatBits
  timed "remainder" values fun x y _ => (Model.remainder x y).toNatBits
  -- Clause 5.3.3
  timed "scaleB" values fun x _ _ => (Model.scale x 3).toNatBits
  timed "logB" values fun x _ _ => (Model.logB x).toNatBits
  -- Clause 5.4.1
  timed "addition" values fun x y _ => (Model.add x y).toNatBits
  timed "subtraction" values fun x y _ => (Model.sub x y).toNatBits
  timed "multiplication" values fun x y _ => (Model.mul x y).toNatBits
  timed "division" values fun x y _ => (Model.div x y).toNatBits
  timed "squareRoot" values fun x _ _ => (Model.sqrt (Model.abs x)).toNatBits
  timed "fusedMultiplyAdd" values fun x y z => (Model.fma x y z).toNatBits
  -- Clause 5.4.1 with the destination binary32, whatever the format of the operands
  timed "formatOfAddition" values fun x y _ =>
    (Model.formatOfAddition FloatFormat.binary32 x y).value.toNatBits
  timed "formatOfSubtraction" values fun x y _ =>
    (Model.formatOfSubtraction FloatFormat.binary32 x y).value.toNatBits
  timed "formatOfMultiplication" values fun x y _ =>
    (Model.formatOfMultiplication FloatFormat.binary32 x y).value.toNatBits
  timed "formatOfDivision" values fun x y _ =>
    (Model.formatOfDivision FloatFormat.binary32 x y).value.toNatBits
  timed "formatOfFusedMultiplyAdd" values fun x y z =>
    (Model.formatOfFusedMultiplyAdd FloatFormat.binary32 x y z).value.toNatBits
  timed "convertFromInt" values fun x _ _ => (ExecDType.convertFromInt fmt (integer x)).toNatBits
  for (suffix, mode) in directions do
    timed s!"convertToInteger{suffix}" values fun x _ _ =>
      converted (ExecDType.convertToInteger x mode)
  for (suffix, mode) in directions do
    timed s!"convertToIntegerExact{suffix}" values fun x _ _ =>
      converted (ExecDType.convertToIntegerExact x mode)
  -- Clauses 5.4.2 and 5.4.3
  timed "convertFormat (to binary32)" values fun x _ _ =>
    (Model.cast fmt FloatFormat.binary32 x).toNatBits
  row "binary" name bits "convertFromDecimalCharacter" texts fun text _ _ => parsed (Model.parse fmt text)
  timed "convertToDecimalCharacter" values fun x _ _ => (Model.format x).length
  row "binary" name bits "convertFromHexCharacter" hexTexts fun text _ _ => parsed (Model.parse fmt text)
  timed "convertToHexCharacter" values fun x _ _ => (Model.format x (.hex)).length
  -- Clause 5.5.1
  timed "copy" values fun x _ _ => (Model.copy x).toNatBits
  timed "negate" values fun x _ _ => (Model.neg x).toNatBits
  timed "abs" values fun x _ _ => (Model.abs x).toNatBits
  timed "copySign" values fun x y _ => (Model.copySign x y).toNatBits
  -- Clause 5.6.1
  for (suffix, predicate) in predicates do
    timed s!"compareQuiet{suffix}" values fun x y _ => (Model.compareQuiet predicate x y).value.toNat
  for (suffix, predicate) in predicates do
    unless suffix == "Unordered" || suffix == "Ordered" do
      timed s!"compareSignaling{suffix}" values fun x y _ =>
        (Model.compareSignaling predicate x y).value.toNat
  -- Clause 5.7.2
  timed "class" values fun x _ _ => if Model.classify x == .positiveNormal then 1 else 0
  timed "isSignMinus" values fun x _ _ => (Model.signBit x).toNat
  timed "isNormal" values fun x _ _ => (Model.isNormal x).toNat
  timed "isFinite" values fun x _ _ => (Model.isFinite x).toNat
  timed "isZero" values fun x _ _ => (Model.isZero x).toNat
  timed "isSubnormal" values fun x _ _ => (Model.isSubnormal x).toNat
  timed "isInfinite" values fun x _ _ => (Model.isInfinite x).toNat
  timed "isNaN" values fun x _ _ => (Model.isNaN x).toNat
  timed "isSignaling" values fun x _ _ => (Model.isSignaling x).toNat
  timed "isCanonical" values fun x _ _ => (Model.isCanonical x).toNat
  timed "radix" values fun x _ _ => Model.radix x
  timed "totalOrder" values fun x y _ => (Model.totalOrder x y).toNat
  timed "totalOrderMag" values fun x y _ => (Model.totalOrderMag x y).toNat
  -- Clause 9.4
  timed "sum (8 elements)" values fun x y z => (Model.sum fmt (eight x y z)).toNatBits
  timed "dot (8 pairs)" values fun x y z =>
    match Model.dot fmt (eight x y z) (eight y z x) with
    | .ok value => value.toNatBits
    | .error _ => 0
  timed "sumSquare (8 elements)" values fun x y z => (Model.sumSquare fmt (eight x y z)).toNatBits
  timed "sumAbs (8 elements)" values fun x y z => (Model.sumAbs fmt (eight x y z)).toNatBits
  timed "scaledProd (8 elements)" values fun x y z => scaledCode (Model.scaledProd fmt (eight x y z))
  timed "scaledProdSum (8 pairs)" values fun x y z =>
    scaledCode? (Model.scaledProdSum fmt (eight x y z) (eight y z x))
  timed "scaledProdDiff (8 pairs)" values fun x y z =>
    scaledCode? (Model.scaledProdDiff fmt (eight x y z) (eight y z x))
  -- Clause 9.4 with one rounding at each addition, accumulated in the format of the row
  timed "sumInOrder (8 elements)" values fun x y z =>
    (Model.sumInOrder fmt fmt (eight x y z).toList).toNatBits
  timed "sumAbsInOrder (8 elements)" values fun x y z =>
    (Model.sumAbsInOrder fmt fmt (eight x y z).toList).toNatBits
  timed "sumSquareInOrder (8 elements)" values fun x y z =>
    (Model.sumSquareInOrder fmt fmt (eight x y z).toList).toNatBits
  timed "dotInOrder (8 pairs)" values fun x y z =>
    (Model.dotInOrder fmt fmt ((eight x y z).toList.zip (eight y z x).toList)).toNatBits
  timed "sumAlong (8 elements in pairs)" values fun x y z =>
    (Model.sumAlong fmt fmt (pairwise x y z)).toNatBits
  -- Clause 9.5
  timed "augmentedAddition" values fun x y _ => augmentedCode (Model.augmentedAddition x y)
  timed "augmentedSubtraction" values fun x y _ => augmentedCode (Model.augmentedSubtraction x y)
  timed "augmentedMultiplication" values fun x y _ =>
    augmentedCode (Model.augmentedMultiplication x y)
  -- Clause 9.6
  timed "minimum" values fun x y _ => (Model.minimum x y).toNatBits
  timed "minimumNumber" values fun x y _ => (Model.minimumNumber x y).toNatBits
  timed "maximum" values fun x y _ => (Model.maximum x y).toNatBits
  timed "maximumNumber" values fun x y _ => (Model.maximumNumber x y).toNatBits
  timed "minimumMagnitude" values fun x y _ => (Model.minimumMagnitude x y).toNatBits
  timed "minimumMagnitudeNumber" values fun x y _ => (Model.minimumMagnitudeNumber x y).toNatBits
  timed "maximumMagnitude" values fun x y _ => (Model.maximumMagnitude x y).toNatBits
  timed "maximumMagnitudeNumber" values fun x y _ => (Model.maximumMagnitudeNumber x y).toNatBits
  -- Clause 9.7
  timed "getPayload" quiet fun x _ _ => (Model.getPayload x).toNatBits
  timed "setPayload" values fun x _ _ =>
    (Model.setPayload (Model.roundToIntegral (Model.abs x))).toNatBits
  timed "setPayloadSignaling" values fun x _ _ =>
    (Model.setPayloadSignaling (Model.roundToIntegral (Model.abs x))).toNatBits

/-- `count` decimal data with full coefficients and quantum exponents within the precision. -/
def decimalOperands (f : DecimalInterchange.Format) (count : Nat) (seed : UInt64) :
    Array DecimalInterchange.Datum := Id.run do
  let mut state := seed
  let mut values := #[]
  for _ in [0:count] do
    let (coefficient, afterCoefficient) := randomBits (4 * f.precision) state
    state := next afterCoefficient
    let exponent : Int := (state.toNat % (2 * f.precision) : Nat) - (f.precision : Int)
    values := values.push
      (.finite ((state >>> 40).toNat % 2 == 1) (coefficient % 10 ^ f.precision) exponent)
  return values

/-- One number of a decimal outcome: the coefficient and the flags. -/
def outcomeCode (outcome : DecimalInterchange.Outcome) : Nat :=
  (match outcome.value with
    | .finite _ coefficient _ => coefficient
    | .infinity _ => 1
    | .nan _ _ payload => payload) + (if outcome.status.inexact then 1 else 0)

/-- The decimal rounding directions with the suffixes of the operation names. -/
def decimalDirections : List (String × DecimalInterchange.RoundingMode) :=
  [("TiesToEven", .nearest), ("TiesToAway", .nearestAway), ("TowardZero", .towardZero),
    ("TowardPositive", .up), ("TowardNegative", .down)]

open DecimalInterchange in
/-- All rows of one decimal format. -/
def decimalRows (name : String) (f : DecimalInterchange.Format) : IO Unit := do
  let values := decimalOperands f 64 0xD1B54A32D192ED03
  let nans : Array Datum := values.map fun x =>
    match x with
    | .finite s c _ => .nan s false (c % f.payloadBound)
    | other => other
  let texts : Array String := values.map fun x => Formatting.formatExact x
  let words : Array (BitVec f.bitWidth) := values.map fun x => (encodeDecimal f x).getD 0
  let binaryWords : Array (BitVec f.bitWidth) := values.map fun x => (encodeBinary f x).getD 0
  let timed := row (α := Datum) "decimal" name f.bitWidth
  let datumCode (x : Datum) : Nat := outcomeCode { value := x }
  -- Clause 5.3.1
  for (suffix, mode) in decimalDirections do
    timed s!"roundToIntegral{suffix}" values fun x _ _ =>
      outcomeCode (Arithmetic.roundToIntegral f mode x)
  timed "roundToIntegralExact" values fun x _ _ =>
    outcomeCode (Arithmetic.roundToIntegralExact f .nearest x)
  timed "nextUp" values fun x _ _ => outcomeCode (Arithmetic.nextUp f x)
  timed "nextDown" values fun x _ _ => outcomeCode (Arithmetic.nextDown f x)
  timed "remainder" values fun x y _ => outcomeCode (Arithmetic.remainder f x y)
  -- Clause 5.3.2
  timed "quantize" values fun x y _ => outcomeCode (Arithmetic.quantize f .nearest x y)
  timed "quantum" values fun x _ _ => outcomeCode (Arithmetic.quantum f x)
  -- Clause 5.3.3
  timed "scaleB" values fun x _ _ => outcomeCode (Arithmetic.scale f .nearest x 3)
  timed "logB" values fun x _ _ => (Arithmetic.logB f x).value.natAbs
  -- Clause 5.4.1
  timed "addition" values fun x y _ => outcomeCode (Arithmetic.add f .nearest x y)
  timed "addition (kernel path)" values fun x y _ => outcomeCode (KernelPath.add f .nearest x y)
  timed "subtraction" values fun x y _ => outcomeCode (Arithmetic.sub f .nearest x y)
  timed "subtraction (kernel path)" values fun x y _ => outcomeCode (KernelPath.sub f .nearest x y)
  timed "multiplication" values fun x y _ => outcomeCode (Arithmetic.mul f .nearest x y)
  timed "multiplication (kernel path)" values fun x y _ => outcomeCode (KernelPath.mul f .nearest x y)
  timed "division" values fun x y _ => outcomeCode (Arithmetic.div f .nearest x y)
  timed "squareRoot" values fun x _ _ => outcomeCode (Arithmetic.sqrt f .nearest x.abs)
  timed "fusedMultiplyAdd" values fun x y z => outcomeCode (Arithmetic.fma f .nearest x y z)
  timed "convertFromInt" values fun x _ _ =>
    outcomeCode (Conversion.Integer.convertFromInt f .nearest ((datumCode x % 1000003 : Nat) : Int))
  for (suffix, mode) in decimalDirections do
    timed s!"convertToInteger{suffix}" values fun x _ _ =>
      (Conversion.Integer.convertToInteger (.signed 64) mode false x).value.natAbs
  for (suffix, mode) in decimalDirections do
    timed s!"convertToIntegerExact{suffix}" values fun x _ _ =>
      (Conversion.Integer.convertToInteger (.signed 64) mode true x).value.natAbs
  -- Clause 5.4.2
  timed "convertFormat (to decimal32)" values fun x _ _ =>
    outcomeCode (Conversion.convertFormat .decimal32 .nearest x)
  row "decimal" name f.bitWidth "convertFromDecimalCharacter" texts fun text _ _ => outcomeCode (Formatting.parse f .nearest text)
  timed "convertToDecimalCharacter" values fun x _ _ => (Formatting.formatExact x).length
  -- Clause 5.5.1
  timed "copy" values fun x _ _ => datumCode x.copy
  timed "negate" values fun x _ _ => datumCode x.negate
  timed "abs" values fun x _ _ => datumCode x.abs
  timed "copySign" values fun x y _ => datumCode (x.copySign y)
  -- Clause 5.5.2
  timed "encodeDecimal" values fun x _ _ => ((encodeDecimal f x).map BitVec.toNat).getD 0
  row "decimal" name f.bitWidth "decodeDecimal" words fun word _ _ => datumCode (decodeDecimal f word)
  timed "encodeBinary" values fun x _ _ => ((encodeBinary f x).map BitVec.toNat).getD 0
  row "decimal" name f.bitWidth "decodeBinary" binaryWords fun word _ _ => datumCode (decodeBinary f word)
  -- Clause 5.6.1
  for (suffix, predicate) in predicates do
    timed s!"compareQuiet{suffix}" values fun x y _ => (Datum.compareQuiet predicate x y).value.toNat
  for (suffix, predicate) in predicates do
    unless suffix == "Unordered" || suffix == "Ordered" do
      timed s!"compareSignaling{suffix}" values fun x y _ =>
        (Datum.compareSignaling predicate x y).value.toNat
  -- Clauses 5.7.2 and 5.7.3
  timed "class" values fun x _ _ => if x.classify f == .positiveNormal then 1 else 0
  timed "isSignMinus" values fun x _ _ => x.isSignMinus.toNat
  timed "isNormal" values fun x _ _ => (x.isNormal f).toNat
  timed "isFinite" values fun x _ _ => x.isFinite.toNat
  timed "isZero" values fun x _ _ => x.isZero.toNat
  timed "isSubnormal" values fun x _ _ => (x.isSubnormal f).toNat
  timed "isInfinite" values fun x _ _ => x.isInfinite.toNat
  timed "isNaN" values fun x _ _ => x.isNaN.toNat
  timed "isSignaling" values fun x _ _ => x.isSignaling.toNat
  row "decimal" name f.bitWidth "isCanonical" words fun word _ _ => (Encoding.dpd.isCanonical f word).toNat
  timed "radix" values fun x _ _ => x.radix
  timed "totalOrder" values fun x y _ => (x.totalOrder y).toNat
  timed "totalOrderMag" values fun x y _ => (x.totalOrderMag y).toNat
  timed "sameQuantum" values fun x y _ => (x.sameQuantum y).toNat
  -- Clause 9.4, with eight operands from three
  let eight (x y z : Datum) : Array Datum := #[x, y, z, x.negate, y.abs, z.negate, x, y]
  timed "sum (8 elements)" values fun x y z => outcomeCode (Arithmetic.sum f .nearest (eight x y z))
  timed "dot (8 pairs)" values fun x y z =>
    match Arithmetic.dot f .nearest (eight x y z) (eight y z x) with
    | .ok outcome => outcomeCode outcome
    | .error _ => 0
  timed "sumSquare (8 elements)" values fun x y z =>
    outcomeCode (Arithmetic.sumSquare f .nearest (eight x y z))
  timed "sumAbs (8 elements)" values fun x y z =>
    outcomeCode (Arithmetic.sumAbs f .nearest (eight x y z))
  -- Clause 9.2. The operands of `expm1` and `logp1` are scaled below one in magnitude.
  let small : Array Datum := values.map fun x =>
    match x with
    | .finite s c _ => .finite s c (-(f.precision : Int))
    | other => other
  timed "rSqrt" values fun x _ _ => outcomeCode (Arithmetic.rSqrt f .nearest x.abs)
  timed "hypot" values fun x y _ => outcomeCode (Arithmetic.hypot f .nearest x y)
  timed "pown" values fun x _ _ => outcomeCode (Arithmetic.pown f .nearest x 5)
  timed "rootn" values fun x _ _ => outcomeCode (Arithmetic.rootn f .nearest x 3)
  timed "expm1" small fun x _ _ =>
    datumCode ((DecimalInterchange.Transcendentals.Certified.expm1 f x).getD x)
  timed "logp1" small fun x _ _ =>
    datumCode ((DecimalInterchange.Transcendentals.Certified.logp1 f x).getD x)
  -- Clause 9.6
  timed "minimum" values fun x y _ => outcomeCode (Arithmetic.minimum f x y)
  timed "minimumNumber" values fun x y _ => outcomeCode (Arithmetic.minimumNumber f x y)
  timed "maximum" values fun x y _ => outcomeCode (Arithmetic.maximum f x y)
  timed "maximumNumber" values fun x y _ => outcomeCode (Arithmetic.maximumNumber f x y)
  timed "minimumMagnitude" values fun x y _ => outcomeCode (Arithmetic.minimumMagnitude f x y)
  timed "minimumMagnitudeNumber" values fun x y _ =>
    outcomeCode (Arithmetic.minimumMagnitudeNumber f x y)
  timed "maximumMagnitude" values fun x y _ => outcomeCode (Arithmetic.maximumMagnitude f x y)
  timed "maximumMagnitudeNumber" values fun x y _ =>
    outcomeCode (Arithmetic.maximumMagnitudeNumber f x y)
  -- Clause 9.7
  timed "getPayload" nans fun x _ _ => datumCode x.getPayload
  timed "setPayload" values fun x _ _ =>
    datumCode (Datum.setPayload f (.finite false (datumCode x % 1000) 0))
  timed "setPayloadSignaling" values fun x _ _ =>
    datumCode (Datum.setPayloadSignaling f (.finite false (datumCode x % 1000) 0))

open Model.Transcendentals in
/-- The functions of one argument of §9.2 by their names. -/
def functions : List (String × CorrectlyRounded.Function) :=
  [("exp2", .exp2), ("exp2m1", .exp2m1), ("exp10", .exp10), ("exp10m1", .exp10m1),
    ("log2", .log2), ("log10", .log10), ("log2p1", .log2p1), ("log10p1", .log10p1),
    ("sin", .sin), ("cos", .cos), ("tan", .tan), ("sinPi", .sinPi), ("cosPi", .cosPi),
    ("tanPi", .tanPi), ("asin", .asin), ("acos", .acos), ("atan", .atan), ("asinPi", .asinPi),
    ("acosPi", .acosPi), ("atanPi", .atanPi), ("sinh", .sinh), ("cosh", .cosh), ("tanh", .tanh),
    ("asinh", .asinh), ("acosh", .acosh), ("atanh", .atanh)]

open Model.Transcendentals in
/-- An operand of magnitude between 1/8 and 16 moved into the domain of a function. -/
def inDomain {fmt : FloatFormat} (function : CorrectlyRounded.Function) (x : Model fmt) :
    Model fmt :=
  match function with
  | .asin | .acos | .asinPi | .acosPi | .atanh => Model.scale x (-4) .nearest
  | .acosh => Model.scale (Model.abs x) 3 .nearest
  | .log2 | .log10 | .log2p1 | .log10p1 => Model.abs x
  | _ => x

/--
One row of a slow function: one pass over the operands, the faster of two passes, or a single
pass when there are fewer than four operands.
-/
def slowRow {fmt : FloatFormat} (format : String) (bits : Nat) (name : String)
    (values : Array (Model fmt)) (operation : Model fmt → Model fmt → Nat) : IO Unit := do
  let size := values.size
  let some first := values[0]? | return
  let mut best := 0
  let mut checksum := 0
  for trial in [0:if size < 4 then 1 else 2] do
    let start ← IO.monoNanosNow
    let mut total := 0
    for index in [0:size] do
      total := total + operation (values.getD index first) (values.getD ((index + 1) % size) first)
    let elapsed := (← IO.monoNanosNow) - start
    checksum := total
    if trial == 0 || elapsed / size < best then best := elapsed / size
  IO.println s!"binary,{format},{bits},{name},{best},{checksum % 1000000007}"
  (← IO.getStdout).flush

open Model.Transcendentals in
/--
The rows of the recommended functions of §9.2 in one binary format, over `count` operands:
every function, or the one called `only`.
-/
def functionRows (name : String) (fmt : FloatFormat) (count : Nat) (only : Option String) :
    IO Unit := do
  let values := operands fmt count 0x9E3779B97F4A7C15
  let bits := fmt.expWidth + fmt.fracWidth + 1
  let wanted (label : String) : Bool := only.all (· == label)
  for (label, function) in functions do
    if wanted label then
      slowRow name bits label values fun x _ =>
        (function.apply (inDomain function x)).value.toNatBits
  if wanted "atan2" then
    slowRow name bits "atan2" values fun x y => (CorrectlyRounded.atan2 x y).value.toNatBits
  if wanted "atan2Pi" then
    slowRow name bits "atan2Pi" values fun x y => (CorrectlyRounded.atan2Pi x y).value.toNatBits
  if wanted "powr" then
    slowRow name bits "powr" values fun x y =>
      (CorrectlyRounded.powr (Model.abs x) y).value.toNatBits
  if wanted "compound" then
    slowRow name bits "compound" values fun x _ =>
      (CorrectlyRounded.compound (Model.scale x (-4) .nearest) 5).value.toNatBits
  -- The functions of §9.2 that round an enclosure or an integer root.
  if wanted "exp" then
    slowRow name bits "exp" values fun x _ => (CorrectlyRounded.exp x).toNatBits
  if wanted "expm1" then
    slowRow name bits "expm1" values fun x _ => (CorrectlyRounded.expm1 x).toNatBits
  if wanted "log" then
    slowRow name bits "log" values fun x _ => (CorrectlyRounded.log (Model.abs x)).toNatBits
  if wanted "logp1" then
    slowRow name bits "logp1" values fun x _ => (CorrectlyRounded.logp1 (Model.abs x)).toNatBits
  if wanted "pow" then
    slowRow name bits "pow" values fun x y => (Model.pow (Model.abs x) y).toNatBits
  if wanted "rSqrt" then
    slowRow name bits "rSqrt" values fun x _ => (Model.rSqrt (Model.abs x)).toNatBits
  if wanted "hypot" then
    slowRow name bits "hypot" values fun x y => (Model.hypot x y).toNatBits
  if wanted "pown" then
    slowRow name bits "pown" values fun x _ => (Model.pown x 5).toNatBits
  if wanted "rootn" then
    slowRow name bits "rootn" values fun x _ => (Model.rootn x 3).toNatBits

open DecimalInterchange in
/--
The rows of the certified decimal functions of §9.2: the 26 functions of one argument, `exp`,
`log` and `compound` on operands of magnitude below one, and the inverse hyperbolic cosine and
`powr` on operands between one and ten. A row times the call whether or not it returns a
result.
-/
def decimalFunctionRows (name : String) (f : DecimalInterchange.Format) : IO Unit := do
  let values := decimalOperands f 64 0xD1B54A32D192ED03
  let datumCode (x : Datum) : Nat := outcomeCode { value := x }
  let small : Array Datum := values.map fun x =>
    match x with
    | .finite s c _ => .finite s c (-(f.precision : Int))
    | other => other
  let large : Array Datum := values.map fun x =>
    match x with
    | .finite _ c _ =>
        .finite false (c % (9 * 10 ^ (f.precision - 1)) + 10 ^ (f.precision - 1))
          (-(f.precision : Int) + 1)
    | other => other
  for (label, function) in functions do
    let operands := match function with
      | .acosh => large
      | .log2 | .log10 => small.map Datum.abs
      | _ => small
    row "decimal" name f.bitWidth label operands fun x _ _ =>
      datumCode ((Transcendentals.Certified.apply f function x).getD x)
  row "decimal" name f.bitWidth "exp" small fun x _ _ =>
    datumCode ((Transcendentals.Certified.exp f x).getD x)
  row "decimal" name f.bitWidth "log" (small.map Datum.abs) fun x _ _ =>
    datumCode ((Transcendentals.Certified.log f x).getD x)
  row "decimal" name f.bitWidth "powr" large fun x y _ =>
    datumCode ((Transcendentals.Certified.powr f x y).getD x)
  row "decimal" name f.bitWidth "compound" small fun x _ _ =>
    datumCode ((Transcendentals.Certified.compound f x.abs 5).getD x)

/-- The binary formats by their names in the rows. -/
def binaryFormats : List (String × FloatFormat) :=
  [("e4f3", FloatFormat.ieee 4 3), ("binary16", FloatFormat.binary16),
    ("binary32", FloatFormat.binary32), ("binary64", FloatFormat.binary64),
    ("binary128", FloatFormat.binary128), ("binary256", FloatFormat.binary256),
    ("binary1024", FloatFormat.ieee 27 996), ("binary4096", FloatFormat.ieee 35 4060)]

end FloatLibBenchmarks.Public.IEEE2019

open FloatLibBenchmarks.Public.IEEE2019 in
/--
Print the CSV header and the rows of every format, or with the arguments
`functions FORMAT [COUNT [NAME]]` the rows of the recommended functions of §9.2 in one binary
format, over `COUNT` operands (eight by default), for every function or for the one called
`NAME`.
-/
public def main (arguments : List String) : IO Unit := do
  if let "functions" :: format :: rest := arguments then
    match binaryFormats.lookup format with
    | some fmt => functionRows format fmt ((rest.head?.bind String.toNat?).getD 8) rest[1]?
    | none => throw (IO.userError s!"unknown binary format {format}")
    return
  IO.println "radix,format,bits,operation,nanoseconds,checksum"
  binaryRows "e4f3" (FloatFormat.ieee 4 3)
  binaryRows "binary16" FloatFormat.binary16
  binaryRows "binary32" FloatFormat.binary32
  binaryRows "binary64" FloatFormat.binary64
  binaryRows "binary128" FloatFormat.binary128
  binaryRows "binary256" FloatFormat.binary256
  binaryRows "binary1024" (FloatFormat.ieee 27 996)
  binaryRows "binary4096" (FloatFormat.ieee 35 4060)
  decimalRows "decimal32" .decimal32
  decimalRows "decimal64" .decimal64
  decimalRows "decimal128" .decimal128
  decimalFunctionRows "decimal32" .decimal32
  decimalFunctionRows "decimal64" .decimal64
  decimalFunctionRows "decimal128" .decimal128
