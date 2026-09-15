/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime

/-!
# Exact reduction vectors for an external MPFR oracle

`oracle reductions` evaluates logical `Model.sumWithStatus` and `Model.dotWithStatus`, then emits
the finite cases as exact signed dyadics. The external checker selects MPFR precision and exponent
bounds from each destination descriptor, evaluates the same mathematical reduction, and compares
the rounded value and IEEE status indicators.

Inputs use a wider source descriptor so the matrix includes cross-format underflow without
smuggling an already-rounded destination value into the test. Every emitted source value is
decoded again and checked against the intended exact dyadic before its case is printed.
-/

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Oracle.Reductions

private inductive Operation where
  | sum
  | dot

private structure ExactCase where
  name : String
  operation : Operation
  left : Array FloatLib.Numerics.Dyadic
  right : Array FloatLib.Numerics.Dyadic := #[]

private def Operation.label : Operation → String
  | .sum => "sum"
  | .dot => "dot"

private def dyadicDescription (value : FloatLib.Numerics.Dyadic) : String :=
  s!"(negative={value.negative}, significand={value.significand}, exponent={value.exponent})"

private def dyadic
    (negative : Bool) (significand : Nat) (exponent : Int) :
    FloatLib.Numerics.Dyadic :=
  { negative, significand, exponent }

private def sourceFormat (destination : FloatFormat) : FloatFormat :=
  FloatFormat.ieee (destination.expWidth + 1) (destination.fracWidth + 3)
    (by
      have := destination.expWidth_ge_two
      omega)
    (by
      have := destination.fracWidth_pos
      omega)

private def maxFiniteDyadic (format : FloatFormat) : FloatLib.Numerics.Dyadic :=
  dyadic false
    (2 ^ (format.fracWidth + 1) - 1)
    (Int.ofNat (FloatFormat.Encoding.maxFiniteExponent .ieee format.expWidth) -
      Int.ofNat format.exponentBias - Int.ofNat format.fracWidth)

private def deterministicTerms
    (format : FloatFormat) (salt : Nat) :
    Array FloatLib.Numerics.Dyadic :=
  (List.range 16).toArray.map fun index =>
    let fraction := (index * salt + salt + 1) % (2 ^ format.fracWidth)
    dyadic (decide ((index + salt) % 3 = 0))
      (2 ^ format.fracWidth + fraction)
      (-Int.ofNat format.fracWidth + Int.ofNat (index % 5) - 2)

private def cases (format : FloatFormat) : Array ExactCase :=
  let one := dyadic false 1 0
  let negativeOne := dyadic true 1 0
  let two := dyadic false 1 1
  let half := dyadic false 1 (-1)
  let halfUlp := dyadic false 1 (-Int.ofNat format.fracWidth - 1)
  let negativeHalfUlp := { halfUlp with negative := true }
  let large := dyadic false 1 (Int.ofNat format.fracWidth + 2)
  let negativeLarge := { large with negative := true }
  let minimum := dyadic false 1 format.minSubnormalExponent
  let negativeMinimum := { minimum with negative := true }
  let belowMinimum := dyadic false 1 (format.minSubnormalExponent - 1)
  let negativeBelowMinimum := { belowMinimum with negative := true }
  let largestSubnormal :=
    dyadic false (2 ^ format.fracWidth - 1) format.minSubnormalExponent
  let negativeLargestSubnormal := { largestSubnormal with negative := true }
  let minimumNormal := dyadic false 1 format.minNormalExponent
  let maximum := maxFiniteDyadic format
  let halfUlpAboveMaximum := { maximum with
    significand := 1
    exponent := maximum.exponent - 1 }
  let quarterUlpAboveMaximum := { halfUlpAboveMaximum with
    exponent := halfUlpAboveMaximum.exponent - 1 }
  let positiveZero := dyadic false 0 0
  let negativeZero := dyadic true 0 0
  let generatedLeft := deterministicTerms format 37
  let generatedRight := deterministicTerms format 61
  #[
    { name := "sum-empty", operation := .sum, left := #[] },
    {
      name := "sum-exact"
      operation := .sum
      left := #[one, two, { half with negative := true }]
    },
    {
      name := "sum-cancellation"
      operation := .sum
      left := #[large, one, negativeLarge]
    },
    {
      name := "sum-positive-tie"
      operation := .sum
      left := #[one, halfUlp]
    },
    {
      name := "sum-negative-tie"
      operation := .sum
      left := #[negativeOne, negativeHalfUlp]
    },
    {
      name := "sum-overflow"
      operation := .sum
      left := #[maximum, maximum]
    },
    {
      name := "sum-overflow-midpoint"
      operation := .sum
      left := #[maximum, halfUlpAboveMaximum]
    },
    {
      name := "sum-overflow-below-midpoint"
      operation := .sum
      left := #[maximum, quarterUlpAboveMaximum]
    },
    {
      name := "sum-minimum-subnormal-exact"
      operation := .sum
      left := #[minimum]
    },
    {
      name := "sum-positive-underflow-midpoint"
      operation := .sum
      left := #[belowMinimum]
    },
    {
      name := "sum-negative-underflow-midpoint"
      operation := .sum
      left := #[negativeBelowMinimum]
    },
    {
      name := "sum-minimum-normal-exact"
      operation := .sum
      left := #[minimumNormal]
    },
    {
      name := "sum-subnormal-normal-boundary"
      operation := .sum
      left := #[largestSubnormal, minimum]
    },
    {
      name := "sum-cancellation-to-subnormal"
      operation := .sum
      left := #[minimumNormal, negativeLargestSubnormal]
    },
    {
      name := "sum-positive-zero"
      operation := .sum
      left := #[positiveZero, positiveZero]
    },
    {
      name := "sum-negative-zero"
      operation := .sum
      left := #[negativeZero, negativeZero]
    },
    {
      name := "sum-mixed-signed-zero"
      operation := .sum
      left := #[negativeZero, positiveZero]
    },
    {
      name := "sum-exact-zero"
      operation := .sum
      left := #[one, negativeOne]
    },
    {
      name := "sum-generated"
      operation := .sum
      left := generatedLeft
    },
    { name := "dot-empty", operation := .dot, left := #[], right := #[] },
    {
      name := "dot-exact"
      operation := .dot
      left := #[one, two, dyadic false 3 0]
      right := #[dyadic false 1 2, negativeOne, half]
    },
    {
      name := "dot-cancellation"
      operation := .dot
      left := #[large, one, large]
      right := #[one, one, negativeOne]
    },
    {
      name := "dot-positive-tie"
      operation := .dot
      left := #[one, halfUlp]
      right := #[one, one]
    },
    {
      name := "dot-negative-tie"
      operation := .dot
      left := #[negativeOne, negativeHalfUlp]
      right := #[one, one]
    },
    {
      name := "dot-overflow"
      operation := .dot
      left := #[maximum]
      right := #[two]
    },
    {
      name := "dot-underflow"
      operation := .dot
      left := #[minimum]
      right := #[half]
    },
    {
      name := "dot-negative-underflow"
      operation := .dot
      left := #[negativeMinimum]
      right := #[half]
    },
    {
      name := "dot-positive-zero"
      operation := .dot
      left := #[positiveZero, negativeZero]
      right := #[one, negativeOne]
    },
    {
      name := "dot-negative-zero"
      operation := .dot
      left := #[negativeZero]
      right := #[one]
    },
    {
      name := "dot-generated"
      operation := .dot
      left := generatedLeft
      right := generatedRight
    }
  ]

private def decodeFinite {format : FloatFormat}
    (value : Model format) : IO FloatLib.Numerics.Dyadic :=
  match Model.toDyadic? value with
  | some exact => pure exact
  | none =>
      throw <| IO.userError
        s!"internal reduction-vector input is exceptional: bits={value.toNatBits}"

private def encodeExact (destination : FloatFormat)
    (values : Array FloatLib.Numerics.Dyadic) :
    IO (Array (Model (sourceFormat destination)) ×
      Array FloatLib.Numerics.Dyadic) := do
  let encoded := values.map fun exact =>
    Model.roundDyadicWithRounding (sourceFormat destination) .nearestEven exact
  let decoded ← encoded.mapM decodeFinite
  for (intended, actual) in values.zip decoded do
    let sameZeroSign :=
      intended.significand != 0 ||
        (actual.significand == 0 && actual.negative == intended.negative)
    if !FloatLib.Numerics.Dyadic.isEqual intended actual || !sameZeroSign then
      throw <| IO.userError <|
        s!"source descriptor rounded a reduction vector: " ++
          s!"intended={dyadicDescription intended}, actual={dyadicDescription actual}"
  pure (encoded, decoded)

private def resultFields {format : FloatFormat}
    (value : Model format) : IO (Array String) := do
  if Model.isInf value then
    pure #["infinity", toString (Model.signBit value).toNat, "0", "0",
      toString value.toNatBits]
  else
    let exact ← decodeFinite value
    pure #["finite", toString exact.negative.toNat, toString exact.significand,
      toString exact.exponent, toString value.toNatBits]

private def inputFields (values : Array FloatLib.Numerics.Dyadic) : Array String :=
  values.flatMap fun value =>
    #[toString value.negative.toNat, toString value.significand, toString value.exponent]

private def emitCase (destination : FloatFormat)
    (test : ExactCase) (mode : Model.IEEERoundingMode) (modeLabel : String) :
    IO Unit := do
  let (left, leftExact) ← encodeExact destination test.left
  let (right, rightExact) ← encodeExact destination test.right
  let outcome ←
    match test.operation with
    | .sum =>
        pure <| Model.sumWithStatus destination left mode
    | .dot =>
        match Model.dotWithStatus destination left right mode with
        | .ok result => pure result
        | .error error =>
            throw <| IO.userError
              s!"internal reduction-vector length mismatch: {reprStr error}"
  let valueFields ← resultFields outcome.value
  let statusFields := #[
    toString outcome.status.invalid.toNat,
    toString outcome.status.divideByZero.toNat,
    toString outcome.status.overflow.toNat,
    toString outcome.status.underflow.toNat,
    toString outcome.status.inexact.toNat
  ]
  let fields :=
    #[
      test.name,
      test.operation.label,
      modeLabel,
      toString destination.expWidth,
      toString destination.fracWidth,
      toString destination.exponentBias,
      toString left.size
    ] ++ valueFields ++ statusFields ++ inputFields leftExact ++ inputFields rightExact
  IO.println <| String.intercalate "\t" fields.toList

private def emitFormat (format : FloatFormat) : IO Unit := do
  for test in cases format do
    for mode in Model.IEEERoundingMode.all do
      emitCase format test mode (toString mode)

/-- Emit finite sum and dot-product vectors. -/
public def run : IO Unit := do
  IO.println <|
    "# name\top\tmode\texpWidth\tfracWidth\tbias\tcount\tclass\tsign" ++
      "\tsignificand\texponent\tbits\tinvalid\tdivideByZero\toverflow" ++
      "\tunderflow\tinexact\tinputs..."
  emitFormat FloatFormat.binary16
  emitFormat FloatFormat.bfloat16
  emitFormat FloatFormat.binary32
  emitFormat FloatFormat.binary64
  emitFormat FloatFormat.binary128
  emitFormat FloatFormat.binary256

end FloatLibTests.Oracle.Reductions
