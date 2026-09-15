/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
import FloatLibTests.Fixtures.NativeIEEE

/-!
# Primitive IEEE vectors for an external MPFR oracle

`oracle primitives` emits results from logical `Model.*WithStatus` operations for binary32 and
binary64. A compact named suite covers NaNs, infinities, invalid operations, division by
zero, and exact subnormal results, which must not report underflow. Additional operands are generated at runtime by a fixed-seed generator; generated corpora
are deliberately not checked in. Every diagnostic identifier contains the seed and sample index
needed to reproduce a failure.

The external checker treats MPFR as the finite arithmetic oracle. IEEE signaling-NaN detection,
NaN payload policy, and invalid-operation precedence cannot be delegated to MPFR, whose number
type has only a single NaN class. The checker therefore compares NaN result class and decodes the
IEEE invalid causes directly from the operand encodings.
-/

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLibTests.Fixtures.NativeIEEE

namespace FloatLibTests.Oracle.Primitives

private inductive Operation where
  | add
  | sub
  | mul
  | div
  | sqrt
  | fma
  deriving BEq

private def Operation.label : Operation → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .sqrt => "sqrt"
  | .fma => "fma"

private structure RawCase where
  name : String
  operation : Operation
  operands : Array Nat

private def exceptionalCases {Word : Type}
    (cases : EdgeCases Word) (toNat : Word → Nat) : Array RawCase :=
  let bits (values : List Word) := values.toArray.map toNat
  #[
    { name := "add-quiet-nan", operation := .add,
      operands := bits [cases.quietNaN, cases.one] },
    { name := "add-signaling-nan", operation := .add,
      operands := bits [cases.signalingNaN, cases.one] },
    { name := "add-opposite-infinities", operation := .add,
      operands := bits [cases.positiveInfinity, cases.negativeInfinity] },
    { name := "add-half-ulp-tie", operation := .add,
      operands := bits [cases.one, cases.halfUlpAtOne] },
    { name := "add-overflow", operation := .add,
      operands := bits [cases.largestFinite, cases.largestFinite] },
    { name := "sub-equal-infinities", operation := .sub,
      operands := bits [cases.positiveInfinity, cases.positiveInfinity] },
    { name := "mul-infinity-zero", operation := .mul,
      operands := bits [cases.positiveInfinity, cases.positiveZero] },
    { name := "mul-infinity-finite", operation := .mul,
      operands := bits [cases.negativeInfinity, cases.two] },
    { name := "div-zero-zero", operation := .div,
      operands := bits [cases.positiveZero, cases.positiveZero] },
    { name := "div-infinity-infinity", operation := .div,
      operands := bits [cases.positiveInfinity, cases.positiveInfinity] },
    { name := "div-finite-zero", operation := .div,
      operands := bits [cases.one, cases.positiveZero] },
    { name := "div-negative-finite-zero", operation := .div,
      operands := bits [cases.negativeOne, cases.positiveZero] },
    { name := "div-tiny-inexact", operation := .div,
      operands := bits [cases.smallestSubnormal, cases.two] },
    { name := "sqrt-negative", operation := .sqrt,
      operands := bits [cases.negativeOne] },
    { name := "sqrt-negative-zero", operation := .sqrt,
      operands := bits [cases.negativeZero] },
    { name := "sqrt-infinity", operation := .sqrt,
      operands := bits [cases.positiveInfinity] },
    { name := "sqrt-quiet-nan", operation := .sqrt,
      operands := bits [cases.quietNaN] },
    { name := "sqrt-signaling-nan", operation := .sqrt,
      operands := bits [cases.signalingNaN] },
    { name := "fma-infinity-zero", operation := .fma,
      operands := bits [cases.positiveInfinity, cases.positiveZero, cases.one] },
    { name := "fma-opposite-infinity", operation := .fma,
      operands := bits [cases.positiveInfinity, cases.one, cases.negativeInfinity] },
    { name := "fma-quiet-nan", operation := .fma,
      operands := bits [cases.quietNaN, cases.one, cases.two] },
    { name := "fma-quiet-nan-with-invalid-product", operation := .fma,
      operands := bits [cases.positiveInfinity, cases.positiveZero, cases.quietNaN] },
    { name := "fma-signaling-nan-with-invalid-product", operation := .fma,
      operands := bits [cases.positiveInfinity, cases.positiveZero, cases.signalingNaN] }
  ]

/--
Operands whose exact result is a nonzero subnormal number.

IEEE 754 underflow requires an inexact result, so these cases must report no underflow in every
rounding direction. They exist because MPFR's `mpfr_subnormalize` raises its own underflow flag
for an exact subnormal, which the external checker must not mistake for IEEE underflow.

Bit patterns below the smallest normal encode `k` times the smallest subnormal as the integer
`k`; a normal power of two encodes as its biased exponent shifted into the exponent field. For
binary32 the multiplication is `2^-100 * 2^-40 = 2^-140` and the division is `2^-140 / 2`.
-/
private def exactSubnormalCases (format : FloatFormat) : Array RawCase :=
  let powerOfTwo (exponent : Int) : Nat :=
    (exponent + format.exponentBias).toNat <<< format.fracWidth
  let smallestNormalExponent : Int := 1 - format.exponentBias
  #[
    { name := "add-exact-subnormal", operation := .add, operands := #[3, 5] },
    { name := "mul-exact-subnormal", operation := .mul,
      operands := #[powerOfTwo (smallestNormalExponent + 26), powerOfTwo (-40)] },
    { name := "div-exact-subnormal", operation := .div,
      operands := #[512, powerOfTwo 1] }
  ]

private def nextState (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

private def operationAt (index : Nat) : Operation :=
  match index % 6 with
  | 0 => .add
  | 1 => .sub
  | 2 => .mul
  | 3 => .div
  | 4 => .sqrt
  | _ => .fma

private def randomCases (seed : UInt64) (width count : Nat) : Array RawCase := Id.run do
  let modulus := 2 ^ width
  let mut state := seed
  let mut result := #[]
  for index in [0:count] do
    let operation := operationAt index
    let arity := if operation == .sqrt then 1 else if operation == .fma then 3 else 2
    let mut operands := #[]
    for _ in [0:arity] do
      state := nextState state
      operands := operands.push (state.toNat % modulus)
    result := result.push {
      name := s!"seed-{seed.toNat}-sample-{index}"
      operation
      operands
    }
  return result

private def applyOperation {format : FloatFormat}
    (operation : Operation) (operands : Array (Model format))
    (mode : Model.IEEERoundingMode) : IO (Model.IEEEOutcome format) :=
  match operation, operands.toList with
  | .add, [left, right] => pure <| Model.addWithStatus left right mode
  | .sub, [left, right] => pure <| Model.subWithStatus left right mode
  | .mul, [left, right] => pure <| Model.mulWithStatus left right mode
  | .div, [left, right] => pure <| Model.divWithStatus left right mode
  | .sqrt, [value] => pure <| Model.sqrtWithStatus value mode
  | .fma, [left, right, addend] => pure <| Model.fmaWithStatus left right addend mode
  | _, _ => throw <| IO.userError s!"invalid arity for {operation.label}"

private def emitCase (format : FloatFormat) (test : RawCase)
    (mode : Model.IEEERoundingMode) (modeLabel : String) : IO Unit := do
  let operands := test.operands.map (Model.ofNatBits (fmt := format))
  let outcome ← applyOperation test.operation operands mode
  let status := outcome.status
  let fields := #[
    test.name,
    test.operation.label,
    modeLabel,
    toString format.expWidth,
    toString format.fracWidth,
    toString format.exponentBias,
    toString outcome.value.toNatBits,
    toString status.invalid.toNat,
    toString status.divideByZero.toNat,
    toString status.overflow.toNat,
    toString status.underflow.toNat,
    toString status.inexact.toNat,
    toString test.operands.size
  ] ++ test.operands.map toString
  IO.println <| String.intercalate "\t" fields.toList

private def emitFormat (format : FloatFormat) (tests : Array RawCase) : IO Unit := do
  for test in tests do
    for mode in Model.IEEERoundingMode.all do
      emitCase format test mode (toString mode)

/-- Emit primitive binary32 and binary64 vectors. -/
public def run : IO Unit := do
  IO.println <|
    "# name\top\tmode\texpWidth\tfracWidth\tbias\tbits\tinvalid\tdivideByZero" ++
      "\toverflow\tunderflow\tinexact\tcount\toperands..."
  emitFormat FloatFormat.binary32 <|
    exceptionalCases binary32Cases UInt32.toNat ++
      exactSubnormalCases FloatFormat.binary32 ++
      randomCases 0x243f6a8885a308d3 32 24
  emitFormat FloatFormat.binary64 <|
    exceptionalCases binary64Cases UInt64.toNat ++
      exactSubnormalCases FloatFormat.binary64 ++
      randomCases 0x13198a2e03707344 64 24

end FloatLibTests.Oracle.Primitives
