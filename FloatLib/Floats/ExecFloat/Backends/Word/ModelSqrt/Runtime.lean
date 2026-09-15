/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import Init.Data.Float.Model.Unpacked.Operations.Sqrt

/-!
# Executable native-backed unpacked floating-point square root

The unpacked-float square-root implementation uses the proved native-word integer-root
dispatcher when the radicand fits in `UInt64`. Wider radicands retain Lean's arbitrary-precision
implementation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeModelSqrt

/-- Native-backed implementation of Lean's unpacked square-root core. -/
@[inline] def sqrtCore (spec : Float.Model.Format) (mantissa : Nat) (exponent : Int) :
    Nat × Int × Float.Model.UnpackedFloat.Accuracy :=
  let targetExponent :=
    min (exponent.ediv 2)
      (spec.targetExponent ((Float.Model.totalExponent mantissa exponent + 1).ediv 2))
  let shiftAmount := (exponent - 2 * targetExponent).toNat
  let scaledMantissa := mantissa <<< shiftAmount
  let root := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat scaledMantissa
  let remainder := scaledMantissa - root * root
  let accuracy : Float.Model.UnpackedFloat.Accuracy :=
    if remainder = 0 then
      .exact
    else
      .inexact (if remainder ≤ root then .lt else .gt)
  (root, targetExponent, accuracy)

/-- Native-backed implementation of Lean's logical unpacked floating-point square root. -/
@[inline] def sqrt (spec : Float.Model.Format) :
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat
  | .notANumber => .notANumber
  | .infinity .positive => .infinity .positive
  | .infinity .negative => .notANumber
  | .finite .negative .. => .notANumber
  | .zero sign => .zero sign
  | .finite .positive mantissa exponent _ =>
      let (mantissa, exponent, accuracy) := sqrtCore spec mantissa exponent
      Float.Model.UnpackedFloat.roundWithAccuracy
        spec .positive mantissa exponent accuracy

end Model.NativeModelSqrt
end FloatLib.Floats.Formats.BinaryInterchange
