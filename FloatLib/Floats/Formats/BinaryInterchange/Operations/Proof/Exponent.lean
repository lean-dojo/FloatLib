/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Exponent-operation contracts

`scale` changes the exact binary exponent before rounding; `binaryExponent`
reports the leading binary exponent. The finite contracts reduce each operation to the shared
dyadic rounder and status calculation. Separate equations cover zero, infinity, and NaNs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-- `scale` is exactly the value component of its status-bearing operation. -/
@[simp] theorem scale_eq_value {fmt : FloatFormat}
    (value : Model fmt) (n : Int) (mode : IEEERoundingMode) :
    scale value n mode = (scaleWithStatus value n mode).value :=
  rfl

/--
On finite input, `scale` changes only the exact binary exponent before rounding.
-/
theorem scaleWithStatus_of_finite
    {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact) :
    scaleWithStatus value n mode =
      let scaled : Numerics.Dyadic := { exact with exponent := exact.exponent + n }
      let rounded := roundDyadicWithRounding fmt mode scaled
      { value := rounded
        status := dyadicRoundingStatus fmt mode scaled rounded } := by
  simp [scaleWithStatus, hvalue]

/-- Scaling by zero uses the ordinary one-round exact-dyadic path. -/
theorem scaleWithStatus_zero_of_finite
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    scaleWithStatus value 0 mode =
      let rounded := roundDyadicWithRounding fmt mode exact
      { value := rounded
        status := dyadicRoundingStatus fmt mode exact rounded } := by
  simp [scaleWithStatus, hvalue]

/-- `scale` preserves either infinity and raises no exception. -/
theorem scaleWithStatus_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) (negative : Bool)
    (hvalue : exactValue value = .infinity negative) :
    scaleWithStatus value n mode =
      { value
        status := .clear } := by
  simp [scaleWithStatus, hvalue, outcomeWithInvalid]

/-- `scale` quiets a NaN and raises `invalid` exactly for a signaling NaN. -/
theorem scaleWithStatus_of_nan
    {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    scaleWithStatus value n mode =
      { value := quietNaN value
        status := { invalid := signaling } } := by
  cases signaling <;>
    simp [scaleWithStatus, hvalue, outcomeWithInvalid, IEEEStatus.clear]

/-- `binaryExponent` is exactly the value component of its status-bearing operation. -/
@[simp] theorem binaryExponent_eq_value {fmt : FloatFormat} (value : Model fmt) :
    binaryExponent value = (binaryExponentWithStatus value).value :=
  rfl

/--
For a nonzero finite dyadic `±m * 2^e` with `m > 0`, `binaryExponent` returns the rounded
encoding of the integer `floor(log₂ m) + e`.
-/
theorem binaryExponentWithStatus_of_finite_nonzero
    {fmt : FloatFormat} (value : Model fmt) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand ≠ 0) :
    binaryExponentWithStatus value =
      let exponent := Int.ofNat exact.significand.log2 + exact.exponent
      let exactResult := Numerics.Dyadic.ofScaledInt exponent 0
      let rounded := roundDyadic fmt exactResult
      { value := rounded
        status := dyadicRoundingStatus fmt .nearestEven exactResult rounded } := by
  simp [binaryExponentWithStatus, hvalue, hsignificand]

/--
`binaryExponent` of finite zero raises `divideByZero` and returns `nativeOverflow fmt true`.

For IEEE encodings that value is negative infinity, as IEEE 754-2019 §5.3.3 requires. For the
`finiteMaxNaN` and `finiteUnsignedZero` encodings, which have no infinity, it is the encoding's
NaN word, with the same `divideByZero` flag for the zero input. The `finite` encoding saturates to
its most negative finite value.
-/
theorem binaryExponentWithStatus_of_zero
    {fmt : FloatFormat} (value : Model fmt) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand = 0) :
    binaryExponentWithStatus value =
      { value := nativeOverflow fmt true
        status := { divideByZero := true } } := by
  simp [binaryExponentWithStatus, hvalue, hsignificand]

/--
`binaryExponent` of either infinity returns `nativeOverflow fmt false` and raises no exception.
For IEEE encodings this is positive infinity.
-/
theorem binaryExponentWithStatus_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (negative : Bool)
    (hvalue : exactValue value = .infinity negative) :
    binaryExponentWithStatus value =
      { value := nativeOverflow fmt false
        status := .clear } := by
  simp [binaryExponentWithStatus, hvalue]

/-- `binaryExponent` quiets a NaN and raises `invalid` exactly for a signaling NaN. -/
theorem binaryExponentWithStatus_of_nan
    {fmt : FloatFormat} (value : Model fmt)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    binaryExponentWithStatus value =
      { value := quietNaN value
        status := { invalid := signaling } } := by
  simp [binaryExponentWithStatus, hvalue]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
