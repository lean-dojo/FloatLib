/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Exponent-operation contracts

`scaleB` changes an exact binary exponent before one rounding step; `logB` reports the leading
binary exponent. The finite contracts reduce each operation to the shared dyadic rounder and
status calculation. Separate equations give the value and flags for zero, infinity, and NaNs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-- `scaleB` is exactly the value component of its status-bearing operation. -/
@[simp] theorem scaleB_eq_value {fmt : FloatFormat}
    (value : Model fmt) (scale : Int) (mode : IEEERoundingMode) :
    scaleB value scale mode = (scaleBWithStatus value scale mode).value :=
  rfl

/--
On finite input, `scaleB` changes only the exact power-of-two exponent before the one selected
rounding operation.
-/
theorem scaleBWithStatus_of_finite
    {fmt : FloatFormat} (value : Model fmt) (scale : Int)
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact) :
    scaleBWithStatus value scale mode =
      let scaled : Numerics.Dyadic := { exact with exponent := exact.exponent + scale }
      let rounded := roundDyadicWithRounding fmt mode scaled
      { value := rounded
        status := dyadicRoundingStatus fmt mode scaled rounded } := by
  simp [scaleBWithStatus, hvalue]

/-- Scaling by zero uses the ordinary one-round exact-dyadic path. -/
theorem scaleBWithStatus_zero_of_finite
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    scaleBWithStatus value 0 mode =
      let rounded := roundDyadicWithRounding fmt mode exact
      { value := rounded
        status := dyadicRoundingStatus fmt mode exact rounded } := by
  simp [scaleBWithStatus, hvalue]

/-- `scaleB` preserves either infinity and raises no exception. -/
theorem scaleBWithStatus_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (scale : Int)
    (mode : IEEERoundingMode) (negative : Bool)
    (hvalue : exactValue value = .infinity negative) :
    scaleBWithStatus value scale mode =
      { value
        status := .clear } := by
  simp [scaleBWithStatus, hvalue, outcomeWithInvalid]

/-- `scaleB` quiets a NaN and raises `invalid` exactly for a signaling NaN. -/
theorem scaleBWithStatus_of_nan
    {fmt : FloatFormat} (value : Model fmt) (scale : Int)
    (mode : IEEERoundingMode) (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    scaleBWithStatus value scale mode =
      { value := quietNaN value
        status := { invalid := signaling } } := by
  cases signaling <;>
    simp [scaleBWithStatus, hvalue, outcomeWithInvalid, IEEEStatus.clear]

/-- `logB` is exactly the value component of its status-bearing operation. -/
@[simp] theorem logB_eq_value {fmt : FloatFormat} (value : Model fmt) :
    logB value = (logBWithStatus value).value :=
  rfl

/--
For a nonzero finite dyadic `±m * 2^e` with `m > 0`, `logB` returns the rounded encoding of the integer
`floor(log₂ m) + e`.
-/
theorem logBWithStatus_of_finite_nonzero
    {fmt : FloatFormat} (value : Model fmt) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand ≠ 0) :
    logBWithStatus value =
      let exponent := Int.ofNat exact.significand.log2 + exact.exponent
      let exactResult := Numerics.Dyadic.ofScaledInt exponent 0
      let rounded := roundDyadic fmt exactResult
      { value := rounded
        status := dyadicRoundingStatus fmt .nearestEven exactResult rounded } := by
  simp [logBWithStatus, hvalue, hsignificand]

/--
`logB` of finite zero raises `divideByZero` and returns `nativeOverflow fmt true`.

For IEEE encodings that value is negative infinity, as IEEE 754-2019 §5.3.3 requires. For the
`finiteMaxNaN` and `finiteUnsignedZero` encodings, which have no infinity, it is the encoding's
NaN word, with the same `divideByZero` flag for the zero input. The `finite` encoding saturates to
its most negative finite value.
-/
theorem logBWithStatus_of_zero
    {fmt : FloatFormat} (value : Model fmt) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand = 0) :
    logBWithStatus value =
      { value := nativeOverflow fmt true
        status := { divideByZero := true } } := by
  simp [logBWithStatus, hvalue, hsignificand]

/--
`logB` of either infinity returns `nativeOverflow fmt false` and raises no exception.
For IEEE encodings this is positive infinity.
-/
theorem logBWithStatus_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (negative : Bool)
    (hvalue : exactValue value = .infinity negative) :
    logBWithStatus value =
      { value := nativeOverflow fmt false
        status := .clear } := by
  simp [logBWithStatus, hvalue]

/-- `logB` quiets a NaN and raises `invalid` exactly for a signaling NaN. -/
theorem logBWithStatus_of_nan
    {fmt : FloatFormat} (value : Model fmt)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    logBWithStatus value =
      { value := quietNaN value
        status := { invalid := signaling } } := by
  simp [logBWithStatus, hvalue]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
