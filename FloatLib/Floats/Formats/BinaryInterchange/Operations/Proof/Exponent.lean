/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

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

/-- A finite nonzero input delivers its exact leading exponent without any exception. -/
theorem binaryExponentInt_of_finite_nonzero {fmt : FloatFormat} (value : Model fmt)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand ≠ 0) :
    binaryExponentInt value = { value := (exact.significand.log2 : Int) + exact.exponent } := by
  simp [binaryExponentInt, hvalue, hsignificand]

/-- The integer answer brackets the exact finite magnitude between consecutive powers of two. -/
theorem binaryExponentInt_bounds {fmt : FloatFormat} (value : Model fmt)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand ≠ 0) :
    (2 : Rat) ^ (binaryExponentInt value).value ≤
        (exact.significand : Rat) * (2 : Rat) ^ exact.exponent ∧
      (exact.significand : Rat) * (2 : Rat) ^ exact.exponent <
        (2 : Rat) ^ ((binaryExponentInt value).value + 1) := by
  rw [binaryExponentInt_of_finite_nonzero value exact hvalue hsignificand]
  have hl : (2 : Rat) ^ exact.significand.log2 ≤ (exact.significand : Rat) := by
    rw [Nat.log2_eq_log_two]
    exact_mod_cast Nat.pow_log_le_self 2 hsignificand
  have hu : (exact.significand : Rat) < (2 : Rat) ^ (exact.significand.log2 + 1) := by
    rw [Nat.log2_eq_log_two]
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) exact.significand
  have hp : 0 < (2 : Rat) ^ exact.exponent := zpow_pos (by norm_num) _
  constructor
  · simpa [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)] using
      mul_le_mul_of_nonneg_right hl hp.le
  · simpa [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), pow_succ, mul_assoc,
      mul_comm, mul_left_comm] using mul_lt_mul_of_pos_right hu hp

/-- The exceptional integer is strictly beyond the IEEE integer-result bound in either sign. -/
theorem binaryExponentSentinel_outside_logBBound (fmt : FloatFormat) :
    2 * |logBBound fmt| < binaryExponentSentinel fmt ∧
      -binaryExponentSentinel fmt < -(2 * |logBBound fmt|) := by
  have hm := le_max_right (max |fmt.minSubnormalExponent| |fmt.maxNormalExponent|)
    |logBBound fmt|
  unfold binaryExponentSentinel
  omega

/-- An integer-result exponent query signals invalid on zero, rather than divide-by-zero. -/
theorem binaryExponentInt_of_zero {fmt : FloatFormat} (value : Model fmt)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand = 0) :
    binaryExponentInt value =
      { value := -binaryExponentSentinel fmt, status := { invalid := true } } := by
  simp [binaryExponentInt, hvalue, hsignificand]

/-- Either infinity uses the positive exceptional integer and signals invalid. -/
theorem binaryExponentInt_of_infinity {fmt : FloatFormat} (value : Model fmt)
    (negative : Bool) (hvalue : exactValue value = .infinity negative) :
    binaryExponentInt value =
      { value := binaryExponentSentinel fmt, status := { invalid := true } } := by
  simp [binaryExponentInt, hvalue]

/-- Both quiet and signaling NaNs signal invalid for an integer-result exponent query. -/
theorem binaryExponentInt_of_nan {fmt : FloatFormat} (value : Model fmt)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    binaryExponentInt value =
      { value := binaryExponentSentinel fmt, status := { invalid := true } } := by
  simp [binaryExponentInt, hvalue]

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
