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

`scale` changes the exact binary exponent before rounding, and `binaryExponent` reports the
leading binary exponent. The finite contracts reduce each operation to the shared dyadic rounder
and status calculation. Zero, infinity, and NaNs have their own equations.
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

/-- Scaling with `status := true` delivers the value of scaling. -/
@[simp] theorem value_scale {fmt : FloatFormat}
    (value : Model fmt) (n : Int) (mode : IEEERoundingMode) :
    (scale value n mode (status := true)).value = scale value n mode :=
  rfl

/--
On finite input, `scale` changes only the exact binary exponent before rounding.
-/
theorem scale_status_of_finite
    {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact) :
    scale value n mode (status := true) =
      let scaled : Numerics.Dyadic := { exact with exponent := exact.exponent + n }
      let rounded := Internal.Directed.roundDyadic fmt mode scaled
      { value := rounded
        status := dyadicRoundingStatus fmt mode scaled rounded
        ternary := dyadicTernary scaled rounded } := by
  simp [scale, Internal.Status.scale, dyadicRoundingOutcome, hvalue]

/-- Scaling by zero uses the ordinary one-round exact-dyadic path. -/
theorem scale_zero_status_of_finite
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    scale value 0 mode (status := true) =
      let rounded := Internal.Directed.roundDyadic fmt mode exact
      { value := rounded
        status := dyadicRoundingStatus fmt mode exact rounded
        ternary := dyadicTernary exact rounded } := by
  simp [scale, Internal.Status.scale, dyadicRoundingOutcome, hvalue]

/-- `scale` returns either infinity unchanged and raises no exception. -/
theorem scale_status_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) (negative : Bool)
    (hvalue : exactValue value = .infinity negative) :
    scale value n mode (status := true) =
      { value
        status := .clear
        ternary := .eq } := by
  simp [scale, Internal.Status.scale, hvalue, outcomeWithInvalid]

/-- `scale` quiets a NaN and raises `invalid` exactly for a signaling NaN. -/
theorem scale_status_of_nan
    {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    scale value n mode (status := true) =
      { value := quietNaN value
        status := { invalid := signaling }
        ternary := .eq } := by
  cases signaling <;>
    simp [scale, Internal.Status.scale, hvalue, outcomeWithInvalid, Numerics.IEEEStatus.clear]

/-- `binaryExponent` with `status := true` delivers the value of `binaryExponent`. -/
@[simp] theorem value_binaryExponent {fmt : FloatFormat} (value : Model fmt) :
    (binaryExponent value (status := true)).value = binaryExponent value :=
  rfl

/--
For a nonzero finite dyadic `±m * 2^e` with `m > 0`, `binaryExponent` returns the rounded
encoding of the integer `floor(log₂ m) + e`.
-/
theorem binaryExponent_status_of_finite_nonzero
    {fmt : FloatFormat} (value : Model fmt) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand ≠ 0) :
    binaryExponent value (status := true) =
      let exponent := Int.ofNat exact.significand.log2 + exact.exponent
      let exactResult := Numerics.Dyadic.ofScaledInt exponent 0
      let rounded := roundDyadic fmt exactResult
      { value := rounded
        status := dyadicRoundingStatus fmt .nearest exactResult rounded
        ternary := dyadicTernary exactResult rounded } := by
  simp [binaryExponent, Internal.Status.binaryExponent, dyadicRoundingOutcome, hvalue, hsignificand]

/--
`binaryExponent` of finite zero raises `divideByZero` and returns `nativeOverflow fmt true`.

For IEEE encodings that value is negative infinity, as IEEE 754-2019 §5.3.3 requires. For the
`finiteMaxNaN` and `finiteUnsignedZero` encodings, which have no infinity, it is the encoding's
NaN word, with the same `divideByZero` flag for the zero input. The `finite` encoding saturates to
its most negative finite value. The ternary value compares that delivery with the exact `-∞`.
-/
theorem binaryExponent_status_of_zero
    {fmt : FloatFormat} (value : Model fmt) (exact : Numerics.Dyadic)
    (hvalue : exactValue value = .finite exact)
    (hsignificand : exact.significand = 0) :
    binaryExponent value (status := true) =
      { value := nativeOverflow fmt true
        status := { divideByZero := true }
        ternary := exactInfinityTernary true (nativeOverflow fmt true) } := by
  simp [binaryExponent, Internal.Status.binaryExponent, hvalue, hsignificand]

/--
`binaryExponent` of either infinity returns `nativeOverflow fmt false` and raises no exception.
For IEEE encodings this is positive infinity. The ternary value compares that delivery with the
exact `+∞`.
-/
theorem binaryExponent_status_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (negative : Bool)
    (hvalue : exactValue value = .infinity negative) :
    binaryExponent value (status := true) =
      { value := nativeOverflow fmt false
        status := .clear
        ternary := exactInfinityTernary false (nativeOverflow fmt false) } := by
  simp [binaryExponent, Internal.Status.binaryExponent, hvalue]

/-- `binaryExponent` quiets a NaN and raises `invalid` exactly for a signaling NaN. -/
theorem binaryExponent_status_of_nan
    {fmt : FloatFormat} (value : Model fmt)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    binaryExponent value (status := true) =
      { value := quietNaN value
        status := { invalid := signaling }
        ternary := .eq } := by
  simp [binaryExponent, Internal.Status.binaryExponent, hvalue]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
