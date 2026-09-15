/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.ToProof

/-!
# Binary conversion of zeros and NaNs

The zero theorem includes all status flags. The NaN field theorems establish the
stored sign, all-ones exponent and quiet-bit-plus-payload fraction independently
of any destination width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats FloatLib.Floats.Formats BinaryInterchange

/-- Zero magnitude cannot overflow in any rounding direction. -/
@[simp] theorem binaryOverflow_zero (fmt : FloatFormat) (mode : RoundingMode) (s : Bool) :
    binaryOverflow fmt mode s 0 = false := by
  have hmax : (0 : ℚ) < (Model.maxFiniteDyadic fmt).toRat := by
    change (0 : ℚ) < ((Model.pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℚ) *
      (2 : ℚ) ^ (fmt.maxNormalExponent - (fmt.fracWidth : Int))
    rw [Model.pow2_eq_two_pow]
    positivity
  have hmid : (0 : ℚ) < (Model.overflowMidpoint fmt).toRat := by
    change (0 : ℚ) < ((2 * (Model.maxFiniteDyadic fmt).significand + 1 : Nat) : ℚ) *
      (2 : ℚ) ^ ((Model.maxFiniteDyadic fmt).exponent - 1)
    positivity
  have hlimit : (0 : ℚ) < (Model.overflowLimit fmt).toRat := by
    change (0 : ℚ) < (((Model.maxFiniteDyadic fmt).significand + 1 : Nat) : ℚ) *
      (2 : ℚ) ^ (Model.maxFiniteDyadic fmt).exponent
    positivity
  cases mode <;> simp [binaryOverflow, not_le.mpr hmid, not_le.mpr hlimit,
    not_lt.mpr hmax.le]

/-- Every decimal zero cohort converts to the source-signed binary zero with clear status. -/
@[simp] theorem toBinary_zero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) (q : Int) :
    toBinary fmt hfmt mode (.finite s 0 q) =
      { value := Model.zero fmt s, status := {} } := by
  simp [toBinary, roundBinaryMagnitude_zero fmt hfmt, binaryStatus, Model.toRat?]

/-- NaN conversion preserves the sign bit for every destination width. -/
@[simp] theorem binaryNaN_signBit (fmt : FloatFormat) (s : Bool) (payload : Nat) :
    Model.signBit (binaryNaN fmt s payload) = s := by
  simp [binaryNaN]

/-- The encoded NaN exponent is all ones. -/
@[simp] theorem binaryNaN_expField (fmt : FloatFormat) (s : Bool) (payload : Nat) :
    Model.expField (binaryNaN fmt s payload) = fmt.expAllOnesNat := by
  simp only [binaryNaN, Model.expField_ofFields]
  apply Nat.mod_eq_of_lt
  simp only [FloatFormat.expAllOnesNat]
  exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)

/-- The quiet bit is set and the remaining fraction bits contain the selected payload. -/
@[simp] theorem binaryNaN_fracField (fmt : FloatFormat) (s : Bool) (payload : Nat) :
    Model.fracField (binaryNaN fmt s payload) =
      2 ^ (fmt.fracWidth - 1) +
        if payload < 2 ^ (fmt.fracWidth - 1) then payload else 0 := by
  simp only [binaryNaN, Model.fracField_ofFields]
  apply Nat.mod_eq_of_lt
  have hpow : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel fmt.fracWidth_pos]
  have hpos := Nat.two_pow_pos (fmt.fracWidth - 1)
  rw [hpow]
  split <;> omega

/-- The binary NaN constructed by conversion is classified as NaN on IEEE destinations. -/
@[simp] theorem binaryNaN_isNaN (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) (payload : Nat) :
    Model.isNaN (binaryNaN fmt s payload) = true := by
  have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
  simp [Model.isNaN, hencoding, Model.IEEE.isNaN]

/-- The highest fraction bit is one, so the constructed NaN is quiet. -/
theorem binaryNaN_quiet_bit (fmt : FloatFormat) (s : Bool) (payload : Nat) :
    Model.fracField (binaryNaN fmt s payload) / 2 ^ (fmt.fracWidth - 1) = 1 := by
  rw [binaryNaN_fracField]
  have hpos := Nat.two_pow_pos (fmt.fracWidth - 1)
  split
  · rename_i h
    rw [Nat.add_div hpos, Nat.div_self hpos, Nat.div_eq_of_lt h]
    simp [Nat.mod_lt _ hpos]
  · simp

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
