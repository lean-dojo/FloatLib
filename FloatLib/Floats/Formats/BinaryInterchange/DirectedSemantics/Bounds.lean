/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.PositiveBounds
public import FloatLib.Floats.Formats.BinaryInterchange.Model.SignedERealSemantics

/-!
# Signed bounds for conventional IEEE directed dyadic rounding

The semantic contracts of `roundDyadicDown` and `roundDyadicUp` give outward bounds for signed
dyadics. For every exact signed dyadic and conventional IEEE `FloatFormat`, executable downward
rounding is an extended-real lower bound and executable upward rounding is an extended-real
upper bound.

Infinities are handled by the positive-magnitude results. Negative inputs follow by swapping the
magnitude rounders and reversing order under negation.

For every descriptor, the directed rounders, the nearest-even general rounder, and the packing
helpers they share turn a nonnegative exact value into a value with a nonnegative real meaning. A
value that is not finite denotes zero, which covers the NaN that a finite-unsigned-zero encoding
delivers on overflow.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

section

/-- Conventional IEEE overflow results of opposite signs are negations of each other. -/
theorem nativeOverflow_true_eq_neg_false_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    nativeOverflow fmt true = neg (nativeOverflow fmt false) := by
  simp [nativeOverflow, FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt]

/--
When the format has signed zeros, rounding a magnitude downward and attaching a negative sign is
the negation of the same rounded magnitude with a positive sign.
-/
theorem roundDyadicMagnitudeDown_true_eq_neg_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hsigned : fmt.supportsSignedZero = true) :
    roundDyadicMagnitudeDown fmt true mantissa exponent =
      neg (roundDyadicMagnitudeDown fmt false mantissa exponent) := by
  have hzero : zero fmt true = neg (zero fmt false) := by
    simp [zero, hsigned]
  have hoverflow :
      maxFinite fmt true = neg (maxFinite fmt false) := by
    simp
  simp only [roundDyadicMagnitudeDown, neg_ite]
  simp only [← hzero, ← hoverflow,
    neg_ofFields_of_supportsSignedZero fmt hsigned, Bool.not_false]

/--
When the format has signed zeros and sign-symmetric overflow results, rounding a magnitude upward
and attaching a negative sign is the negation of the same rounded magnitude with a positive sign.
-/
theorem roundDyadicMagnitudeUp_true_eq_neg_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hsigned : fmt.supportsSignedZero = true)
    (hoverflow : nativeOverflow fmt true = neg (nativeOverflow fmt false)) :
    roundDyadicMagnitudeUp fmt true mantissa exponent =
      neg (roundDyadicMagnitudeUp fmt false mantissa exponent) := by
  have hmin : ofFields fmt true 0 1 = neg (ofFields fmt false 0 1) := by
    rw [neg_ofFields_of_supportsSignedZero fmt hsigned]
    rfl
  have hsubnormal (fraction : Nat) :
      packRoundedSubnormal fmt true (ofFields fmt true 0 1) fraction =
        neg (packRoundedSubnormal fmt false (ofFields fmt false 0 1) fraction) := by
    simp only [packRoundedSubnormal, neg_ite]
    simp only [← hmin, neg_ofFields_of_supportsSignedZero fmt hsigned,
      Bool.not_false]
  have hnormal (totalExponent : Int) (roundedMantissa : Nat) :
      packRoundedNormal fmt true (nativeOverflow fmt true)
          totalExponent roundedMantissa =
        neg (packRoundedNormal fmt false (nativeOverflow fmt false)
          totalExponent roundedMantissa) := by
    simp only [packRoundedNormal, neg_ite]
    simp only [← hoverflow, neg_ofFields_of_supportsSignedZero fmt hsigned,
      Bool.not_false]
  simp only [roundDyadicMagnitudeUp, neg_ite]
  simp only [← hmin, ← hoverflow, ← hsubnormal, ← hnormal]

/-- Directed-down rounding of an exact signed dyadic never produces a NaN. -/
theorem isNaN_roundDyadicDown_eq_false
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) :
    isNaN (roundDyadicDown fmt d) = false := by
  by_cases hmant : d.significand = 0
  · cases hsign : d.negative <;> simp [roundDyadicDown, hmant, hsign]
  · cases hsign : d.negative
    · rw [show roundDyadicDown fmt d =
          roundDyadicPosDown fmt d.significand d.exponent by
        simp [roundDyadicDown, roundDyadicPosDown, hmant, hsign]]
      exact isNaN_roundDyadicPosDown_eq_false fmt d.significand d.exponent hfmt
    · rw [show roundDyadicDown fmt d =
          neg (roundDyadicPosUp fmt d.significand d.exponent) by
        simp only [roundDyadicDown, beq_iff_eq, hmant, ite_false, hsign, ite_true,
          roundDyadicPosUp]
        exact roundDyadicMagnitudeUp_true_eq_neg_false fmt d.significand d.exponent
          (by simp [hfmt]) (nativeOverflow_true_eq_neg_false_of_isIEEE fmt hfmt)]
      simpa using isNaN_roundDyadicPosUp_eq_false
        fmt d.significand d.exponent hfmt hmant

/-- Directed-up rounding of an exact signed dyadic never produces a NaN. -/
theorem isNaN_roundDyadicUp_eq_false
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) :
    isNaN (roundDyadicUp fmt d) = false := by
  by_cases hmant : d.significand = 0
  · cases hsign : d.negative <;> simp [roundDyadicUp, hmant, hsign]
  · cases hsign : d.negative
    · rw [show roundDyadicUp fmt d =
          roundDyadicPosUp fmt d.significand d.exponent by
        simp [roundDyadicUp, roundDyadicPosUp, hmant, hsign]]
      exact isNaN_roundDyadicPosUp_eq_false fmt d.significand d.exponent hfmt hmant
    · rw [show roundDyadicUp fmt d =
          neg (roundDyadicPosDown fmt d.significand d.exponent) by
        simp only [roundDyadicUp, beq_iff_eq, hmant, ite_false, hsign, ite_true,
          roundDyadicPosDown]
        exact roundDyadicMagnitudeDown_true_eq_neg_false fmt d.significand d.exponent
          (by simp [hfmt])]
      simpa using isNaN_roundDyadicPosDown_eq_false
        fmt d.significand d.exponent hfmt

/-- Directed-down dyadic rounding never exceeds the exact signed dyadic value. -/
theorem toEReal_roundDyadicDown_le (fmt : FloatFormat) (d : Numerics.Dyadic) :
    fmt.isIEEE = true →
    toEReal (roundDyadicDown fmt d) ≤ (d.toReal : EReal) := by
  intro hfmt
  by_cases hmant : d.significand = 0
  · simp [roundDyadicDown, Numerics.Dyadic.toReal, hmant]
  · by_cases hsign : d.negative
    · have hbound :=
        le_toEReal_roundDyadicPosUp fmt d.significand d.exponent hfmt hmant
      have hnan :=
        isNaN_roundDyadicPosUp_eq_false fmt d.significand d.exponent hfmt hmant
      have hmant' : (d.significand == 0) = false :=
        beq_eq_false_iff_ne.mpr hmant
      rw [show roundDyadicDown fmt d =
          neg (roundDyadicPosUp fmt d.significand d.exponent) by
        simp only [roundDyadicDown, hmant', hsign, ite_true,
          roundDyadicPosUp]
        exact roundDyadicMagnitudeUp_true_eq_neg_false fmt d.significand d.exponent
          (by simp [hfmt]) (nativeOverflow_true_eq_neg_false_of_isIEEE fmt hfmt)]
      rw [toEReal_neg_of_isNaN_eq_false _ hnan]
      simpa [Numerics.Dyadic.toReal, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        EReal.neg_le_neg_iff.mpr hbound
    · simpa [roundDyadicDown, roundDyadicPosDown,
        Numerics.Dyadic.toReal, hmant, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        toEReal_roundDyadicPosDown_le fmt d.significand d.exponent hfmt hmant

/-- The exact signed dyadic value never exceeds directed-up dyadic rounding. -/
theorem le_toEReal_roundDyadicUp (fmt : FloatFormat) (d : Numerics.Dyadic) :
    fmt.isIEEE = true →
    (d.toReal : EReal) ≤ toEReal (roundDyadicUp fmt d) := by
  intro hfmt
  by_cases hmant : d.significand = 0
  · simp [roundDyadicUp, Numerics.Dyadic.toReal, hmant]
  · by_cases hsign : d.negative
    · have hbound :=
        toEReal_roundDyadicPosDown_le fmt d.significand d.exponent hfmt hmant
      have hnan :=
        isNaN_roundDyadicPosDown_eq_false fmt d.significand d.exponent hfmt
      have hmant' : (d.significand == 0) = false :=
        beq_eq_false_iff_ne.mpr hmant
      rw [show roundDyadicUp fmt d =
          neg (roundDyadicPosDown fmt d.significand d.exponent) by
        simp only [roundDyadicUp, hmant', hsign, ite_true,
          roundDyadicPosDown]
        exact roundDyadicMagnitudeDown_true_eq_neg_false fmt d.significand d.exponent
          (by simp [hfmt])]
      rw [toEReal_neg_of_isNaN_eq_false _ hnan]
      simpa [Numerics.Dyadic.toReal, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        EReal.neg_le_neg_iff.mpr hbound
    · simpa [roundDyadicUp, roundDyadicPosUp,
        Numerics.Dyadic.toReal, hmant, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        le_toEReal_roundDyadicPosUp fmt d.significand d.exponent hfmt hmant

/-! ## Nonnegative results of positive rounding -/

/-- A value that is not finite denotes zero. -/
theorem toReal_eq_zero_of_isFinite_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = false) : toReal x = 0 := by
  have hnone : toDyadic? x = none := by
    cases hdecode : toDyadic? x with
    | none => rfl
    | some d =>
        rw [isFinite_eq_true_of_toDyadic?_some hdecode] at hfinite
        contradiction
  simp [toReal_eq, hnone]

/-- A value with a clear sign bit has a nonnegative real value, whether or not it is finite. -/
theorem toReal_nonneg_of_signBit_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hsign : signBit x = false) : 0 ≤ toReal x := by
  cases hdecode : toDyadic? x with
  | none => simp [toReal_eq, hdecode]
  | some d =>
      have hnegative : d.negative = false :=
        (sign_eq_signBit_of_toDyadic?_some hdecode).trans hsign
      have hreal : toReal x = d.toReal := by
        simp [toReal_eq, hdecode]
      rw [hreal, Numerics.Dyadic.toReal]
      simp only [Numerics.Dyadic.cast_signedSignificand, hnegative, Bool.false_eq_true, ite_false,
        one_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le

/-- The positive native overflow value has a nonnegative real value in every encoding. -/
theorem toReal_nativeOverflow_false_nonneg (fmt : FloatFormat) :
    0 ≤ toReal (nativeOverflow fmt false) := by
  cases hencoding : fmt.encoding with
  | ieee =>
      exact toReal_nonneg_of_signBit_eq_false (by simp [nativeOverflow, hencoding])
  | finiteMaxNaN =>
      exact toReal_nonneg_of_signBit_eq_false (by simp [nativeOverflow, propagatedNaN, hencoding])
  | finiteUnsignedZero =>
      rw [toReal_eq_zero_of_isFinite_eq_false]
      apply isFinite_eq_false_of_isNaN
      simp [nativeOverflow, invalidResult, negZero, isNaN, hencoding, ofBits]
  | finite =>
      exact toReal_nonneg_of_signBit_eq_false (by simp [nativeOverflow, hencoding])

/-- Packing a positive normal significand gives a nonnegative value when `overflow` is one. -/
private theorem toReal_packRoundedNormal_false_nonneg (fmt : FloatFormat) (overflow : Model fmt)
    (totalExponent : Int) (roundedMantissa : Nat) (hoverflow : 0 ≤ toReal overflow) :
    0 ≤ toReal (packRoundedNormal fmt false overflow totalExponent roundedMantissa) := by
  unfold packRoundedNormal
  dsimp only
  split_ifs <;> first | exact hoverflow | exact toReal_nonneg_of_signBit_eq_false (by simp)

/-- Packing a positive subnormal significand gives a nonnegative value when `zeroResult` is one. -/
private theorem toReal_packRoundedSubnormal_false_nonneg (fmt : FloatFormat)
    (zeroResult : Model fmt) (fraction : Nat) (hzero : 0 ≤ toReal zeroResult) :
    0 ≤ toReal (packRoundedSubnormal fmt false zeroResult fraction) := by
  unfold packRoundedSubnormal
  split_ifs <;> first | exact hzero | exact toReal_nonneg_of_signBit_eq_false (by simp)

/-- Rounding a positive magnitude downward gives a nonnegative value. -/
theorem toReal_roundDyadicMagnitudeDown_false_nonneg (fmt : FloatFormat) (mantissa : Nat)
    (exponent : Int) : 0 ≤ toReal (roundDyadicMagnitudeDown fmt false mantissa exponent) := by
  apply toReal_nonneg_of_signBit_eq_false
  unfold roundDyadicMagnitudeDown
  dsimp only
  split_ifs <;> simp

/-- Rounding a positive magnitude upward gives a nonnegative value. -/
theorem toReal_roundDyadicMagnitudeUp_false_nonneg (fmt : FloatFormat) (mantissa : Nat)
    (exponent : Int) : 0 ≤ toReal (roundDyadicMagnitudeUp fmt false mantissa exponent) := by
  have hoverflow := toReal_nativeOverflow_false_nonneg fmt
  have hsubnormal := fun fraction =>
    toReal_packRoundedSubnormal_false_nonneg fmt (ofFields fmt false 0 1) fraction
      (toReal_nonneg_of_signBit_eq_false (by simp))
  have hnormal := fun totalExponent roundedMantissa =>
    toReal_packRoundedNormal_false_nonneg fmt (nativeOverflow fmt false) totalExponent
      roundedMantissa hoverflow
  unfold roundDyadicMagnitudeUp
  dsimp only
  split_ifs <;> first
    | with_reducible exact hoverflow
    | with_reducible exact hsubnormal _
    | with_reducible exact hnormal _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)

/-- Nearest-even rounding of a nonnegative dyadic gives a nonnegative value. -/
theorem toReal_roundDyadicGeneral_nonneg (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hvalue : value.negative = false) : 0 ≤ toReal (roundDyadicGeneral fmt value) := by
  have hoverflow := toReal_nativeOverflow_false_nonneg fmt
  have hsubnormal := fun fraction =>
    toReal_packRoundedSubnormal_false_nonneg fmt (zero fmt false) fraction
      (toReal_nonneg_of_signBit_eq_false (by simp))
  have hnormal := fun totalExponent roundedMantissa =>
    toReal_packRoundedNormal_false_nonneg fmt (nativeOverflow fmt false) totalExponent
      roundedMantissa hoverflow
  unfold roundDyadicGeneral
  dsimp only
  rw [hvalue]
  split_ifs <;> first
    | with_reducible exact hoverflow
    | with_reducible exact hsubnormal _
    | with_reducible exact hnormal _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)

/-- Rounding a nonnegative dyadic upward gives a nonnegative value. -/
theorem toReal_roundDyadicUp_nonneg (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hvalue : value.negative = false) : 0 ≤ toReal (roundDyadicUp fmt value) := by
  unfold roundDyadicUp
  rw [hvalue]
  split_ifs <;> first
    | with_reducible exact toReal_roundDyadicMagnitudeUp_false_nonneg fmt _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)
    | simp_all

/-- Rounding a nonnegative dyadic downward gives a nonnegative value. -/
theorem toReal_roundDyadicDown_nonneg (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hvalue : value.negative = false) : 0 ≤ toReal (roundDyadicDown fmt value) := by
  unfold roundDyadicDown
  rw [hvalue]
  split_ifs <;> first
    | with_reducible exact toReal_roundDyadicMagnitudeDown_false_nonneg fmt _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)
    | simp_all

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
