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

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
