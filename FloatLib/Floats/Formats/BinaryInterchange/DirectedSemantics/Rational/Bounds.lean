/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Downward
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Upward
public import FloatLib.Floats.Formats.BinaryInterchange.Model.SignedERealSemantics

/-!
# Signed bounds for conventional IEEE directed rational rounding

Positive-magnitude rational packing bounds extend to signed rationals by exchanging the
magnitude rounders under negation. Directed rounding swaps the lower and upper magnitude
rounders for negative values, while executable negation transports the result to the negative
half-line.

The main theorems apply to conventional IEEE `FloatFormat`s, retain infinities as valid outward
bounds in `EReal`, and establish that a nonzero denominator never produces NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

noncomputable section

@[simp] private theorem toEReal_posZero_eq_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toEReal (posZero fmt) = 0 := by
  simpa only [Bool.false_eq_true, ite_false] using
    toEReal_signedZero fmt hfmt false

@[simp] private theorem toEReal_negZero_eq_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toEReal (negZero fmt) = 0 := by
  simpa only [ite_eq_left rfl, ite_true] using
    toEReal_signedZero fmt hfmt true

/-- Changing only the stored sign negates a directed rational magnitude result. -/
theorem roundRatMagnitudeDirectedScaled_neg
    (fmt : FloatFormat) (roundMagnitudeUp : Bool)
    (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    roundRatMagnitudeDirectedScaled
        fmt roundMagnitudeUp true numerator denominator exponent =
      neg (roundRatMagnitudeDirectedScaled
        fmt roundMagnitudeUp false numerator denominator exponent) := by
  have hdenominator' : (denominator == 0) = false :=
    (beq_eq_false_iff_ne).2 hdenominator
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hsigned : fmt.supportsSignedZero = true := by
    simp [FloatFormat.supportsSignedZero, hencoding]
  have hzero :
      neg (zero fmt false) = zero fmt true := by
    simp [zero, hsigned]
  have hoverflow :
      neg (directedOverflow fmt false roundMagnitudeUp) =
        directedOverflow fmt true roundMagnitudeUp := by
    cases roundMagnitudeUp <;>
      simp [directedOverflow, nativeOverflow, hencoding]
  have hsubnormal (fraction : Nat) :
      packRoundedSubnormal fmt true (zero fmt true) fraction =
        neg (packRoundedSubnormal fmt false (zero fmt false) fraction) := by
    simp only [packRoundedSubnormal, neg_ite]
    simp only [hzero, neg_ofFields_of_supportsSignedZero fmt hsigned,
      Bool.not_false]
  have hnormal (totalExponent : Int) (roundedMantissa : Nat) :
      packRoundedNormal fmt true (directedOverflow fmt true roundMagnitudeUp)
          totalExponent roundedMantissa =
        neg (packRoundedNormal fmt false
          (directedOverflow fmt false roundMagnitudeUp)
          totalExponent roundedMantissa) := by
    simp only [packRoundedNormal, neg_ite]
    simp only [hoverflow, neg_ofFields_of_supportsSignedZero fmt hsigned,
      Bool.not_false]
  simp only [roundRatMagnitudeDirectedScaled, hdenominator',
    Bool.false_eq_true, ite_false, ite_true, neg_ite]
  simp only [hzero, hoverflow, neg_posMinSubnormal, ← hsubnormal, ← hnormal]

/-- Downward rounding of a signed scaled rational is an extended-real lower bound. -/
theorem toEReal_roundRatDownScaled_le
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    toEReal (roundRatDownScaled fmt sign numerator denominator exponent) ≤
      (signedScaledRatToReal sign numerator denominator exponent : EReal) := by
  by_cases hnumerator : numerator = 0
  · cases sign <;>
      simp [roundRatDownScaled, roundRatWithRoundingScaled,
        roundRatMagnitudeDirectedScaled, signedScaledRatToReal,
        scaledRatToReal, hnumerator, hdenominator, hfmt]
  · cases sign with
    | false =>
      simpa [roundRatDownScaled, roundRatWithRoundingScaled,
        signedScaledRatToReal] using
        toEReal_roundRatMagnitudeDirectedScaled_pos_down_le
          fmt numerator denominator exponent hfmt hnumerator hdenominator
    | true =>
      have hbound :=
        le_toEReal_roundRatMagnitudeDirectedScaled_pos_up
          fmt numerator denominator exponent hfmt hnumerator hdenominator
      have hnan :=
        isNaN_roundRatMagnitudeDirectedScaled_pos_up_eq_false
          fmt numerator denominator exponent hfmt hnumerator hdenominator
      change toEReal
          (roundRatMagnitudeDirectedScaled
            fmt true true numerator denominator exponent) ≤
        ((-scaledRatToReal numerator denominator exponent : ℝ) : EReal)
      rw [roundRatMagnitudeDirectedScaled_neg
        fmt true numerator denominator exponent hfmt hdenominator]
      rw [toEReal_neg_of_isNaN_eq_false _ hnan]
      simpa [EReal.coe_neg] using
        EReal.neg_le_neg_iff.mpr hbound

/-- A signed scaled rational is bounded above by its upward-rounded result. -/
theorem le_toEReal_roundRatUpScaled
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    (signedScaledRatToReal sign numerator denominator exponent : EReal) ≤
      toEReal (roundRatUpScaled fmt sign numerator denominator exponent) := by
  by_cases hnumerator : numerator = 0
  · cases sign <;>
      simp [roundRatUpScaled, roundRatWithRoundingScaled,
        roundRatMagnitudeDirectedScaled, signedScaledRatToReal,
        scaledRatToReal, hnumerator, hdenominator, hfmt]
  · cases sign with
    | false =>
      simpa [roundRatUpScaled, roundRatWithRoundingScaled,
        signedScaledRatToReal] using
        le_toEReal_roundRatMagnitudeDirectedScaled_pos_up
          fmt numerator denominator exponent hfmt hnumerator hdenominator
    | true =>
      have hbound :=
        toEReal_roundRatMagnitudeDirectedScaled_pos_down_le
          fmt numerator denominator exponent hfmt hnumerator hdenominator
      have hnan :=
        isNaN_roundRatMagnitudeDirectedScaled_pos_down_eq_false
          fmt numerator denominator exponent hfmt hnumerator hdenominator
      change ((-scaledRatToReal numerator denominator exponent : ℝ) : EReal) ≤
        toEReal
          (roundRatMagnitudeDirectedScaled
            fmt false true numerator denominator exponent)
      rw [roundRatMagnitudeDirectedScaled_neg
        fmt false numerator denominator exponent hfmt hdenominator]
      rw [toEReal_neg_of_isNaN_eq_false _ hnan]
      simpa [EReal.coe_neg] using
        EReal.neg_le_neg_iff.mpr hbound

/-- Downward rational rounding with a nonzero denominator never produces NaN. -/
theorem isNaN_roundRatDownScaled_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    isNaN (roundRatDownScaled fmt sign numerator denominator exponent) = false := by
  by_cases hnumerator : numerator = 0
  · cases sign <;>
      simp [roundRatDownScaled, roundRatWithRoundingScaled,
        roundRatMagnitudeDirectedScaled, hnumerator, hdenominator, hfmt]
  · cases sign with
    | false =>
      simpa [roundRatDownScaled, roundRatWithRoundingScaled] using
        isNaN_roundRatMagnitudeDirectedScaled_pos_down_eq_false
          fmt numerator denominator exponent hfmt hnumerator hdenominator
    | true =>
      change isNaN
          (roundRatMagnitudeDirectedScaled
            fmt true true numerator denominator exponent) = false
      rw [roundRatMagnitudeDirectedScaled_neg
        fmt true numerator denominator exponent hfmt hdenominator]
      simpa using
        isNaN_roundRatMagnitudeDirectedScaled_pos_up_eq_false
          fmt numerator denominator exponent hfmt hnumerator hdenominator

/-- Upward rational rounding with a nonzero denominator never produces NaN. -/
theorem isNaN_roundRatUpScaled_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    isNaN (roundRatUpScaled fmt sign numerator denominator exponent) = false := by
  by_cases hnumerator : numerator = 0
  · cases sign <;>
      simp [roundRatUpScaled, roundRatWithRoundingScaled,
        roundRatMagnitudeDirectedScaled, hnumerator, hdenominator, hfmt]
  · cases sign with
    | false =>
      simpa [roundRatUpScaled, roundRatWithRoundingScaled] using
        isNaN_roundRatMagnitudeDirectedScaled_pos_up_eq_false
          fmt numerator denominator exponent hfmt hnumerator hdenominator
    | true =>
      change isNaN
          (roundRatMagnitudeDirectedScaled
            fmt false true numerator denominator exponent) = false
      rw [roundRatMagnitudeDirectedScaled_neg
        fmt false numerator denominator exponent hfmt hdenominator]
      simpa using
        isNaN_roundRatMagnitudeDirectedScaled_pos_down_eq_false
          fmt numerator denominator exponent hfmt hnumerator hdenominator

/-- Downward rounding of an unscaled signed rational is an extended-real lower bound. -/
theorem toEReal_roundRatDown_le
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    toEReal (roundRatDown fmt sign numerator denominator) ≤
      (signedScaledRatToReal sign numerator denominator 0 : EReal) := by
  exact toEReal_roundRatDownScaled_le
    fmt sign numerator denominator 0 hfmt hdenominator

/-- An unscaled signed rational is bounded above by its upward-rounded result. -/
theorem le_toEReal_roundRatUp
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    (signedScaledRatToReal sign numerator denominator 0 : EReal) ≤
      toEReal (roundRatUp fmt sign numerator denominator) := by
  exact le_toEReal_roundRatUpScaled
    fmt sign numerator denominator 0 hfmt hdenominator

/-- Unscaled downward rational rounding with a nonzero denominator never produces NaN. -/
theorem isNaN_roundRatDown_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (roundRatDown fmt sign numerator denominator) = false := by
  exact isNaN_roundRatDownScaled_eq_false
    fmt sign numerator denominator 0 hfmt hdenominator

/-- Unscaled upward rational rounding with a nonzero denominator never produces NaN. -/
theorem isNaN_roundRatUp_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (roundRatUp fmt sign numerator denominator) = false := by
  exact isNaN_roundRatUpScaled_eq_false
    fmt sign numerator denominator 0 hfmt hdenominator

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
