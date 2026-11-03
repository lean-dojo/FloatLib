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

section

@[simp] private theorem toEReal_posZero_eq_zero (fmt : FloatFormat) :
    toEReal (posZero fmt) = 0 := by
  rw [toEReal_eq_coe_toReal_of_isFinite _ (isFinite_posZero fmt), toReal_posZero, EReal.coe_zero]

@[simp] private theorem toEReal_negZero_eq_zero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    toEReal (negZero fmt) = 0 := by
  simpa only [ite_eq_left rfl, ite_true] using toEReal_signedZero fmt hfmt true

/--
In a conventional IEEE format with a nonzero denominator, changing only the stored sign negates a
directed rational magnitude result.
-/
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

/--
In a conventional IEEE format, directed rational magnitude rounding with a nonzero denominator
never produces NaN, in either magnitude direction and for either attached sign.
-/
theorem isNaN_roundRatMagnitudeDirectedScaled_eq_false
    (fmt : FloatFormat) (roundMagnitudeUp sign : Bool)
    (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (roundRatMagnitudeDirectedScaled
      fmt roundMagnitudeUp sign numerator denominator exponent) = false := by
  have hpositive :
      isNaN (roundRatMagnitudeDirectedScaled
        fmt roundMagnitudeUp false numerator denominator exponent) = false := by
    cases roundMagnitudeUp
    · exact isNaN_roundRatMagnitudeDirectedScaled_pos_down_eq_false
        fmt numerator denominator exponent hfmt hdenominator
    · exact isNaN_roundRatMagnitudeDirectedScaled_pos_up_eq_false
        fmt numerator denominator exponent hfmt hdenominator
  cases sign
  · exact hpositive
  · rw [roundRatMagnitudeDirectedScaled_neg
      fmt roundMagnitudeUp numerator denominator exponent hfmt hdenominator, isNaN_neg]
    exact hpositive

/--
In a conventional IEEE format with a nonzero denominator, attaching a negative sign negates a
directed rational magnitude result in the extended reals. The magnitude direction stays fixed, so
for a negative value it is the opposite numerical direction.
-/
theorem toEReal_roundRatMagnitudeDirectedScaled_neg
    (fmt : FloatFormat) (roundMagnitudeUp : Bool)
    (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    toEReal (roundRatMagnitudeDirectedScaled
        fmt roundMagnitudeUp true numerator denominator exponent) =
      -toEReal (roundRatMagnitudeDirectedScaled
        fmt roundMagnitudeUp false numerator denominator exponent) := by
  rw [roundRatMagnitudeDirectedScaled_neg
    fmt roundMagnitudeUp numerator denominator exponent hfmt hdenominator]
  exact toEReal_neg_of_isNaN_eq_false _
    (isNaN_roundRatMagnitudeDirectedScaled_eq_false
      fmt roundMagnitudeUp false numerator denominator exponent hfmt hdenominator)

/--
In a conventional IEEE format with a nonzero denominator, downward rounding of a signed scaled
rational is an extended-real lower bound.
-/
theorem toEReal_roundRatDownScaled_le
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    toEReal (roundRatDownScaled fmt sign numerator denominator exponent) ≤
      (signedScaledRatToReal sign numerator denominator exponent : EReal) := by
  cases sign with
  | false =>
    simpa [roundRatDownScaled, Internal.Directed.roundRatScaled,
      signedScaledRatToReal] using
      toEReal_roundRatMagnitudeDirectedScaled_pos_down_le
        fmt numerator denominator exponent hfmt hdenominator
  | true =>
    change toEReal
        (roundRatMagnitudeDirectedScaled
          fmt true true numerator denominator exponent) ≤
      ((-scaledRatToReal numerator denominator exponent : ℝ) : EReal)
    rw [toEReal_roundRatMagnitudeDirectedScaled_neg
      fmt true numerator denominator exponent hfmt hdenominator, EReal.coe_neg]
    exact EReal.neg_le_neg_iff.mpr
      (le_toEReal_roundRatMagnitudeDirectedScaled_pos_up
        fmt numerator denominator exponent hfmt hdenominator)

/--
In a conventional IEEE format with a nonzero denominator, a signed scaled rational is bounded
above by its upward-rounded result in the extended reals.
-/
theorem le_toEReal_roundRatUpScaled
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    (signedScaledRatToReal sign numerator denominator exponent : EReal) ≤
      toEReal (roundRatUpScaled fmt sign numerator denominator exponent) := by
  cases sign with
  | false =>
    simpa [roundRatUpScaled, Internal.Directed.roundRatScaled,
      signedScaledRatToReal] using
      le_toEReal_roundRatMagnitudeDirectedScaled_pos_up
        fmt numerator denominator exponent hfmt hdenominator
  | true =>
    change ((-scaledRatToReal numerator denominator exponent : ℝ) : EReal) ≤
      toEReal
        (roundRatMagnitudeDirectedScaled
          fmt false true numerator denominator exponent)
    rw [toEReal_roundRatMagnitudeDirectedScaled_neg
      fmt false numerator denominator exponent hfmt hdenominator, EReal.coe_neg]
    exact EReal.neg_le_neg_iff.mpr
      (toEReal_roundRatMagnitudeDirectedScaled_pos_down_le
        fmt numerator denominator exponent hfmt hdenominator)

/--
In a conventional IEEE format, downward rational rounding with a nonzero denominator never
produces NaN.
-/
theorem isNaN_roundRatDownScaled_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    isNaN (roundRatDownScaled fmt sign numerator denominator exponent) = false :=
  isNaN_roundRatMagnitudeDirectedScaled_eq_false
    fmt sign sign numerator denominator exponent hfmt hdenominator

/--
In a conventional IEEE format, upward rational rounding with a nonzero denominator never produces
NaN.
-/
theorem isNaN_roundRatUpScaled_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    isNaN (roundRatUpScaled fmt sign numerator denominator exponent) = false :=
  isNaN_roundRatMagnitudeDirectedScaled_eq_false
    fmt (!sign) sign numerator denominator exponent hfmt hdenominator

/--
In a conventional IEEE format with a nonzero denominator, downward rounding of an unscaled signed
rational is an extended-real lower bound.
-/
theorem toEReal_roundRatDown_le
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    toEReal (roundRatDown fmt sign numerator denominator) ≤
      (signedScaledRatToReal sign numerator denominator 0 : EReal) := by
  exact toEReal_roundRatDownScaled_le
    fmt sign numerator denominator 0 hfmt hdenominator

/--
In a conventional IEEE format with a nonzero denominator, an unscaled signed rational is bounded
above by its upward-rounded result in the extended reals.
-/
theorem le_toEReal_roundRatUp
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    (signedScaledRatToReal sign numerator denominator 0 : EReal) ≤
      toEReal (roundRatUp fmt sign numerator denominator) := by
  exact le_toEReal_roundRatUpScaled
    fmt sign numerator denominator 0 hfmt hdenominator

/--
In a conventional IEEE format, unscaled downward rational rounding with a nonzero denominator
never produces NaN.
-/
theorem isNaN_roundRatDown_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (roundRatDown fmt sign numerator denominator) = false := by
  exact isNaN_roundRatDownScaled_eq_false
    fmt sign numerator denominator 0 hfmt hdenominator

/--
In a conventional IEEE format, unscaled upward rational rounding with a nonzero denominator never
produces NaN.
-/
theorem isNaN_roundRatUp_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (roundRatUp fmt sign numerator denominator) = false := by
  exact isNaN_roundRatUpScaled_eq_false
    fmt sign numerator denominator 0 hfmt hdenominator

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
