/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.PositiveBounds

/-!
# Finiteness of saturating nearest-even packing

OCP OFP8 revision 1.0, §5.2.1, SAT conversion always returns a finite word
for a finite source. The packing statements here apply to every binary
descriptor, including encodings with a reserved negative-zero NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- A positive subnormal fraction is finite under every descriptor encoding. -/
theorem isFinite_ofFields_subnormal_of_pos (fmt : FloatFormat) (sign : Bool)
    (fraction : Nat) (hpos : 0 < fraction) (hhigh : fraction < 2 ^ fmt.fracWidth) :
    isFinite (ofFields fmt sign 0 fraction) = true := by
  rw [isFinite_ofFields fmt sign 0 fraction (by positivity) hhigh]
  have hexp := fmt.expAllOnesNat_pos
  cases fmt.encoding <;> simp_all <;> omega

/-- Subnormal packing is finite, including zero and carry into the least normal value. -/
theorem isFinite_packRoundedSubnormal (fmt : FloatFormat) (sign : Bool) (fraction : Nat) :
    isFinite (packRoundedSubnormal fmt sign (zero fmt sign) fraction) = true := by
  unfold packRoundedSubnormal
  split_ifs with hzero hnormal
  · exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
  · apply isFinite_ofFields_normal_of_le_maxFinite
    · decide
    · exact pow_pos (by decide) _
    · have hexp := fmt.four_le_two_pow_expWidth
      cases hencoding : fmt.encoding <;>
        simp [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent,
          hencoding] <;> omega
  · exact isFinite_ofFields_subnormal_of_pos fmt sign fraction
      (Nat.pos_of_ne_zero (by simpa only [beq_iff_eq] using hzero))
      (by simpa only [pow2_eq_two_pow] using lt_of_not_ge hnormal)

/-- Bounded normal packing returns a finite word or exactly the chosen overflow endpoint. -/
theorem isFinite_packRoundedNormal_or_eq_overflow (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (exponent : Int) (mantissa : Nat)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hhigh : mantissa ≤ pow2 (fmt.fracWidth + 1)) :
    isFinite (packRoundedNormal fmt sign overflow exponent mantissa) = true ∨
      packRoundedNormal fmt sign overflow exponent mantissa = overflow := by
  let normalizedExponent := if mantissa == pow2 (fmt.fracWidth + 1) then exponent + 1
    else exponent
  let normalizedMantissa := if mantissa == pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth
    else mantissa
  have he : fmt.minNormalExponent ≤ normalizedExponent := by
    dsimp [normalizedExponent]
    split_ifs <;> omega
  have hm : normalizedMantissa < pow2 (fmt.fracWidth + 1) := by
    dsimp [normalizedMantissa]
    split_ifs with hcarry
    · exact pow2_lt_pow2_succ _
    · simp only [beq_iff_eq] at hcarry
      omega
  have hf : normalizedMantissa - pow2 fmt.fracWidth < 2 ^ fmt.fracWidth := by
    simp only [pow2_eq_two_pow, pow_succ] at hm ⊢
    omega
  change (fun result => isFinite result = true ∨ result = overflow)
    (if normalizedExponent > fmt.maxNormalExponent then overflow else
    if Int.toNat (normalizedExponent + Int.ofNat fmt.exponentBias) > fmt.maxFiniteExpField ||
      (Int.toNat (normalizedExponent + Int.ofNat fmt.exponentBias) == fmt.maxFiniteExpField &&
        normalizedMantissa - pow2 fmt.fracWidth > fmt.maxFiniteFracField) then overflow else
      ofFields fmt sign (Int.toNat (normalizedExponent + Int.ofNat fmt.exponentBias))
        (normalizedMantissa - pow2 fmt.fracWidth))
  split_ifs with hemax hguard
  · exact Or.inr rfl
  · exact Or.inr rfl
  · left
    exact isFinite_ofFields_of_packingGuard_eq_false fmt sign _ _ he hf hguard

/-- A finite overflow endpoint makes every bounded normal packing finite. -/
theorem isFinite_packRoundedNormal (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (exponent : Int) (mantissa : Nat)
    (hoverflow : isFinite overflow = true)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hhigh : mantissa ≤ pow2 (fmt.fracWidth + 1)) :
    isFinite (packRoundedNormal fmt sign overflow exponent mantissa) = true := by
  rcases isFinite_packRoundedNormal_or_eq_overflow fmt sign overflow exponent mantissa
      hmin hhigh with hf | heq
  · exact hf
  · simpa only [heq] using hoverflow

namespace Policy

/-- Inputs below the normal range round to finite words under either overflow policy. -/
theorem isFinite_roundRatGeneral_nearest_of_lt_min (fmt : FloatFormat)
    (overflow : OverflowMode) (entropy : Nat) (sign : Bool) (num den : Nat)
    (hd : den ≠ 0) (hs : RationalBinary.floorLog2 num den < fmt.minNormalExponent) :
    isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
      entropy sign num den hd) = true := by
  have hz := isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
  have he : ¬fmt.maxNormalExponent < RationalBinary.floorLog2 num den :=
    not_lt.mpr (hs.le.trans (minNormalExponent_le_maxNormalExponent fmt))
  by_cases hn : num = 0
  · simpa [roundRatGeneralOfDenNeZero, applyUnderflow, hn] using hz
  by_cases ht : RationalBinary.floorLog2 num den + 1 < fmt.minSubnormalExponent
  · simpa [roundRatGeneralOfDenNeZero, applyUnderflow, hn, he, hs, ht,
      tinyRoundsMagnitudeUp?] using hz
  · simpa [roundRatGeneralOfDenNeZero, applyUnderflow, hn, he, hs, ht] using
      isFinite_packRoundedSubnormal fmt sign
        (roundQuot .nearest sign entropy
          (Nat.shiftLeft num (fmt.exponentBias + fmt.fracWidth - 1)) den)

/-- The rational rounder returns a finite word or exactly its selected overflow endpoint. -/
theorem isFinite_roundRatGeneral_nearest_or_eq_overflow (fmt : FloatFormat)
    (overflow : OverflowMode)
    (entropy : Nat) (sign : Bool) (num den : Nat) (hd : den ≠ 0) :
    isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
      entropy sign num den hd) = true ∨
      roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
        entropy sign num den hd = overflowResult fmt overflow .nearest sign := by
  have hz := isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
  by_cases hn : num = 0
  · left
    simpa [roundRatGeneralOfDenNeZero, applyUnderflow, hn] using hz
  by_cases he : fmt.maxNormalExponent < RationalBinary.floorLog2 num den
  · right
    simp [roundRatGeneralOfDenNeZero, applyUnderflow, hn, he]
  by_cases hs : RationalBinary.floorLog2 num den < fmt.minNormalExponent
  · exact Or.inl
      (isFinite_roundRatGeneral_nearest_of_lt_min fmt overflow entropy sign num den hd hs)
  · rw [roundRatGeneral_nearest_eq_pack_of_normal fmt overflow entropy sign num den hn hd
      (le_of_not_gt hs) (le_of_not_gt he)]
    have hb := roundQuotientEven_normal_bounds fmt num den hn hd
    exact isFinite_packRoundedNormal_or_eq_overflow fmt sign _ _ _
      (le_of_not_gt hs) hb.2

/-- Nearest-even rational rounding is finite when its overflow endpoint is finite. -/
theorem isFinite_roundRatGeneral_nearest (fmt : FloatFormat) (overflow : OverflowMode)
    (entropy : Nat) (sign : Bool) (num den : Nat) (hd : den ≠ 0)
    (hoverflow : isFinite (overflowResult fmt overflow .nearest sign) = true) :
    isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
      entropy sign num den hd) = true := by
  rcases isFinite_roundRatGeneral_nearest_or_eq_overflow fmt overflow entropy sign num den hd
      with hf | heq
  · exact hf
  · simpa only [heq] using hoverflow

/-- OCP OFP8 rev. 1.0, §5.2.1, SAT finiteness, generalized to every binary descriptor. -/
theorem isFinite_roundRat_saturate_nearest (fmt : FloatFormat) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hd : den ≠ 0) (rounded : Model fmt)
    (hr : roundRat fmt { rounding := .nearest, overflow := .saturate }
      entropy sign num den = some rounded) :
    isFinite rounded = true := by
  have hr' : roundRatGeneralOfDenNeZero fmt
      { rounding := .nearest, overflow := .saturate } entropy sign num den hd = rounded := by
    simpa [roundRat, hd, QuantizationPolicy.nearest] using hr
  subst rounded
  exact isFinite_roundRatGeneral_nearest fmt .saturate entropy sign num den hd (by simp
    [overflowResult])

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
