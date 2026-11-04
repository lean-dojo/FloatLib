/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Quotient.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.NearestEven
public import FloatLib.Floats.ExecFloat.Backends.Generic.QuotientRound.Proof

/-!
# Shared bounds for native-word quotient kernels

The one-word and binary64 division backends pack differently, but they normalize the same exact
rational quotient, so we prove the representation-independent facts once:

* the normalization shift is nonnegative, so an accepted normal specification is the scaled rational
  rounding `roundRatScaled` (`roundRatScaled_eq_of_normalSpec`),
* the rounded significand lies in `[2^fracWidth, 2^(fracWidth + 1)]`,
* the restoring quotient and its carry bit fit in the `UInt64` kernel.

Shift and significand bounds come before the representation-specific estimates. A shifted numerator
fits below bit 63 when `2 * (fracWidth + 1) ≤ 63`, while the quotient and a possible rounding
increment fit below bit 63 under the weaker condition `fracWidth ≤ 61`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeWordQuotient

open FloatLib.Numerics.FixedWord.RestoringQuotient

/-- A word below `2 ^ (width + 1)`, zero included, has its leading bit below `width + 1`. -/
private theorem log2_toNat_lt_succ (value : UInt64) (width : Nat)
    (hfit : value.toNat < 2 ^ (width + 1)) :
    value.log2.toNat < width + 1 := by
  by_cases hvalue : value = 0
  · subst hvalue
    rw [FloatLib.Numerics.FixedWord.log2_toNat]
    simp
  · exact FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      value (width + 1) hvalue hfit

/-- The normalizing shift computed by the native kernel is the corresponding integer difference. -/
theorem normalShift_eq
    (fmt : FloatFormat) (num den : UInt64)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1)) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    Int.ofNat shift =
      Int.ofNat fmt.fracWidth - rationalExponent := by
  have hnumLog := log2_toNat_lt_succ num fmt.fracWidth hnumFit
  have hrange := floorLog2RatWord_log_bounds num den
  simp only [Int.ofNat_eq_natCast] at hrange
  have hnumLogLe :
      (num.log2.toNat : Int) ≤ Int.ofNat fmt.fracWidth := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hnonnegative :
      0 ≤ Int.ofNat fmt.fracWidth -
        floorLog2RatWord num den := by
    have hfloorLe := hrange.2
    omega
  exact Int.toNat_of_nonneg hnonnegative

/--
An accepted normal quotient specification on native significands is the scaled rational rounding
of their quotient.
-/
theorem roundRatScaled_eq_of_normalSpec
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) (num den : UInt64)
    (exponent : Int) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1)) (result : Model fmt)
    (hspec :
      FiniteQuotientRound.normalSpec? fmt sign num.toNat den.toNat exponent = some result) :
    result = Model.roundRatScaled fmt sign num.toNat den.toNat exponent := by
  apply FiniteQuotientRound.normalSpec_eq_roundRatScaled_of_some fmt hfmt sign _ _ exponent
    result _ hspec
  have hshift := normalShift_eq fmt num den hnumFit
  rw [← floorLog2RatWord_eq num den hden, ← hshift]
  exact Int.natCast_nonneg _

/--
The normalized numerator and its shift fit the signed-width budget used by the `UInt64` quotient
kernel.

The condition `2 * (fracWidth + 1) ≤ 63` is the representation boundary for this shifted-numerator
path. Binary32 and other narrow formats satisfy it, and wider one-word formats use the restoring
loop without first materializing the whole shifted numerator.
-/
theorem normalShift_bounds
    (fmt : FloatFormat) (num den : UInt64)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hdenFit : den.toNat < 2 ^ (fmt.fracWidth + 1))
    (hbudget : 2 * (fmt.fracWidth + 1) ≤ 63) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    shift < 64 ∧ num.toNat <<< shift < 2 ^ 63 := by
  let rationalExponent := floorLog2RatWord num den
  let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  have hnumLog := log2_toNat_lt_succ num fmt.fracWidth hnumFit
  have hdenLog := log2_toNat_lt_succ den fmt.fracWidth hdenFit
  have hrange := floorLog2RatWord_log_bounds num den
  simp only [Int.ofNat_eq_natCast] at hrange
  have hshiftInt :
      Int.ofNat shift =
        Int.ofNat fmt.fracWidth - rationalExponent :=
    normalShift_eq fmt num den hnumFit
  simp only [Int.ofNat_eq_natCast] at hshiftInt
  have hshiftLt : shift < 64 := by
    dsimp only [rationalExponent] at hshiftInt
    omega
  have hexponent :
      num.log2.toNat + 1 + shift ≤ 63 := by
    dsimp only [rationalExponent] at hshiftInt
    omega
  have hbound :
      num.toNat <<< shift <
        2 ^ (num.toNat.log2 + 1 + shift) :=
    Nat.shiftLeft_lt Nat.lt_log2_self
  rw [← FloatLib.Numerics.FixedWord.log2_toNat] at hbound
  exact ⟨hshiftLt, lt_of_lt_of_le hbound <|
    Nat.pow_le_pow_right (by decide) hexponent⟩

/-- Normalized nearest-even quotient rounding stays within the expected significand interval. -/
theorem roundedMantissa_bounds
    (fmt : FloatFormat) (num den : UInt64)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1)) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    2 ^ fmt.fracWidth ≤
        Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat ∧
      Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat ≤
        2 ^ (fmt.fracWidth + 1) := by
  let rationalExponent := floorLog2RatWord num den
  let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  have hnumNat : num.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hnum
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hfloor := floorLog2RatWord_eq num den hden
  have hshift := normalShift_eq fmt num den hnumFit
  have hscaled :
      Numerics.RationalBinary.scaleByPowerOfTwo num.toNat den.toNat
          (Int.ofNat fmt.fracWidth -
            Numerics.RationalBinary.floorLog2 num.toNat den.toNat) =
        (num.toNat <<< shift, den.toNat) := by
    rw [← hfloor, ← hshift]
    rfl
  have hrounded :=
    Model.roundQuotientEven_normal_bounds
      fmt num.toNat den.toNat hnumNat hdenNat
  dsimp only at hrounded
  rw [hscaled] at hrounded
  simpa only [Model.pow2_eq_two_pow] using hrounded

/--
The restoring quotient and a possible rounding increment fit below bit 63.

The bound `fracWidth ≤ 61` leaves room for a significand carry and a possible rounding increment
without using bit 63.
-/
theorem quotient_lt_two_pow_63
    (fmt : FloatFormat) (num den : UInt64)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hfracWidth : fmt.fracWidth ≤ 61) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    (num.toNat <<< shift) / den.toNat + 1 < 2 ^ 63 := by
  by_cases hnum : num = 0
  · subst hnum
    simp
  by_cases hden : den = 0
  · subst hden
    simp
  let rationalExponent := floorLog2RatWord num den
  let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hroundedUpper :
      Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat ≤
        2 ^ (fmt.fracWidth + 1) :=
    (roundedMantissa_bounds fmt num den hnum hden hnumFit).2
  have hfloorLe :
      (num.toNat <<< shift) / den.toNat ≤
        Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat := by
    have hsandwich :=
      Model.roundQuotDirected_false_le_roundQuotientEven_le_true
        (num.toNat <<< shift) den.toNat hdenNat
    simpa [Model.roundQuotDirected] using hsandwich.1
  change
    (num.toNat <<< shift) / den.toNat + 1 < 2 ^ 63
  have hpow : 2 ^ (fmt.fracWidth + 1) < 2 ^ 63 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeWordQuotient
