/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable

/-!
# Rational nearest-even rounding with native and saturating overflow

The policy engine and descriptor rounder use the same exact quotient alignment.
The finite-value contract identifies their results with the independent real grid,
clipped at the finite endpoints exactly when the overflow policy saturates.
This includes OCP OFP8 revision 1.0, §5.2.1, SAT and NONSAT as instances.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

open FloatLib.Floats FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-- Native nearest-even policy rounding agrees with the descriptor's general rational path. -/
theorem roundRatGeneralOfDenNeZero_nearest_eq_roundRatScaledGeneral
    (fmt : FloatFormat) (entropy : Nat) (sign : Bool) (num den : Nat) (hd : den ≠ 0) :
    roundRatGeneralOfDenNeZero fmt .nearest entropy sign num den hd =
      roundRatScaledGeneral fmt sign num den 0 := by
  have hq (shift : Int) :
      roundQuot .nearest sign entropy
          (RationalBinary.scaleByPowerOfTwo num den shift).1
          (RationalBinary.scaleByPowerOfTwo num den shift).2 =
        roundQuotientEven
          (RationalBinary.scaleByPowerOfTwo num den shift).1
          (RationalBinary.scaleByPowerOfTwo num den shift).2 :=
    roundQuot_nearest_eq_roundQuotientEven sign entropy _ _
      (RationalBinary.scaleByPowerOfTwo_snd_ne_zero num den shift hd)
  have hsub := minSubnormalExponent_lt_minNormalExponent fmt
  unfold roundRatGeneralOfDenNeZero roundRatScaledGeneral
  simp only [QuantizationPolicy.nearest, applyUnderflow, overflowResult,
    overflowRoundsMagnitudeUp, directedOverflow, beq_iff_eq, hd, ite_false,
    Int.add_zero, Int.zero_add]
  split_ifs with hn he hs ht ht
  all_goals
    simp_all only [tinyRoundsMagnitudeUp?, not_lt,
      roundQuot_nearest_eq_roundQuotientEven sign entropy _ den hd]
  all_goals
    first
    | rfl
    | omega
    | cases hshift : Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den <;>
        simpa only [RationalBinary.scaleByPowerOfTwo, hshift] using
          congrArg (packRoundedNormal fmt sign (nativeOverflow fmt sign)
            (RationalBinary.floorLog2 num den))
            (hq (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den))

/-- Every nearest-even overflow result has the signed finite endpoint when it is finite. -/
theorem toReal_overflowResult_nearest (fmt : FloatFormat) (overflow : OverflowMode)
    (sign : Bool) (hf : isFinite (overflowResult fmt overflow .nearest sign) = true) :
    toReal (overflowResult fmt overflow .nearest sign) =
      (if sign then (-1 : ℝ) else 1) * toReal (posMaxFinite fmt) := by
  cases overflow with
  | native => exact toReal_nativeOverflow_of_isFinite sign hf
  | saturate => exact toReal_maxFinite fmt sign

/-- Nearest-even overflow has a finite endpoint for SAT or for a fully finite encoding. -/
theorem isFinite_overflowResult_nearest_eq (fmt : FloatFormat) (overflow : OverflowMode)
    (sign : Bool) :
    isFinite (overflowResult fmt overflow .nearest sign) =
      decide (overflow = .saturate ∨ fmt.encoding = .finite) := by
  cases overflow <;>
    simp [overflowResult, overflowRoundsMagnitudeUp, directedOverflow,
      isFinite_nativeOverflow_eq]

/-- Real-grid rounding of a signed rational uses the exact quotient at its grid exponent. -/
theorem roundAt_rat_eq (fmt : FloatFormat) (sign : Bool) (num den : Nat) (hd : den ≠ 0) :
    roundAt fmt (signedScaledRatToReal sign num den 0) =
      (if sign then (-1 : ℝ) else 1) *
        (roundQuotientEven
          (RationalBinary.scaleByPowerOfTwo num den
            (-fexpOf fmt (RationalBinary.floorLog2 num den + 1))).1
          (RationalBinary.scaleByPowerOfTwo num den
            (-fexpOf fmt (RationalBinary.floorLog2 num den + 1))).2 : ℝ) *
        bpow (fexpOf fmt (RationalBinary.floorLog2 num den + 1)) := by
  have h := roundAt_scaledRat_eq fmt sign num den 0 hd
  cases sign <;>
    simpa only [Int.add_zero, Int.zero_sub, Bool.false_eq_true, ite_false, ite_true,
      Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_neg, one_mul,
      neg_one_mul, neg_mul] using h

/-- In the normal range the quotient aligns to the descriptor's fraction width. -/
theorem roundAt_rat_normal (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (hd : den ≠ 0) (hmin : fmt.minNormalExponent ≤ RationalBinary.floorLog2 num den) :
    roundAt fmt (signedScaledRatToReal sign num den 0) =
      (if sign then (-1 : ℝ) else 1) *
        (roundQuotientEven
          (RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).1
          (RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).2 : ℝ) *
        bpow (RationalBinary.floorLog2 num den - Int.ofNat fmt.fracWidth) := by
  rw [roundAt_rat_eq fmt sign num den hd, fexpOf_total_eq_normal fmt _ hmin]
  rw [neg_sub]

/-- The general nearest-even rounder packs the exact aligned quotient in the normal range. -/
theorem roundRatGeneral_nearest_eq_pack_of_normal
    (fmt : FloatFormat) (overflow : OverflowMode) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hn : num ≠ 0) (hd : den ≠ 0)
    (hmin : fmt.minNormalExponent ≤ RationalBinary.floorLog2 num den)
    (hmax : RationalBinary.floorLog2 num den ≤ fmt.maxNormalExponent) :
    roundRatGeneralOfDenNeZero fmt
      { rounding := .nearest, overflow } entropy sign num den hd =
      packRoundedNormal fmt sign (overflowResult fmt overflow .nearest sign)
        (RationalBinary.floorLog2 num den)
        (roundQuotientEven
          (RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).1
          (RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).2) := by
  have hq := roundQuot_nearest_eq_roundQuotientEven sign entropy
    (RationalBinary.scaleByPowerOfTwo num den
      (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).1
    (RationalBinary.scaleByPowerOfTwo num den
      (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).2
    (RationalBinary.scaleByPowerOfTwo_snd_ne_zero num den _ hd)
  simp only [roundRatGeneralOfDenNeZero, applyUnderflow, beq_iff_eq, hn,
    ite_false, not_lt.mpr hmin, not_lt.mpr hmax]
  cases hshift : Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den <;>
    simpa only [RationalBinary.scaleByPowerOfTwo, hshift] using
      congrArg (packRoundedNormal fmt sign (overflowResult fmt overflow .nearest sign)
        (RationalBinary.floorLog2 num den)) hq

/-- OCP OFP8 revision 1.0, §5.2.1, generalized to every descriptor and rational input:
finite nearest-even results denote real grid rounding, clipped exactly for a finite overflow
endpoint. The hypothesis excludes exceptional NONSAT outputs. -/
theorem toReal_roundRatGeneral_nearest
    (fmt : FloatFormat) (overflow : OverflowMode) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hd : den ≠ 0)
    (hf : isFinite (roundRatGeneralOfDenNeZero fmt
      { rounding := .nearest, overflow } entropy sign num den hd) = true) :
    toReal (roundRatGeneralOfDenNeZero fmt
      { rounding := .nearest, overflow } entropy sign num den hd) =
      if isFinite (overflowResult fmt overflow .nearest sign) then
        clampAt fmt (roundAt fmt (signedScaledRatToReal sign num den 0))
      else roundAt fmt (signedScaledRatToReal sign num den 0) := by
  by_cases hn : num = 0
  · subst num
    have hM := (toReal_posMaxFinite_pos fmt).le
    simp [roundRatGeneralOfDenNeZero, applyUnderflow, signedScaledRatToReal,
      scaledRatToReal, clampAt, hM]
  have hround := roundAt_rat_eq fmt sign num den hd
  have hbounds := roundQuotientEven_normal_bounds fmt num den hn hd
  by_cases he : fmt.maxNormalExponent < RationalBinary.floorLog2 num den
  · simp only [roundRatGeneralOfDenNeZero, applyUnderflow, beq_iff_eq, hn,
      ite_false, he, ite_true] at hf ⊢
    have hnormal : fmt.minNormalExponent ≤ RationalBinary.floorLog2 num den :=
      (minNormalExponent_le_maxNormalExponent fmt).trans he.le
    have hround := roundAt_rat_normal fmt sign num den hd hnormal
    have hmag :=
      (posMaxFinite_lt_normalizedMagnitude_of_exponent fmt _ _ hbounds.1 he).le
    rw [toReal_overflowResult_nearest fmt overflow sign hf, ite_eq_left hf, hround,
      mul_assoc, clampAt_signedMagnitude fmt sign
        (mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _))]
    congr 1
    exact (min_eq_right hmag).symm
  by_cases hs : RationalBinary.floorLog2 num den < fmt.minNormalExponent
  · rw [fexpOf_total_eq_minSubnormal fmt _ hs] at hround
    by_cases ht : RationalBinary.floorLog2 num den + 1 < fmt.minSubnormalExponent
    · rw [roundQuotientEven_scaled_eq_zero num den _ hn hd (by omega)] at hround
      have hz : roundAt fmt (signedScaledRatToReal sign num den 0) = 0 := by
        simpa only [Nat.cast_zero, mul_zero, zero_mul] using hround
      have hM := (toReal_posMaxFinite_pos fmt).le
      simp [roundRatGeneralOfDenNeZero, applyUnderflow, hn, he, hs, ht,
        tinyRoundsMagnitudeUp?, hz, clampAt, hM]
    · have halign := subnormalAlignExp_add_minSubnormalExponent fmt
      have hshift : -fmt.minSubnormalExponent =
          Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) := by
        simpa only [FloatFormat.subnormalAlignExp] using
          (show -fmt.minSubnormalExponent =
            Int.ofNat (FloatFormat.subnormalAlignExp fmt) by omega)
      rw [hshift] at hround
      simp only [RationalBinary.scaleByPowerOfTwo] at hround
      have hq : roundQuotientEven (Nat.shiftLeft num
          (fmt.exponentBias + fmt.fracWidth - 1)) den ≤
          pow2 fmt.fracWidth := by
        simpa only [Int.zero_add, FloatFormat.subnormalAlignExp,
          RationalBinary.scaleByPowerOfTwo] using
          roundQuotientEven_subnormal_le fmt num den 0 hn hd (by simpa using hs)
      have hbounded : |roundAt fmt (signedScaledRatToReal sign num den 0)| ≤
          toReal (posMaxFinite fmt) := by
        rw [hround]
        have hm := subnormalMagnitude_le_posMaxFinite fmt _ hq
        cases sign <;>
          simpa [abs_mul, abs_of_nonneg (bpow_nonneg _)] using hm
      simp only [roundRatGeneralOfDenNeZero, applyUnderflow, beq_iff_eq, hn,
        ite_false, he, hs, ite_true, ht,
        roundQuot_nearest_eq_roundQuotientEven sign entropy _ den hd]
      rw [toReal_packRoundedSubnormal fmt sign _ hq, clampAt_eq_self fmt hbounded,
        hround]
      simp only [ite_self]
  · have hnormal := le_of_not_gt hs
    have hround := roundAt_rat_normal fmt sign num den hd hnormal
    have hp := roundRatGeneral_nearest_eq_pack_of_normal fmt overflow entropy sign num den
      hn hd hnormal (le_of_not_gt he)
    rw [hp] at hf ⊢
    rw [toReal_packRoundedNormal_of_overflow fmt sign _ _ _ hbounds.1 hbounds.2
      hnormal (toReal_overflowResult_nearest fmt overflow sign) hf,
      hround, mul_assoc, clampAt_signedMagnitude fmt sign
        (mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _))]
    split_ifs <;> rfl

/-- Finite results of the public rational policy rounder have the same independent
nearest-even grid semantics, including its specialized IEEE path. -/
theorem toReal_roundRat_nearest
    (fmt : FloatFormat) (overflow : OverflowMode) (entropy : Nat)
    (sign : Bool) (num den : Nat) (rounded : Model fmt) (hd : den ≠ 0)
    (hr : roundRat fmt { rounding := .nearest, overflow } entropy sign num den =
      some rounded)
    (hf : isFinite rounded = true) :
    toReal rounded =
      if isFinite (overflowResult fmt overflow .nearest sign) then
        clampAt fmt (roundAt fmt (signedScaledRatToReal sign num den 0))
      else roundAt fmt (signedScaledRatToReal sign num den 0) := by
  cases overflow with
  | native =>
    have hr' : Model.roundRat fmt sign num den = rounded := by
      simpa only [show ({ rounding := .nearest, overflow := .native } :
          QuantizationPolicy) = .nearest from rfl,
        roundRat_nearest_eq_execFloat fmt entropy sign num den hd,
        Option.some.injEq] using hr
    subst rounded
    by_cases hi : fmt.isIEEE = true
    · have hover : isFinite (overflowResult fmt .native .nearest sign) = false := by
        change isFinite (nativeOverflow fmt sign) = false
        rw [isFinite_nativeOverflow_eq, ((FloatFormat.isIEEE_eq_true_iff fmt).mp hi).1]
        rfl
      simpa only [Model.roundRat, hover, Bool.false_eq_true, ite_false] using
        toReal_roundRatScaled_eq_roundAt fmt sign num den 0 hi hf
    · have hgeneral : roundRatGeneralOfDenNeZero fmt .nearest entropy sign num den hd =
          Model.roundRat fmt sign num den := by
        rw [roundRatGeneralOfDenNeZero_nearest_eq_roundRatScaledGeneral]
        simp [Model.roundRat, Model.roundRatScaled, hi]
      have h := toReal_roundRatGeneral_nearest fmt .native entropy sign num den hd
        (by simpa only [show ({ rounding := .nearest, overflow := .native } :
            QuantizationPolicy) = .nearest from rfl, hgeneral] using hf)
      simpa only [show ({ rounding := .nearest, overflow := .native } :
          QuantizationPolicy) = .nearest from rfl, hgeneral] using h
  | saturate =>
    have hr' : roundRatGeneralOfDenNeZero fmt
        { rounding := .nearest, overflow := .saturate } entropy sign num den hd =
          rounded := by
      simpa [roundRat, hd, QuantizationPolicy.nearest] using hr
    subst rounded
    exact toReal_roundRatGeneral_nearest fmt .saturate entropy sign num den hd hf

end FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
