/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Div

/-!
# Exact nearest-even overflow classification

OCP OFP8 revision 1.0, §5.2.1, tests overflow after precision rounding.
The criterion here uses the independent real grid and applies to every binary
descriptor. An exceptional result is exactly the selected overflow word.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-- Normal packing is finite precisely when its endpoint is finite or its magnitude fits. -/
theorem isFinite_packRoundedNormal_normalized_iff (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent) :
    isFinite (packRoundedNormal fmt sign overflow exponent mantissa) = true ↔
      isFinite overflow = true ∨
        (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth) ≤
          toReal (posMaxFinite fmt) := by
  by_cases ho : isFinite overflow = true
  · simp only [ho, true_or, iff_true]
    exact isFinite_packRoundedNormal fmt sign overflow exponent mantissa ho hmin hhigh.le
  constructor
  · intro hf
    right
    have hv := toReal_packRoundedNormal_normalized fmt sign overflow mantissa exponent
      hlow hhigh hmin (fun h => (ho h).elim) hf
    have hb := abs_toReal_le_posMaxFinite_of_isFinite _ hf
    rw [hv] at hb
    cases sign <;> simpa [ho, abs_mul, abs_of_nonneg (bpow_nonneg _)] using hb
  · rintro (hf | hb)
    · exact (ho hf).elim
    have he : ¬fmt.maxNormalExponent < exponent := fun h =>
      (posMaxFinite_lt_normalizedMagnitude_of_exponent fmt mantissa exponent hlow h).not_ge hb
    have hg :
        ¬(decide ((exponent + Int.ofNat fmt.exponentBias).toNat > fmt.maxFiniteExpField) ||
          (exponent + Int.ofNat fmt.exponentBias).toNat == fmt.maxFiniteExpField &&
            decide (mantissa - pow2 fmt.fracWidth > fmt.maxFiniteFracField)) = true :=
      fun h => (posMaxFinite_lt_normalizedMagnitude_of_guard fmt mantissa exponent
        hlow hmin (le_of_not_gt he) h).not_ge hb
    simp only [packRoundedNormal, beq_iff_eq, Nat.ne_of_lt hhigh, ite_false, he, hg]
    apply isFinite_ofFields_of_packingGuard_eq_false fmt sign _ _ hmin _ hg
    simp only [pow2_eq_two_pow, pow_succ] at hhigh ⊢
    omega

/-- The normal-packing criterion includes a full significand carry. -/
theorem isFinite_packRoundedNormal_iff (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa ≤ pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent) :
    isFinite (packRoundedNormal fmt sign overflow exponent mantissa) = true ↔
      isFinite overflow = true ∨
        (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth) ≤
          toReal (posMaxFinite fmt) := by
  by_cases hc : mantissa = pow2 (fmt.fracWidth + 1)
  · rw [hc, packRoundedNormal_carry,
      isFinite_packRoundedNormal_normalized_iff fmt sign overflow _ _ le_rfl
        (pow2_lt_pow2_succ _) (by omega), normalizedMagnitude_carry]
  · exact isFinite_packRoundedNormal_normalized_iff fmt sign overflow mantissa exponent
      hlow (lt_of_le_of_ne hhigh hc) hmin

namespace Policy

/-- The public nearest-even rational dispatcher returns the general rounder's word,
including when it selects the specialized IEEE engine. -/
theorem roundRat_nearest_eq_general (fmt : FloatFormat) (overflow : OverflowMode)
    (entropy : Nat) (sign : Bool) (num den : Nat) (hd : den ≠ 0) :
    roundRat fmt { rounding := .nearest, overflow } entropy sign num den =
      some (roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
        entropy sign num den hd) := by
  cases overflow with
  | saturate => simp [roundRat, hd, QuantizationPolicy.nearest]
  | native =>
    change roundRat fmt .nearest entropy sign num den =
      some (roundRatGeneralOfDenNeZero fmt .nearest entropy sign num den hd)
    rw [roundRat_nearest_eq_execFloat fmt entropy sign num den hd,
      roundRatGeneralOfDenNeZero_nearest_eq_roundRatScaledGeneral]
    congr 1
    by_cases hn : num = 0
    · simp [hn, Model.roundRat_num_zero fmt sign den hd, roundRatScaledGeneral, hd]
    have hb := roundQuotientEven_normal_bounds fmt num den hn hd
    unfold Model.roundRat Model.roundRatScaled
    split_ifs with hi
    · exact KernelPath.ieeeRoundRatScaled_eq_general fmt hi sign num den 0 hd
        (by simpa only [pow2_eq_two_pow] using hb.2)
    · rfl

/-- Nearest-even rational rounding is finite exactly when the overflow endpoint is finite
or the independent rounded-grid value fits between the finite endpoints. -/
theorem isFinite_roundRatGeneral_nearest_iff (fmt : FloatFormat) (overflow : OverflowMode)
    (entropy : Nat) (sign : Bool) (num den : Nat) (hd : den ≠ 0) :
    isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
      entropy sign num den hd) = true ↔
      isFinite (overflowResult fmt overflow .nearest sign) = true ∨
        |roundAt fmt (signedScaledRatToReal sign num den 0)| ≤
          toReal (posMaxFinite fmt) := by
  by_cases ho : isFinite (overflowResult fmt overflow .nearest sign) = true
  · simp only [ho, true_or, iff_true]
    exact isFinite_roundRatGeneral_nearest fmt overflow entropy sign num den hd ho
  constructor
  · intro hf
    right
    have hb := abs_toReal_le_posMaxFinite_of_isFinite _ hf
    simpa only [toReal_roundRatGeneral_nearest fmt overflow entropy sign num den hd hf,
      ite_eq_right ho] using hb
  · rintro (hf | hb)
    · exact (ho hf).elim
    by_cases hn : num = 0
    · have hz := isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
      simpa [roundRatGeneralOfDenNeZero, applyUnderflow, hn] using hz
    have hq := roundQuotientEven_normal_bounds fmt num den hn hd
    by_cases he : fmt.maxNormalExponent < RationalBinary.floorLog2 num den
    · have hmin := (minNormalExponent_le_maxNormalExponent fmt).trans he.le
      rw [roundAt_rat_normal fmt sign num den hd hmin] at hb
      have hmag :=
        posMaxFinite_lt_normalizedMagnitude_of_exponent fmt _ _ hq.1 he
      exfalso
      apply hmag.not_ge
      cases sign <;> simpa [abs_mul, abs_of_nonneg (bpow_nonneg _)] using hb
    by_cases hs : RationalBinary.floorLog2 num den < fmt.minNormalExponent
    · exact isFinite_roundRatGeneral_nearest_of_lt_min fmt overflow entropy sign num den hd hs
    · have hmin := le_of_not_gt hs
      rw [roundRatGeneral_nearest_eq_pack_of_normal fmt overflow entropy sign num den hn hd
        hmin (le_of_not_gt he), isFinite_packRoundedNormal_iff fmt sign _ _ _ hq.1 hq.2 hmin]
      right
      rw [roundAt_rat_normal fmt sign num den hd hmin] at hb
      cases sign <;> simpa [abs_mul, abs_of_nonneg (bpow_nonneg _)] using hb

/-- Every exceptional result of general nearest-even rational rounding is the chosen
overflow word; finite inputs cannot enter another exceptional case. -/
theorem roundRatGeneral_nearest_eq_overflow_of_not_isFinite
    (fmt : FloatFormat) (overflow : OverflowMode) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hd : den ≠ 0)
    (hf : isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
      entropy sign num den hd) ≠ true) :
    roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow }
      entropy sign num den hd = overflowResult fmt overflow .nearest sign :=
  Or.resolve_left
    (isFinite_roundRatGeneral_nearest_or_eq_overflow fmt overflow entropy sign num den hd) hf

/-- OCP OFP8 rev. 1.0, §5.2.1, generalized to every descriptor: the public rounder's
finite-result criterion tests the independent rounded value, not the exact input. -/
theorem isFinite_roundRat_nearest_iff (fmt : FloatFormat) (overflow : OverflowMode)
    (entropy : Nat) (sign : Bool) (num den : Nat) (hd : den ≠ 0)
    (rounded : Model fmt)
    (hr : roundRat fmt { rounding := .nearest, overflow } entropy sign num den =
      some rounded) :
    isFinite rounded = true ↔
      isFinite (overflowResult fmt overflow .nearest sign) = true ∨
        |roundAt fmt (signedScaledRatToReal sign num den 0)| ≤
          toReal (posMaxFinite fmt) := by
  rw [roundRat_nearest_eq_general fmt overflow entropy sign num den hd,
    Option.some.injEq] at hr
  subst rounded
  exact isFinite_roundRatGeneral_nearest_iff fmt overflow entropy sign num den hd

/-- A nonfinite public nearest-even result is exactly the selected overflow word. -/
theorem roundRat_nearest_eq_overflow_of_not_isFinite
    (fmt : FloatFormat) (overflow : OverflowMode) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hd : den ≠ 0) (rounded : Model fmt)
    (hr : roundRat fmt { rounding := .nearest, overflow } entropy sign num den =
      some rounded) (hf : isFinite rounded ≠ true) :
    rounded = overflowResult fmt overflow .nearest sign := by
  rw [roundRat_nearest_eq_general fmt overflow entropy sign num den hd,
    Option.some.injEq] at hr
  subst rounded
  exact roundRatGeneral_nearest_eq_overflow_of_not_isFinite
    fmt overflow entropy sign num den hd hf

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
