/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Power
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticRuntime
public import FloatLib.Numerics.Quantization.Stochastic.Realization

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Grid

/-!
# Decoded stochastic rounding on every binary grid

The exact alignment and packing identities connect the executable integer
quotient to decoded values. Finite output and absence of clipping are explicit:
a finite saturated result alone does not imply unbiased rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

open FloatLib.Floats FloatLib.Numerics MeasureTheory ProbabilityTheory
open FloatLib.Numerics.Quantization.Stochastic
open scoped NNReal

/-- Stochastic quotient rounding selects one of the existing directed quotients. -/
theorem roundQuot_stochastic_directed (sign : Bool) (entropy num den : ℕ)
    (hd : den ≠ 0) :
    roundQuot .stochastic sign entropy num den =
      roundQuotDirected (decide (entropy % den < num % den)) num den := by
  by_cases hr : num % den = 0
  · simp [roundQuot_stochastic, roundQuotDirected, hr]
  · simp only [roundQuot_stochastic, roundQuotDirected, decide_eq_true_eq,
      roundQuotient_up_eq, hd, hr, ite_false]

/-- The spacing at the runtime's aligned significand, including the subnormal lattice. -/
noncomputable def stochasticSpacing (fmt : FloatFormat) (num den : ℕ) : ℝ :=
  bpow (if RationalBinary.floorLog2 num den < fmt.minNormalExponent then
    fmt.minSubnormalExponent else RationalBinary.floorLog2 num den - fmt.fracWidth)

/-- Alignment changes units but preserves the exact rational value. -/
theorem alignedRatio_value (fmt : FloatFormat) (num den : ℕ) :
    ((alignedRatio fmt num den).1 : ℝ) / (alignedRatio fmt num den).2 *
      stochasticSpacing fmt num den = (num : ℝ) / den := by
  unfold alignedRatio stochasticSpacing
  dsimp only
  split
  · have h := scaledRatToReal_subnormal_grid fmt num den 0
    rw [← scaleByPowerOfTwo_real] at h
    simpa [FloatFormat.subnormalAlignExp, RationalBinary.scaleByPowerOfTwo,
      scaledRatToReal] using h
  · have h := scaledRatToReal_normal_grid fmt num den
      (RationalBinary.floorLog2 num den) 0
    rw [← scaleByPowerOfTwo_real] at h
    cases he : (fmt.fracWidth : ℤ) - RationalBinary.floorLog2 num den <;>
      simpa [RationalBinary.scaleByPowerOfTwo, scaledRatToReal, Int.ofNat_eq_natCast, he] using h

/-- The runtime quotient lies in the packer's closed mantissa interval. -/
theorem roundQuot_stochastic_bounds (fmt : FloatFormat) (sign : Bool)
    (entropy num den : ℕ) (hn : num ≠ 0) (hd : den ≠ 0) :
    let ratio := alignedRatio fmt num den
    let q := roundQuot .stochastic sign entropy ratio.1 ratio.2
    if RationalBinary.floorLog2 num den < fmt.minNormalExponent then
      q ≤ pow2 fmt.fracWidth
    else pow2 fmt.fracWidth ≤ q ∧ q ≤ pow2 (fmt.fracWidth + 1) := by
  have hd' := Nat.ne_of_gt (alignedRatio_den_pos fmt num den (Nat.pos_of_ne_zero hd))
  dsimp only
  rw [roundQuot_stochastic_directed _ _ _ _ hd']
  by_cases hs : RationalBinary.floorLog2 num den < fmt.minNormalExponent
  · simp only [hs, ite_true]
    apply roundQuotDirected_le_pow2_of_div_lt
    have h := scaleByPowerOfTwo_subnormal_lt_pow2 fmt num den 0 hn hd (by simpa using hs)
    simpa [alignedRatio, hs, FloatFormat.subnormalAlignExp,
      RationalBinary.scaleByPowerOfTwo] using h
  · simp only [hs, ite_false]
    have h := roundQuotDirected_normal_bounds fmt
      (decide (entropy % (alignedRatio fmt num den).2 <
        (alignedRatio fmt num den).1 % (alignedRatio fmt num den).2)) num den hn hd
    cases he : (fmt.fracWidth : ℤ) - RationalBinary.floorLog2 num den <;>
      simpa [alignedRatio, hs, RationalBinary.scaleByPowerOfTwo, Int.ofNat_eq_natCast, he] using h

/-- Native overflow with gradual underflow leaves the quotient's grid value unchanged
when the output is finite and its rounded magnitude is within the finite range. -/
theorem toReal_roundRat_stochastic (fmt : FloatFormat) (sign : Bool)
    (entropy num den : ℕ) (hn : num ≠ 0) (hd : den ≠ 0)
    (he : RationalBinary.floorLog2 num den ≤ fmt.maxNormalExponent)
    (hf : isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      entropy sign num den hd) = true)
    (hb : (roundQuot .stochastic sign entropy (alignedRatio fmt num den).1
      (alignedRatio fmt num den).2 : ℝ) * stochasticSpacing fmt num den ≤
        toReal (posMaxFinite fmt)) :
    toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      entropy sign num den hd) =
      (if sign then (-1 : ℝ) else 1) *
        (roundQuot .stochastic sign entropy (alignedRatio fmt num den).1
          (alignedRatio fmt num den).2 : ℝ) * stochasticSpacing fmt num den := by
  have hq := roundQuot_stochastic_bounds fmt sign entropy num den hn hd
  have hp :
      roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
        entropy sign num den hd =
      if RationalBinary.floorLog2 num den < fmt.minNormalExponent then
        packRoundedSubnormal fmt sign (zero fmt sign)
          (roundQuot .stochastic sign entropy (alignedRatio fmt num den).1
            (alignedRatio fmt num den).2)
      else packRoundedNormal fmt sign (nativeOverflow fmt sign)
        (RationalBinary.floorLog2 num den)
        (roundQuot .stochastic sign entropy (alignedRatio fmt num den).1
          (alignedRatio fmt num den).2) := by
    unfold roundRatGeneralOfDenNeZero alignedRatio
    simp only [beq_iff_eq, hn, ite_false, not_lt_of_ge he, tinyRoundsMagnitudeUp?,
      ite_self, overflowResult, overflowRoundsMagnitudeUp, directedOverflow, applyUnderflow]
    split_ifs <;> rfl
  rw [hp] at hf ⊢
  by_cases hs : RationalBinary.floorLog2 num den < fmt.minNormalExponent
  · simp only [hs, ite_true] at hf hq ⊢
    simpa [stochasticSpacing, hs] using toReal_packRoundedSubnormal fmt sign _ hq
  · simp only [hs, ite_false] at hf hq ⊢
    rw [toReal_packRoundedNormal fmt sign _ _ hq.1 hq.2 (le_of_not_gt hs) hf]
    have hb' := hb
    simp only [stochasticSpacing, hs, ite_false] at hb'
    rw [min_eq_left hb']
    simp [stochasticSpacing, hs]

/-- The decoded runtime is unbiased when the aligned denominator divides the entropy
range and every possible output satisfies the finite, unclipped packing conditions. -/
theorem mean_roundRat_stochastic (fmt : FloatFormat) (sign : Bool)
    (M num den : ℕ) (hM : 0 < M) (hn : num ≠ 0) (hd : den ≠ 0)
    (he : RationalBinary.floorLog2 num den ≤ fmt.maxNormalExponent)
    (hdiv : (alignedRatio fmt num den).2 ∣ M)
    (hf : ∀ e, isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e sign num den hd) = true)
    (hb : ∀ e, (roundQuot .stochastic sign e (alignedRatio fmt num den).1
      (alignedRatio fmt num den).2 : ℝ) * stochasticSpacing fmt num den ≤
        toReal (posMaxFinite fmt)) :
    (∫ e, toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e sign num den hd) ∂entropyLaw M) =
      (if sign then (-1 : ℝ) else 1) * ((num : ℝ) / den) := by
  have hfun :
      (fun e ↦ toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
        e sign num den hd)) =
      fun e ↦ (if sign then (-1 : ℝ) else 1) *
        (roundQuot .stochastic sign e (alignedRatio fmt num den).1
          (alignedRatio fmt num den).2 : ℝ) * stochasticSpacing fmt num den := by
    funext e
    exact toReal_roundRat_stochastic fmt sign e num den hn hd he (hf e) (hb e)
  rw [hfun, integral_mul_const, integral_const_mul, roundQuot_mean_of_dvd sign M _ _ hM
    (alignedRatio_den_pos fmt num den (Nat.pos_of_ne_zero hd)) hdiv]
  rw [mul_assoc, alignedRatio_value]

/-- Checking the two possible encodings proves finiteness for every entropy integer. -/
theorem roundRat_stochastic_finite (fmt : FloatFormat) (policy : QuantizationPolicy)
    (hs : policy.rounding = .stochastic) (sign : Bool) (num den : ℕ) (hd : den ≠ 0)
    (hu : isFinite (roundRatGeneralOfDenNeZero fmt policy 0 sign num den hd) = true)
    (hl : isFinite (roundRatGeneralOfDenNeZero fmt policy
      ((alignedRatio fmt num den).2 - 1) sign num den hd) = true) (e : ℕ) :
    isFinite (roundRatGeneralOfDenNeZero fmt policy e sign num den hd) = true := by
  have h := roundRat_stochastic_choice fmt policy hs e sign num den hd
  dsimp only at h
  rw [h]
  split_ifs <;> assumption

/-- The upper quotient bounds every possible rounded magnitude. -/
theorem roundQuot_stochastic_upper (sign : Bool) (e num den : ℕ) :
    roundQuot .stochastic sign e num den ≤ roundQuot .stochastic sign 0 num den := by
  by_cases hr : num % den = 0
  · simp [roundQuot_stochastic, hr]
  · have hp : 0 < num % den := Nat.pos_of_ne_zero hr
    simp only [roundQuot_stochastic, Nat.zero_mod, hp, ite_true]
    split_ifs <;> omega

/-- The actual decoded error has the cell-width Hoeffding proxy, independently of sign.
The premises exclude exceptional outputs and clipping and require an exact residue law. -/
theorem subgaussian_roundRat_stochastic (fmt : FloatFormat) (sign : Bool)
    (M num den : ℕ) (hM : 0 < M) (hn : num ≠ 0) (hd : den ≠ 0)
    (he : RationalBinary.floorLog2 num den ≤ fmt.maxNormalExponent)
    (hdiv : (alignedRatio fmt num den).2 ∣ M)
    (hf : ∀ e, isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e sign num den hd) = true)
    (hb : ∀ e, (roundQuot .stochastic sign e (alignedRatio fmt num den).1
      (alignedRatio fmt num den).2 : ℝ) * stochasticSpacing fmt num den ≤
        toReal (posMaxFinite fmt)) :
    HasSubgaussianMGF
      (fun e ↦ toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
        e sign num den hd) - (if sign then (-1 : ℝ) else 1) * ((num : ℝ) / den))
      ((‖stochasticSpacing fmt num den‖₊ / 2) ^ 2) (entropyLaw M) := by
  let := entropyLaw_probability M hM
  have hq : HasSubgaussianMGF
      (fun e ↦ (roundQuot .stochastic sign e (alignedRatio fmt num den).1
        (alignedRatio fmt num den).2 : ℝ) -
        ((alignedRatio fmt num den).1 : ℝ) / (alignedRatio fmt num den).2)
      (1 / 4) (entropyLaw M) := by
    convert subgaussian_of_cell (roundQuot_cell sign M (alignedRatio fmt num den).1 _ hM
      (alignedRatio_den_pos fmt num den (Nat.pos_of_ne_zero hd)) hdiv)
      using 1
    norm_num
  convert hq.const_mul ((if sign then (-1 : ℝ) else 1) * stochasticSpacing fmt num den)
      using 1
  · funext e
    rw [toReal_roundRat_stochastic fmt sign e num den hn hd he (hf e) (hb e),
      ← alignedRatio_value fmt num den]
    ring
  · apply NNReal.coe_injective
    change (‖stochasticSpacing fmt num den‖ / 2) ^ 2 =
      ((if sign then (-1 : ℝ) else 1) * stochasticSpacing fmt num den) ^ 2 * (1 / 4)
    cases sign <;> norm_num [Real.norm_eq_abs, div_pow, sq_abs] <;> ring

/-- The decoded runtime's second moment is bounded by the squared half spacing. -/
theorem second_moment_roundRat_stochastic (fmt : FloatFormat) (sign : Bool)
    (M num den : ℕ) (hM : 0 < M) (hn : num ≠ 0) (hd : den ≠ 0)
    (he : RationalBinary.floorLog2 num den ≤ fmt.maxNormalExponent)
    (hdiv : (alignedRatio fmt num den).2 ∣ M)
    (hf : ∀ e, isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e sign num den hd) = true)
    (hb : ∀ e, (roundQuot .stochastic sign e (alignedRatio fmt num den).1
      (alignedRatio fmt num den).2 : ℝ) * stochasticSpacing fmt num den ≤
        toReal (posMaxFinite fmt)) :
    (∫ e, (toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e sign num den hd) - (if sign then (-1 : ℝ) else 1) * ((num : ℝ) / den)) ^ 2
        ∂entropyLaw M) ≤ (stochasticSpacing fmt num den) ^ 2 / 4 := by
  have hq := second_moment_of_cell_le (roundQuot_cell sign M
    (alignedRatio fmt num den).1 _ hM
    (alignedRatio_den_pos fmt num den (Nat.pos_of_ne_zero hd)) hdiv)
  norm_num at hq
  have hfun :
      (fun e ↦ (toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
        e sign num den hd) - (if sign then (-1 : ℝ) else 1) * ((num : ℝ) / den)) ^ 2) =
      fun e ↦ (stochasticSpacing fmt num den) ^ 2 *
        ((roundQuot .stochastic sign e (alignedRatio fmt num den).1
          (alignedRatio fmt num den).2 : ℝ) -
          (alignedRatio fmt num den).1 / (alignedRatio fmt num den).2) ^ 2 := by
    funext e
    rw [toReal_roundRat_stochastic fmt sign e num den hn hd he (hf e) (hb e),
      ← alignedRatio_value fmt num den]
    cases sign <;> dsimp <;> ring
  rw [hfun, integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hq (sq_nonneg _)).trans_eq (by ring)

end FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
