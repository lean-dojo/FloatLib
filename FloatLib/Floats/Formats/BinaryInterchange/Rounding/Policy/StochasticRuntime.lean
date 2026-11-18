/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Stochastic

/-!
# Exact stochastic law through packing and output policies

The complete rational runtime chooses between the two encodings obtained from the
upper and lower quotient choices. This remains true at zero, subnormal carry,
saturation, native overflow, and output flushing, even if the encodings coincide.
The observation formula applies to any real-valued function of those encodings.
An indicator observes exceptional-output probability without treating NaN or
infinity as a real numerical value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

open FloatLib.Numerics MeasureTheory ProbabilityTheory
open FloatLib.Numerics.Quantization.Stochastic

/-- The exact ratio at the discarded-bit boundary, before quotient rounding. -/
def alignedRatio (fmt : FloatFormat) (num den : ℕ) : ℕ × ℕ :=
  let exponent := RationalBinary.floorLog2 num den
  if exponent < fmt.minNormalExponent then
    (Nat.shiftLeft num (fmt.exponentBias + fmt.fracWidth - 1), den)
  else
    match (Int.ofNat fmt.fracWidth - exponent) with
    | .ofNat amount => (Nat.shiftLeft num amount, den)
    | .negSucc amount => (num, Nat.shiftLeft den (amount + 1))

/-- Alignment never creates a zero denominator. -/
theorem alignedRatio_den_pos (fmt : FloatFormat) (num den : ℕ) (hd : 0 < den) :
    0 < (alignedRatio fmt num den).2 := by
  unfold alignedRatio
  dsimp only
  split
  · exact hd
  · split <;> simp_all [Nat.shiftLeft_eq]

private theorem quotient_choice (sign : Bool) (e num den : ℕ) (hd : 0 < den) :
    roundQuot .stochastic sign e num den =
      if e % den < num % den then roundQuot .stochastic sign 0 num den
      else roundQuot .stochastic sign (den - 1) num den := by
  have he : den - 1 < den := by omega
  have hr : num % den ≤ den - 1 := by have := Nat.mod_lt num hd; omega
  simp only [roundQuot_stochastic, Nat.zero_mod, Nat.mod_eq_of_lt he,
    not_lt_of_ge hr, ite_false]
  by_cases h : e % den < num % den
  · simp [h, show 0 < num % den by omega]
  · simp [h]

/-- The complete runtime is a single two-encoding choice, including exceptional policies. -/
theorem roundRat_stochastic_choice (fmt : FloatFormat) (policy : QuantizationPolicy)
    (hs : policy.rounding = .stochastic) (e : ℕ) (sign : Bool) (num den : ℕ)
    (hd : den ≠ 0) :
    let ratio := alignedRatio fmt num den
    let out := fun e ↦ roundRatGeneralOfDenNeZero fmt policy e sign num den hd
    out e = if e % ratio.2 < ratio.1 % ratio.2 then out 0 else out (ratio.2 - 1) := by
  dsimp only
  unfold roundRatGeneralOfDenNeZero alignedRatio
  simp only [hs, tinyRoundsMagnitudeUp?, ite_self]
  by_cases hz : num = 0
  · simp [hz]
  simp only [beq_iff_eq, hz, ite_false]
  by_cases hover : RationalBinary.floorLog2 num den > fmt.maxNormalExponent
  · simp [hover]
  simp only [hover, ite_false]
  by_cases hsub : RationalBinary.floorLog2 num den < fmt.minNormalExponent
  · simp only [hsub, ite_true]
    rw [quotient_choice sign e _ _ (Nat.pos_of_ne_zero hd)]
    simp only [apply_ite]
    split_ifs <;> rfl
  · simp only [hsub, ite_false]
    cases hshift : Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den with
    | ofNat amount =>
      dsimp only
      rw [quotient_choice sign e _ _ (Nat.pos_of_ne_zero hd)]
      simp only [apply_ite]
      split_ifs <;> rfl
    | negSucc amount =>
      dsimp only
      have hdshift : 0 < Nat.shiftLeft den (amount + 1) := by
        simpa only [Nat.shiftLeft_eq', Nat.shiftLeft_pos_iff] using Nat.pos_of_ne_zero hd
      rw [quotient_choice sign e num (Nat.shiftLeft den (amount + 1)) hdshift]
      simp only [apply_ite]
      split_ifs <;> rfl

/-- Exact expectation of every real observation of the complete stochastic runtime. -/
theorem integral_roundRat_stochastic (fmt : FloatFormat) (policy : QuantizationPolicy)
    (hs : policy.rounding = .stochastic) (sign : Bool) (M num den : ℕ)
    (hM : 0 < M) (hd : den ≠ 0) (f : Model fmt → ℝ) :
    let ratio := alignedRatio fmt num den
    let out := fun e ↦ roundRatGeneralOfDenNeZero fmt policy e sign num den hd
    let p : ℝ :=
      ((M / ratio.2) * (ratio.1 % ratio.2) + min (M % ratio.2) (ratio.1 % ratio.2) : ℕ) / M
    (∫ e, f (out e) ∂entropyLaw M) =
      p * f (out 0) + (1 - p) * f (out (ratio.2 - 1)) := by
  dsimp only
  have hfun :
      (fun e ↦ f (roundRatGeneralOfDenNeZero fmt policy e sign num den hd)) =
      fun e ↦ if e % (alignedRatio fmt num den).2 <
          (alignedRatio fmt num den).1 % (alignedRatio fmt num den).2 then
        f (roundRatGeneralOfDenNeZero fmt policy 0 sign num den hd) else
        f (roundRatGeneralOfDenNeZero fmt policy
          ((alignedRatio fmt num den).2 - 1) sign num den hd) := by
    funext e
    have h := roundRat_stochastic_choice fmt policy hs e sign num den hd
    dsimp only at h
    rw [h]
    simp only [apply_ite]
    split_ifs <;> rfl
  rw [hfun, integral_finite_choice M hM]
  rw [count_mod _ _ _ (alignedRatio_den_pos fmt num den (Nat.pos_of_ne_zero hd))
    (Nat.mod_lt _ (alignedRatio_den_pos fmt num den (Nat.pos_of_ne_zero hd))).le]

end FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
