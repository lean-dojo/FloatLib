/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
public import FloatLib.Numerics.Quantization.Stochastic.Finite

/-!
# The distribution of the executable stochastic quotient

These theorems refine `roundQuot`, the actual natural-number implementation.
They give its law and its exact quotient bias under finite uniform entropy.
No theorem here silently extends quotient unbiasedness through overflow or flushing:
packing and exceptional-output policies require their own hypotheses.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

open MeasureTheory ProbabilityTheory FloatLib.Numerics.Quantization.Stochastic

/-- The early return on an exact quotient agrees with the uniform threshold description. -/
theorem roundQuot_stochastic (sign : Bool) (e num den : ℕ) :
    roundQuot .stochastic sign e num den =
      if e % den < num % den then num / den + 1 else num / den := by
  by_cases h : num % den = 0 <;> simp [roundQuot, h]

/-- The runtime quotient has the common counted finite-entropy Bernoulli distribution. -/
theorem roundQuot_hasLaw (sign : Bool) (M num den : ℕ) (hM : 0 < M) :
    HasLaw (fun e ↦ (roundQuot .stochastic sign e num den : ℝ))
      (bernoulliMeasure ((num / den : ℕ) + 1 : ℝ) (num / den : ℕ)
        ⟨(Nat.count (fun e ↦ e % den < num % den) M : ℝ) / M,
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          (div_le_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_le.mpr (Nat.count_le _))⟩)
      (entropyLaw M) := by
  simpa only [roundQuot_stochastic, Nat.cast_ite, Nat.cast_add, Nat.cast_one] using
    hasLaw_finite_choice M hM (fun e ↦ e % den < num % den)
      (num / den : ℕ) ((num / den : ℕ) + 1)

/-- Exact runtime quotient bias; negative signed values reverse this magnitude bias. -/
theorem roundQuot_bias (sign : Bool) (M num den : ℕ) (hM : 0 < M) (hd : 0 < den) :
    (∫ e, (roundQuot .stochastic sign e num den : ℝ) ∂entropyLaw M) - (num : ℝ) / den =
      ((den : ℝ) * min (M % den) (num % den) -
        (M % den : ℕ) * (num % den : ℕ)) / ((M : ℝ) * den) := by
  rw [(roundQuot_hasLaw sign M num den hM).integral_eq, integral_bernoulliMeasure]
  have h := mod_bias M den (num % den) hM hd (Nat.mod_lt num hd).le
  rw [entropyLaw_real] at h
  have hsplit : (num : ℝ) = (num / den : ℕ) * (den : ℝ) + (num % den : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div num den).symm)
  change (Nat.count (fun e ↦ e % den < num % den) M : ℝ) / M *
      ((num / den : ℕ) + 1) +
      (1 - (Nat.count (fun e ↦ e % den < num % den) M : ℝ) / M) *
      (num / den : ℕ) - (num : ℝ) / den = _
  rw [← h]
  field_simp
  nlinarith

/-- Uniform entropy is exactly unbiased whenever its range is a multiple of the denominator. -/
theorem roundQuot_mean_of_dvd (sign : Bool) (M num den : ℕ)
    (hM : 0 < M) (hd : 0 < den) (hdiv : den ∣ M) :
    (∫ e, (roundQuot .stochastic sign e num den : ℝ) ∂entropyLaw M) = (num : ℝ) / den := by
  have h := roundQuot_bias sign M num den hM hd
  simp only [Nat.mod_eq_zero_of_dvd hdiv, zero_le, inf_of_le_left, CharP.cast_eq_zero, mul_zero,
    zero_mul, sub_self, zero_div] at h
  exact sub_eq_zero.mp h

/-- Euclidean division encloses a positive-denominator rational between adjacent integers. -/
theorem quotient_mem (num den : ℕ) (hd : 0 < den) :
    (num : ℝ) / den ∈ Set.Icc ((num / den : ℕ) : ℝ) (((num / den : ℕ) : ℝ) + 1) := by
  have hdr : (0 : ℝ) < den := Nat.cast_pos.mpr hd
  have hs : (num : ℝ) = (num / den : ℕ) * (den : ℝ) + (num % den : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div num den).symm)
  have hr : ((num % den : ℕ) : ℝ) < den := Nat.cast_lt.mpr (Nat.mod_lt num hd)
  constructor
  · apply (le_div_iff₀ hdr).mpr
    linarith
  · apply (div_le_iff₀ hdr).mpr
    linarith

/-- With an exact residue law, the executable quotient realizes the ideal cell contract. -/
theorem roundQuot_cell (sign : Bool) (M num den : ℕ)
    (hM : 0 < M) (hd : 0 < den) (hdiv : den ∣ M) :
    HasLaw (fun e ↦ (roundQuot .stochastic sign e num den : ℝ))
      (cellLaw (num / den : ℕ) ((num / den : ℕ) + 1) ((num : ℝ) / den)
        (lt_add_one _) (quotient_mem num den hd)) (entropyLaw M) := by
  have h := roundQuot_hasLaw sign M num den hM
  have hp := entropyLaw_mod_of_dvd M den (num % den) hM hd (Nat.mod_lt num hd).le hdiv
  rw [entropyLaw_real] at hp
  have hs : (num : ℝ) = (num / den : ℕ) * (den : ℝ) + (num % den : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div num den).symm)
  have he :
      (Nat.count (fun e ↦ e % den < num % den) M : ℝ) / M =
      (((num : ℝ) / den) - (num / den : ℕ)) / (((num / den : ℕ) + 1) - (num / den : ℕ)) := by
    rw [hp]
    have hdr : (den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    field_simp
    linarith
  unfold cellLaw upProb
  convert h using 2
  congr 1
  exact he.symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
