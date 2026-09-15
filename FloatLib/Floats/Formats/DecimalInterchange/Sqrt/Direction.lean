/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Semantics

/-!
# Directed square-root bounds and tininess

In the absence of overflow, the returned values bound the real square root in
the requested direction. Decimal underflow tests the exact root before rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem sqrtMagnitude_quantum_le_of_no_overflow (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = false) :
    (sqrtPair f mode x).2 ≤ f.maxQuantum := by
  apply le_of_not_gt
  intro h
  have ht := (sqrtMagnitude_overflow_iff f mode x preferred).mpr h
  simp [hfinite] at ht

theorem le_sqrtMagnitude_towardPositive (f : Format) {x : ℚ} (hx : 0 ≤ x)
    (preferred : Int)
    (hfinite : (sqrtMagnitude f .towardPositive x preferred).status.overflow = false) :
    ∃ value : ℚ, (sqrtMagnitude f .towardPositive x preferred).value.toRat? = some value ∧
      Real.sqrt (x : ℝ) ≤ (value : ℝ) := by
  have hq := sqrtMagnitude_quantum_le_of_no_overflow f .towardPositive x preferred hfinite
  refine ⟨_, sqrtMagnitude_value f .towardPositive x preferred hq, ?_⟩
  have hu : 0 < (10 : ℝ) ^ sqrtQuantum f x := zpow_pos (by norm_num) _
  have h := le_sqrtRound_towardPositive
    (div_nonneg hx
      (zpow_pos (by norm_num : (0 : ℚ) < 10) (2 * sqrtQuantum f x)).le)
  have hs := mul_le_mul_of_nonneg_right h hu.le
  rw [sqrt_scaled] at hs
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat] using hs

theorem sqrtMagnitude_directed_le (f : Format) (mode : RoundingMode)
    (hm : mode = .towardZero ∨ mode = .towardNegative) {x : ℚ} (hx : 0 ≤ x)
    (preferred : Int)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = false) :
    ∃ value : ℚ, (sqrtMagnitude f mode x preferred).value.toRat? = some value ∧
      (value : ℝ) ≤ Real.sqrt (x : ℝ) := by
  have hq := sqrtMagnitude_quantum_le_of_no_overflow f mode x preferred hfinite
  refine ⟨_, sqrtMagnitude_value f mode x preferred hq, ?_⟩
  have hu : 0 < (10 : ℝ) ^ sqrtQuantum f x := zpow_pos (by norm_num) _
  have hx' : 0 ≤ x / (10 : ℚ) ^ (2 * sqrtQuantum f x) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have h : (mode.sqrtRound (x / (10 : ℚ) ^ (2 * sqrtQuantum f x)) : ℝ) ≤
      Real.sqrt ((x / (10 : ℚ) ^ (2 * sqrtQuantum f x) : ℚ) : ℝ) := by
    rcases hm with rfl | rfl
    · exact sqrtRound_towardZero_le hx'
    · exact sqrtRound_towardNegative_le hx'
  have hs := mul_le_mul_of_nonneg_right h hu.le
  rw [sqrt_scaled] at hs
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat] using hs

theorem sqrtMagnitude_error_lt_one (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = false) :
    ∃ value : ℚ, (sqrtMagnitude f mode x preferred).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt (x : ℝ)| < (10 : ℝ) ^ sqrtQuantum f x := by
  have hq := sqrtMagnitude_quantum_le_of_no_overflow f mode x preferred hfinite
  refine ⟨_, sqrtMagnitude_value f mode x preferred hq, ?_⟩
  let q := sqrtQuantum f x
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hx' : 0 ≤ x / (10 : ℚ) ^ (2 * q) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have h := sqrtRound_error_lt_one mode hx'
  have he :
      (((mode.sqrtRound (x / (10 : ℚ) ^ (2 * q)) : Nat) : ℝ) * (10 : ℝ) ^ q -
          Real.sqrt (x : ℝ)) =
        (((mode.sqrtRound (x / (10 : ℚ) ^ (2 * q)) : Nat) : ℝ) -
          Real.sqrt ((x / (10 : ℚ) ^ (2 * q) : ℚ) : ℝ)) * (10 : ℝ) ^ q := by
    rw [sub_mul, sqrt_scaled]
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat]
  rw [he, abs_mul, abs_of_pos hu]
  exact (mul_lt_mul_of_pos_right h hu).trans_eq (one_mul _)

/-- Underflow compares the exact mathematical root with the least normal magnitude. -/
theorem sqrtMagnitude_underflow_iff (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = false) :
    (sqrtMagnitude f mode x preferred).status.underflow = true ↔
      Real.sqrt (x : ℝ) < (f.minNormal : ℝ) ∧
        (sqrtMagnitude f mode x preferred).status.inexact = true := by
  have hq := sqrtMagnitude_quantum_le_of_no_overflow f mode x preferred hfinite
  have hn : (0 : ℚ) < f.minNormal :=
    mul_pos (pow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
  have he : Real.sqrt (x : ℝ) < (f.minNormal : ℝ) ↔ x < f.minNormal ^ 2 := by
    rw [Real.sqrt_lt (by exact_mod_cast hx) (by exact_mod_cast hn.le)]
    exact_mod_cast Iff.rfl
  simp [sqrtMagnitude, not_lt.mpr hq, he]

end FloatLib.Floats.Formats.DecimalInterchange
