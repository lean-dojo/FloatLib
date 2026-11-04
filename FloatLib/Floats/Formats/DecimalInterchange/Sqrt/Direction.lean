/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Semantics

/-!
# Directed square-root bounds and tininess

Without overflow, the returned values bound the real square root from the requested side, and the
downward bound holds on overflow too. Decimal underflow tests the exact root, before rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Rounding toward positive, a nonoverflowing square root of a nonnegative rational is finite and
at least the real square root. -/
theorem le_sqrtMagnitude_up (f : Format) {x : ℚ} (hx : 0 ≤ x)
    (preferred : Int)
    (hfinite : (sqrtMagnitude f .up x preferred).status.overflow = false) :
    ∃ value : ℚ, (sqrtMagnitude f .up x preferred).value.toRat? = some value ∧
      Real.sqrt (x : ℝ) ≤ (value : ℝ) := by
  obtain ⟨value, hv, he⟩ := sqrtMagnitude_value_sub_sqrt f .up x preferred hfinite
  refine ⟨value, hv, ?_⟩
  have hu : 0 < (10 : ℝ) ^ sqrtQuantum f x := zpow_pos (by norm_num) _
  have h := le_sqrtRound_up
    (div_nonneg hx (zpow_pos (by norm_num : (0 : ℚ) < 10) (2 * sqrtQuantum f x)).le)
  have hs := mul_nonneg (sub_nonneg.mpr h) hu.le
  rw [← he] at hs
  linarith

/-- Rounding toward zero or toward negative, a square root of a nonnegative rational is finite and
at most the real square root, and the two modes agree because the root is nonnegative. An overflow
delivers the greatest finite datum, which lies below the root. -/
theorem sqrtMagnitude_directed_le (f : Format) (mode : RoundingMode)
    (hm : mode = .towardZero ∨ mode = .down) {x : ℚ} (hx : 0 ≤ x)
    (preferred : Int) :
    ∃ value : ℚ, (sqrtMagnitude f mode x preferred).value.toRat? = some value ∧
      (value : ℝ) ≤ Real.sqrt (x : ℝ) := by
  cases hfinite : (sqrtMagnitude f mode x preferred).status.overflow
  swap
  · have hq := (sqrtMagnitude_overflow_iff f mode x preferred).mp hfinite
    have hinf : mode.overflowToInfinity false = false := by
      rcases hm with rfl | rfl <;> rfl
    refine ⟨((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum, ?_, ?_⟩
    · simp [sqrtMagnitude, hq, hinf, Format.maxFinite, Datum.toRat?_eq]
    · rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat]
      exact (maxFinite_lt_sqrt_of_overflow f mode hx hq).le
  obtain ⟨value, hv, he⟩ := sqrtMagnitude_value_sub_sqrt f mode x preferred hfinite
  refine ⟨value, hv, ?_⟩
  have hu : 0 < (10 : ℝ) ^ sqrtQuantum f x := zpow_pos (by norm_num) _
  have hx' : 0 ≤ x / (10 : ℚ) ^ (2 * sqrtQuantum f x) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have h : (mode.sqrtRound (x / (10 : ℚ) ^ (2 * sqrtQuantum f x)) : ℝ) ≤
      Real.sqrt ((x / (10 : ℚ) ^ (2 * sqrtQuantum f x) : ℚ) : ℝ) := by
    rcases hm with rfl | rfl
    · exact sqrtRound_towardZero_le hx'
    · exact sqrtRound_down_le hx'
  have hs := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hu.le
  rw [← he] at hs
  linarith

/-- In every rounding direction, a nonoverflowing square root of a nonnegative rational is finite
and less than one grid unit from the real square root. -/
theorem sqrtMagnitude_error_lt_one (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = false) :
    ∃ value : ℚ, (sqrtMagnitude f mode x preferred).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt (x : ℝ)| < (10 : ℝ) ^ sqrtQuantum f x := by
  obtain ⟨value, hv, he⟩ := sqrtMagnitude_value_sub_sqrt f mode x preferred hfinite
  refine ⟨value, hv, ?_⟩
  have hu : 0 < (10 : ℝ) ^ sqrtQuantum f x := zpow_pos (by norm_num) _
  have h := sqrtRound_error_lt_one mode
    (div_nonneg hx (zpow_pos (by norm_num : (0 : ℚ) < 10) (2 * sqrtQuantum f x)).le)
  rw [he, abs_mul, abs_of_pos hu]
  exact (mul_lt_mul_of_pos_right h hu).trans_eq (one_mul _)

/-- Underflow compares the exact mathematical root with the least normal magnitude, and an
overflowing root is never tiny. -/
theorem sqrtMagnitude_underflow_iff (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int) :
    (sqrtMagnitude f mode x preferred).status.underflow = true ↔
      Real.sqrt (x : ℝ) < (f.minNormal : ℝ) ∧
        (sqrtMagnitude f mode x preferred).status.inexact = true := by
  by_cases hq : (sqrtPair f mode x).2 ≤ f.maxQuantum
  swap
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_sqrt_of_overflow f mode hx hq'
    have hmin : ((f.minNormal : ℚ) : ℝ) ≤
        ((f.coefficientBound - 1 : Nat) : ℝ) * (10 : ℝ) ^ f.maxQuantum := by
      simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr f.minNormal_le_maxFinite
    simp only [sqrtMagnitude, hq', ↓reduceIte, Bool.false_eq_true, false_iff, not_and]
    exact fun h => absurd h (not_lt.mpr (hmin.trans hlt.le))
  have hn : (0 : ℚ) < f.minNormal :=
    mul_pos (pow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
  have he : Real.sqrt (x : ℝ) < (f.minNormal : ℝ) ↔ x < f.minNormal ^ 2 := by
    rw [Real.sqrt_lt (by exact_mod_cast hx) (by exact_mod_cast hn.le)]
    exact_mod_cast Iff.rfl
  simp [sqrtMagnitude, not_lt.mpr hq, he]

end FloatLib.Floats.Formats.DecimalInterchange
