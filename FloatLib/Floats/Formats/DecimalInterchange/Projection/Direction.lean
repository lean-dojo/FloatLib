/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Semantics

/-!
# Directed projection bounds

In the absence of overflow, the returned datum bounds the exact input on the side
prescribed by the rounding direction. Rounding toward zero cannot increase its magnitude.
The bounds include subnormal results and either sign of an exact zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

private theorem signed_div_mul (s : Bool) (x : ℚ) {u : ℚ} (hu : u ≠ 0) :
    (if s then -(x / u) else x / u) * u = if s then -x else x := by
  cases s <;> simp [hu]

private theorem roundSigned_mul (mode : RoundingMode) (s : Bool) (x : ℚ) (q : Int) :
    mode.roundSigned s (x / (10 : ℚ) ^ q) * (10 : ℚ) ^ q =
      (if s then -1 else 1) * (mode.roundAt s x q : ℚ) * (10 : ℚ) ^ q := by
  cases s <;> simp [RoundingMode.roundSigned, RoundingMode.roundAt]

theorem projectMagnitude_towardPositive_le (f : Format) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f .towardPositive s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f .towardPositive s x preferred).value.toRat? = some value ∧
      (if s then -x else x) ≤ value := by
  refine ⟨_, projectMagnitude_value f .towardPositive s x preferred hq, ?_⟩
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
  have h := RoundingMode.le_roundSigned_towardPositive s (div_nonneg hx hu.le)
  have hs := mul_le_mul_of_nonneg_right h hu.le
  rwa [signed_div_mul s x hu.ne', roundSigned_mul] at hs

theorem projectMagnitude_towardNegative_le (f : Format) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f .towardNegative s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f .towardNegative s x preferred).value.toRat? = some value ∧
      value ≤ (if s then -x else x) := by
  refine ⟨_, projectMagnitude_value f .towardNegative s x preferred hq, ?_⟩
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
  have h := RoundingMode.roundSigned_towardNegative_le s (div_nonneg hx hu.le)
  have hs := mul_le_mul_of_nonneg_right h hu.le
  rwa [signed_div_mul s x hu.ne', roundSigned_mul] at hs

/-- An upward-rounded finite datum is an upper bound on the exact rational input. -/
theorem le_project_towardPositive (f : Format) (x : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hfinite : (project f .towardPositive x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f .towardPositive x preferred negativeZero).value.toRat? = some value ∧
      x ≤ value := by
  have hq := project_quantum_le_of_no_overflow f .towardPositive x preferred negativeZero
    hfinite
  simpa only [project, signed_abs] using projectMagnitude_towardPositive_le f
    (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) preferred hq

/-- A downward-rounded finite datum is a lower bound on the exact rational input. -/
theorem project_towardNegative_le (f : Format) (x : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hfinite : (project f .towardNegative x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f .towardNegative x preferred negativeZero).value.toRat? = some value ∧
      value ≤ x := by
  have hq := project_quantum_le_of_no_overflow f .towardNegative x preferred negativeZero
    hfinite
  simpa only [project, signed_abs] using projectMagnitude_towardNegative_le f
    (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) preferred hq

/-- Rounding toward zero cannot increase a finite result's magnitude. -/
theorem abs_project_towardZero_le (f : Format) (x : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hfinite : (project f .towardZero x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f .towardZero x preferred negativeZero).value.toRat? = some value ∧
      |value| ≤ |x| := by
  let s := if x = 0 then negativeZero else decide (x < 0)
  have hq := project_quantum_le_of_no_overflow f .towardZero x preferred negativeZero
    hfinite
  refine ⟨_, projectMagnitude_value f .towardZero s |x| preferred hq, ?_⟩
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f |x| := zpow_pos (by norm_num) _
  have h := RoundingMode.roundMagnitude_towardZero_le s (div_nonneg (abs_nonneg x) hu.le)
  have hs := mul_le_mul_of_nonneg_right h hu.le
  rw [div_mul_cancel₀ _ hu.ne'] at hs
  have habs : |(if s then (-1 : ℚ) else 1)| = 1 := by cases s <;> norm_num
  have hc : (0 : ℚ) ≤ RoundingMode.towardZero.roundMagnitude s
      (|x| / (10 : ℚ) ^ roundingQuantum f |x|) := Nat.cast_nonneg _
  simpa only [RoundingMode.roundAt, abs_mul, habs, one_mul,
    abs_of_nonneg hc, abs_of_pos hu] using hs

end FloatLib.Floats.Formats.DecimalInterchange
