/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Exact

/-!
# Signed projection guarantees

The error bounds concern the actual rational value of the returned datum.
The bounds assume that the returned overflow flag is false. Directed bounds and
midpoint decisions come from the integer-grid rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem projectMagnitude_overflow_iff (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (preferred : Int) :
    (projectMagnitude f mode s x preferred).status.overflow = true ↔
      f.maxQuantum < (roundedPair f mode s x).2 := by
  by_cases h : f.maxQuantum < (roundedPair f mode s x).2 <;>
    simp [projectMagnitude_eq, h]

theorem project_quantum_le_of_no_overflow (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) (negativeZero : Bool)
    (hfinite : (project f mode x preferred negativeZero).status.overflow = false) :
    (roundedPair f mode (if x = 0 then negativeZero else decide (x < 0))
      |x|).2 ≤ f.maxQuantum := by
  apply le_of_not_gt
  intro h
  have ht := (projectMagnitude_overflow_iff f mode _ |x| preferred).mpr h
  change (project f mode x preferred negativeZero).status.overflow = true at ht
  simp [hfinite] at ht

theorem projectMagnitude_error_lt_one (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f mode s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f mode s x preferred).value.toRat? = some value ∧
      |value - (if s then -x else x)| < (10 : ℚ) ^ roundingQuantum f x := by
  refine ⟨_, projectMagnitude_value f mode s x preferred hq, ?_⟩
  have h := mode.roundAt_error_lt_one s hx (roundingQuantum f x)
  cases s <;> simpa [neg_add_eq_sub, abs_sub_comm] using h

/-- Reconstruct a rational from its magnitude and the sign used by `project`. -/
theorem signed_abs (x : ℚ) (negativeZero : Bool) :
    (if (if x = 0 then negativeZero else decide (x < 0)) then -|x| else |x|) = x := by
  by_cases hz : x = 0
  · simp [hz]
  · by_cases hn : x < 0
    · simp [hz, hn, abs_of_neg hn]
    · simp [hz, hn, abs_of_nonneg (le_of_not_gt hn)]

/-- Both nearest modes have at most half a unit of error on the selected decimal grid. -/
theorem project_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : ℚ) (preferred : Int) (negativeZero : Bool)
    (hfinite : (project f mode x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f mode x preferred negativeZero).value.toRat? = some value ∧
      |value - x| ≤ (10 : ℚ) ^ roundingQuantum f |x| / 2 := by
  have hq := project_quantum_le_of_no_overflow f mode x preferred negativeZero hfinite
  simpa only [project, signed_abs] using
    projectMagnitude_error_le_half f mode hm
      (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) preferred hq

/-- In every rounding direction, a nonoverflowing result is less than one grid unit away. -/
theorem project_error_lt_one (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) (negativeZero : Bool)
    (hfinite : (project f mode x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f mode x preferred negativeZero).value.toRat? = some value ∧
      |value - x| < (10 : ℚ) ^ roundingQuantum f |x| := by
  have hq := project_quantum_le_of_no_overflow f mode x preferred negativeZero hfinite
  simpa only [project, signed_abs] using
    projectMagnitude_error_lt_one f mode
      (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) preferred hq

/-- Without overflow, the inexact flag detects a change in numerical value. -/
theorem projectMagnitude_inexact_iff (f : Format) (mode : RoundingMode) (s : Bool)
    (x value : ℚ) (preferred : Int)
    (hq : (roundedPair f mode s x).2 ≤ f.maxQuantum)
    (hv : (projectMagnitude f mode s x preferred).value.toRat? = some value) :
    (projectMagnitude f mode s x preferred).status.inexact = true ↔
      value ≠ (if s then -x else x) := by
  have he := projectMagnitude_value f mode s x preferred hq
  rw [hv] at he
  have hv' := Option.some.inj he
  simp only [projectMagnitude_eq, ite_eq_right (not_lt.mpr hq), decide_eq_true_eq]
  rw [hv', roundedPair_value]
  cases s <;> simp

/-- Without overflow, inexactness is equivalent to a change in numerical value. -/
theorem project_inexact_iff (f : Format) (mode : RoundingMode)
    (x value : ℚ) (preferred : Int) (negativeZero : Bool)
    (hfinite : (project f mode x preferred negativeZero).status.overflow = false)
    (hv : (project f mode x preferred negativeZero).value.toRat? = some value) :
    (project f mode x preferred negativeZero).status.inexact = true ↔ value ≠ x := by
  have hq := project_quantum_le_of_no_overflow f mode x preferred negativeZero hfinite
  simpa only [project, signed_abs] using projectMagnitude_inexact_iff f mode
    (if x = 0 then negativeZero else decide (x < 0)) |x| value preferred hq hv

/-- Decimal tininess is tested on the exact input, before rounding. -/
theorem project_underflow_iff (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) (negativeZero : Bool)
    (hfinite : (project f mode x preferred negativeZero).status.overflow = false) :
    (project f mode x preferred negativeZero).status.underflow = true ↔
      |x| < f.minNormal ∧
        (project f mode x preferred negativeZero).status.inexact = true := by
  have hq := project_quantum_le_of_no_overflow f mode x preferred negativeZero hfinite
  simp [project, projectMagnitude_eq, not_lt.mpr hq]

end FloatLib.Floats.Formats.DecimalInterchange
