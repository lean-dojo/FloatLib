/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Exact

/-!
# Signed projection guarantees

The error bounds concern the actual rational value of the returned datum and assume that the
returned overflow flag is false. The underflow law holds for every input. The inexact law holds
whenever the returned datum has a rational value, saturation to the greatest finite datum included;
an overflow to infinity has none, and `project_inexact_of_overflow` shows that every overflow is
inexact. Directed bounds and midpoint decisions come from the integer-grid rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Projection raises overflow exactly when the precision-rounded quantum exceeds the format's
largest quantum; overflow is tested after rounding. -/
theorem projectMagnitude_overflow_iff (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (preferred : Int) :
    (projectMagnitude f mode s x preferred).status.overflow = true ↔
      f.maxQuantum < (roundedPair f mode s x).2 := by
  by_cases h : f.maxQuantum < (roundedPair f mode s x).2 <;>
    simp [projectMagnitude_eq, h]

/-- Without overflow, the quantum of the rounded pair behind a projection is at most the format's
largest quantum. -/
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

/-- In every rounding direction without overflow, projecting a magnitude with either sign gives a
finite datum less than one grid unit from the signed exact value. -/
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
    (hm : mode = .nearest ∨ mode = .nearestAway)
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

/-- The inexact flag detects a change in numerical value. An overflow to the greatest finite datum
is inexact, since the exact magnitude lies strictly above it. -/
theorem projectMagnitude_inexact_iff (f : Format) (mode : RoundingMode) (s : Bool)
    (x value : ℚ) (preferred : Int)
    (hv : (projectMagnitude f mode s x preferred).value.toRat? = some value) :
    (projectMagnitude f mode s x preferred).status.inexact = true ↔
      value ≠ (if s then -x else x) := by
  by_cases hq : (roundedPair f mode s x).2 ≤ f.maxQuantum
  · have he := projectMagnitude_value f mode s x preferred hq
    rw [hv] at he
    have hv' := Option.some.inj he
    simp only [projectMagnitude_eq, ite_eq_right (not_lt.mpr hq), decide_eq_true_eq]
    rw [hv', roundedPair_value]
    cases s <;> simp
  · have hq' := lt_of_not_ge hq
    have hne : ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum ≠ x := by
      rcases le_or_gt 0 x with hx | hx
      · exact (maxFinite_lt_of_roundedPair_overflow f mode s hx hq').ne
      · exact (lt_of_lt_of_le hx
          (mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le)).ne'
    simp only [projectMagnitude_eq, hq', ↓reduceIte] at hv ⊢
    split at hv
    · simp [Datum.toRat?_eq] at hv
    · simp only [Format.maxFinite, Datum.toRat?_eq, Option.some.injEq] at hv
      subst hv
      cases s <;> simpa [mul_assoc] using hne

/--
Whenever the result has a rational value, inexactness is equivalent to a change in numerical
value. This includes saturation to the greatest finite datum; an overflow to infinity has no
rational value and is covered by `project_inexact_of_overflow`.
-/
theorem project_inexact_iff (f : Format) (mode : RoundingMode)
    (x value : ℚ) (preferred : Int) (negativeZero : Bool)
    (hv : (project f mode x preferred negativeZero).value.toRat? = some value) :
    (project f mode x preferred negativeZero).status.inexact = true ↔ value ≠ x := by
  simpa only [project, signed_abs] using projectMagnitude_inexact_iff f mode
    (if x = 0 then negativeZero else decide (x < 0)) |x| value preferred hv

/-- Every overflow is inexact, whether the result is an infinity or the greatest finite datum. -/
theorem project_inexact_of_overflow (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) (negativeZero : Bool)
    (hoverflow : (project f mode x preferred negativeZero).status.overflow = true) :
    (project f mode x preferred negativeZero).status.inexact = true := by
  by_cases hq : (roundedPair f mode (if x = 0 then negativeZero else decide (x < 0))
      |x|).2 ≤ f.maxQuantum
  · simp [project, projectMagnitude_eq, not_lt.mpr hq] at hoverflow
  · simp [project, projectMagnitude_eq, lt_of_not_ge hq]

/-- Decimal tininess is tested on the exact input, before rounding. An overflowing input is never
tiny, so the law also holds when the result overflows. -/
theorem project_underflow_iff (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) (negativeZero : Bool) :
    (project f mode x preferred negativeZero).status.underflow = true ↔
      |x| < f.minNormal ∧
        (project f mode x preferred negativeZero).status.inexact = true := by
  by_cases hq : (roundedPair f mode (if x = 0 then negativeZero else decide (x < 0))
      |x|).2 ≤ f.maxQuantum
  · simp [project, projectMagnitude_eq, not_lt.mpr hq]
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_of_roundedPair_overflow f mode _ (abs_nonneg x) hq'
    have hmin := f.minNormal_le_maxFinite
    simp only [project, projectMagnitude_eq, hq', ↓reduceIte, Bool.false_eq_true, false_iff,
      not_and]
    exact fun h => absurd h (not_lt.mpr (hmin.trans hlt.le))

end FloatLib.Floats.Formats.DecimalInterchange
