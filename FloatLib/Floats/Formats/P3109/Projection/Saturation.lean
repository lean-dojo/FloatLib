/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.P3109.Projection.Range
import Mathlib.Tactic.CasesM

/-!
# Saturation respects finite numerical equality

P3109 Interim Report v4.1, §4.7.5 (unapproved draft).
The sign-split implementation is the rational interval test, including
either zero sign. Thus normalization of a finite dyadic representation
cannot change its saturated datum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Format

open FloatLib.Numerics

/-- P3109 datum equality composes numerical finite equality and the two nonfinite classes.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1 and 4.7.2–4.7.6.
-/
theorem SameDatum.trans {left middle right : NumericalValue Numerics.Dyadic}
    (hleft : SameDatum left middle) (hright : SameDatum middle right) :
    SameDatum left right := by
  cases left <;> cases middle <;> cases right
  all_goals try cases_type* ExceptionalValue
  all_goals simp_all [SameDatum]

/-- P3109 interim report v4.1, §4.7.5: finite saturation uses the two rational range comparisons. -/
theorem saturate_finite_eq_range (format : Format) (mode : SaturationMode)
    (rounding : RoundingMode) (value : Numerics.Dyadic) :
    format.saturate mode rounding (.finite value) =
      if value.toRat < format.minFinite.toRat then Internal.saturateBelow format mode rounding
      else if format.maxFinite.toRat < value.toRat then
        Internal.saturateAbove format mode rounding
      else .finite value := by
  have hmin : format.minFinite.toRat ≤ 0 := by
    cases hs : format.signedness with
    | signed =>
        rw [minFinite, hs, Numerics.Dyadic.neg_toRat]
        exact neg_nonpos.mpr format.maxFinite_toRat_pos.le
    | unsigned => simp [minFinite, hs]
  have hsign :
      (value.negative = false → 0 ≤ value.toRat) ∧
      (value.negative = true → value.toRat ≤ 0) := by
    by_cases hz : value.significand = 0
    · simp [(Numerics.Dyadic.toRat_eq_zero_iff value).mpr hz]
    · exact ⟨fun h => (Numerics.Dyadic.toRat_pos_of_significand_ne_zero value hz h).le,
        fun h => (Numerics.Dyadic.toRat_neg_of_significand_ne_zero value hz h).le⟩
  cases hs : value.negative
  · have hlo := not_lt_of_ge (hmin.trans (hsign.1 hs))
    simp [saturate, hs, Numerics.Dyadic.Internal.compareScalable_eq_compare,
      Numerics.Dyadic.compare_eq_lt_iff, hlo]
  · have hhi := not_lt_of_ge ((hsign.2 hs).trans format.maxFinite_toRat_pos.le)
    simp [saturate, hs, Numerics.Dyadic.Internal.compareScalable_eq_compare,
      Numerics.Dyadic.compare_eq_lt_iff, hhi]

/-- P3109 interim report v4.1, §4.7.5: two equal finite values saturate to the same datum,
    including signed zero. -/
theorem sameDatum_saturate_finite (format : Format) (mode : SaturationMode)
    (rounding : RoundingMode) {left right : Numerics.Dyadic} (h : left.toRat = right.toRat) :
    SameDatum (format.saturate mode rounding (.finite left))
      (format.saturate mode rounding (.finite right)) := by
  rw [saturate_finite_eq_range, saturate_finite_eq_range, h]
  split_ifs
  · cases mode <;> cases rounding <;>
      cases hs : format.signedness <;> cases hd : format.domain <;>
      simp [Internal.saturateBelow, hs, hd, SameDatum]
  · cases mode <;> cases rounding <;> cases hd : format.domain <;>
      simp [Internal.saturateAbove, hd, SameDatum]
  · exact h

end FloatLib.Floats.Formats.P3109.Format
