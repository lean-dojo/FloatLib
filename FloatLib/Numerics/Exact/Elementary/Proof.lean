/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof

/-!
# Real semantics of exact elementary comparisons

These are total comparisons with the mathematical exponential and natural logarithm.
They include equality: `exp 0 = 1` and `log 1 = 0` are handled exactly before refinement.
-/

public section

namespace FloatLib.Numerics.ElementaryComparison

/-- The executable logarithm comparison agrees with the real ordering. -/
theorem compareLog_eq_real (argument boundary : ℚ) (hpositive : 0 < argument) :
    compareLog argument boundary hpositive =
      cmp (Real.log (argument : ℝ)) (boundary : ℝ) := by
  by_cases hone : argument = 1
  · subst argument
    simp [compareLog, cmp, cmpUsing]
  · rw [compareLog, dite_eq_right hone]
    dsimp only
    let bits := boundary.den.log2 + 32
    have hcontains := Enclosure.BinaryGrid.contains_log argument bits
      (Enclosure.BinaryGrid.logPrecision bits argument bits) hpositive
    split
    · rename_i hlt
      have hreal : Real.log (argument : ℝ) < (boundary : ℝ) :=
        hcontains.2.trans_lt (by exact_mod_cast hlt)
      simp [cmp, cmpUsing, hreal]
    · split
      · rename_i hgt
        have hreal : (boundary : ℝ) < Real.log (argument : ℝ) :=
          (show (boundary : ℝ) < _ by exact_mod_cast hgt).trans_le hcontains.1
        simp [cmp, cmpUsing, hreal, not_lt_of_ge hreal.le]
      · exact Enclosure.Comparison.compare_eq_real _ _ _ _
          (fun n => Enclosure.contains_log argument (2 ^ n) hpositive)

/-- The executable exponential comparison agrees with the real ordering. -/
theorem compareExp_eq_real (argument boundary : ℚ) :
    compareExp argument boundary = cmp (Real.exp (argument : ℝ)) (boundary : ℝ) := by
  unfold compareExp
  split
  · rename_i hpositive
    have hreal : (0 : ℝ) < boundary := by exact_mod_cast hpositive
    rw [compareLog_eq_real, cmp_swap]
    simp only [cmp, cmpUsing, Real.lt_log_iff_exp_lt hreal,
      Real.log_lt_iff_lt_exp hreal]
  · rename_i hnonpositive
    have hreal : (boundary : ℝ) < Real.exp (argument : ℝ) :=
      (show (boundary : ℝ) ≤ 0 by exact_mod_cast le_of_not_gt hnonpositive).trans_lt
        (Real.exp_pos _)
    simp [cmp, cmpUsing, hreal, not_lt_of_ge hreal.le]

/-- Sharing logarithm enclosures preserves the exact real comparison. -/
theorem prepareLog_eq_real (argument : ℚ) (levels : Nat) (hpositive : 0 < argument)
    (boundary : ℚ) :
    (prepareLog argument levels hpositive).compare boundary =
      cmp (Real.log (argument : ℝ)) (boundary : ℝ) := by
  by_cases hone : argument = 1
  · subst argument
    simp [prepareLog, Enclosure.Comparison.Prepared.compare, cmp, cmpUsing]
  · rw [prepareLog, dite_eq_right hone, Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simp only [Enclosure.Comparison.cacheIntervals_apply]
    exact Enclosure.contains_log argument (2 ^ n) hpositive

/-- Both prepared exponential algorithms implement the same exact real comparison. -/
theorem prepareExp_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareExp argument levels).compare boundary =
      cmp (Real.exp (argument : ℝ)) (boundary : ℝ) := by
  by_cases hzero : argument = 0
  · subst argument
    have hlt : (1 : ℝ) < boundary ↔ (1 : ℚ) < boundary := by exact_mod_cast Iff.rfl
    have hgt : (boundary : ℝ) < 1 ↔ boundary < (1 : ℚ) := by exact_mod_cast Iff.rfl
    simp [prepareExp, Enclosure.Comparison.Prepared.compare, cmp, cmpUsing, hlt, hgt]
  · rw [prepareExp, dite_eq_right hzero]
    split
    · rw [Enclosure.Comparison.Prepared.compare]
      apply Enclosure.Comparison.compare_eq_real
      intro n
      simp only [Enclosure.Comparison.cacheIntervals_apply]
      exact Enclosure.contains_exp argument (2 ^ n)
    · exact compareExp_eq_real argument boundary

end FloatLib.Numerics.ElementaryComparison
