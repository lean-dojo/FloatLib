/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.Runtime
import FloatLib.Numerics.Order.Comparison
import Mathlib.Tactic.Linarith

/-!
# Exact real semantics of ordinary trigonometric comparisons

Every direct comparator returns the ordering of the exact real function value and rational
boundary. The inverse sine and cosine contracts require an argument in `[-1, 1]` and use
their usual principal branches. Exact rational values are included: sine, tangent, and
arctangent at zero; cosine at zero; inverse sine at zero; and inverse cosine at one.

Prepared and uncached comparators satisfy the same contracts at every cache size.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- Sharing sine enclosures preserves the exact real ordering. -/
theorem prepareSin_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareSin argument levels).compare boundary =
      cmp (Real.sin (argument : ℝ)) (boundary : ℝ) := by
  by_cases hzero : argument = 0
  · subst argument
    simp [prepareSin, Enclosure.Comparison.Prepared.compare, cmp, cmpUsing]
  · rw [prepareSin, dif_neg hzero]
    dsimp only [Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simp only [Enclosure.Comparison.cacheIntervals_apply]
    exact Enclosure.contains_sinReduced argument (2 ^ n)

/-- Sharing cosine enclosures preserves the exact real ordering, including `cos 0 = 1`. -/
theorem prepareCos_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareCos argument levels).compare boundary =
      cmp (Real.cos (argument : ℝ)) (boundary : ℝ) := by
  by_cases hzero : argument = 0
  · subst argument
    have hlt : (1 : ℝ) < boundary ↔ (1 : ℚ) < boundary := by exact_mod_cast Iff.rfl
    have hgt : (boundary : ℝ) < 1 ↔ boundary < (1 : ℚ) := by exact_mod_cast Iff.rfl
    simp [prepareCos, Enclosure.Comparison.Prepared.compare, cmp, cmpUsing, hlt, hgt]
  · rw [prepareCos, dif_neg hzero]
    dsimp only [Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simp only [Enclosure.Comparison.cacheIntervals_apply]
    exact Enclosure.contains_cosReduced argument (2 ^ n)

/-- Sharing arctangent enclosures preserves the exact real ordering. -/
theorem prepareArctan_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareArctan argument levels).compare boundary =
      cmp (Real.arctan (argument : ℝ)) (boundary : ℝ) := by
  by_cases hzero : argument = 0
  · subst argument
    simp [prepareArctan, Enclosure.Comparison.Prepared.compare, cmp, cmpUsing]
  · rw [prepareArctan, dif_neg hzero]
    dsimp only [Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simp only [Enclosure.Comparison.cacheIntervals_apply]
    exact Enclosure.contains_atan argument (2 ^ n)

/-- Sine comparison is total and agrees with the real ordering. -/
theorem compareSin_eq_real (argument boundary : ℚ) :
    compareSin argument boundary = cmp (Real.sin (argument : ℝ)) (boundary : ℝ) :=
  prepareSin_eq_real argument 0 boundary

/-- Cosine comparison is total and agrees with the real ordering. -/
theorem compareCos_eq_real (argument boundary : ℚ) :
    compareCos argument boundary = cmp (Real.cos (argument : ℝ)) (boundary : ℝ) :=
  prepareCos_eq_real argument 0 boundary

/-- Arctangent comparison is total and agrees with the real ordering. -/
theorem compareArctan_eq_real (argument boundary : ℚ) :
    compareArctan argument boundary = cmp (Real.arctan (argument : ℝ)) (boundary : ℝ) :=
  prepareArctan_eq_real argument 0 boundary

/-- The cosine sign and the residual sign determine the exact tangent ordering. -/
theorem prepareTan_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareTan argument levels).compare boundary = cmp (Real.tan (argument : ℝ)) (boundary : ℝ) := by
  by_cases hzero : argument = 0
  · subst argument
    simp [prepareTan, Enclosure.Comparison.Prepared.compare, cmp, cmpUsing]
  · rw [prepareTan, dif_neg hzero]
    dsimp only [Enclosure.Comparison.Prepared.compare]
    have hc := Enclosure.Comparison.compare_eq_real
      (Enclosure.Comparison.cacheIntervals
        (fun n => Enclosure.cosReduced argument (2 ^ n)) levels).get 0
      (by simpa only [Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_cos_separating argument 0 hzero) (Real.cos (argument : ℝ))
      (fun n => by simpa only [Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.contains_cosReduced argument (2 ^ n))
    have hr := Enclosure.Comparison.compare_eq_real
      (fun n => ((Enclosure.Comparison.cacheIntervals
        (fun i => Enclosure.sinReduced argument (2 ^ i)) levels).get n).sub
          (((Enclosure.Comparison.cacheIntervals
            (fun i => Enclosure.cosReduced argument (2 ^ i)) levels).get n).scale boundary)) 0
      (by simpa only [Enclosure.Comparison.cacheIntervals_apply, Enclosure.sinSubCos] using
        Enclosure.exists_sinSubCos_separating argument boundary hzero)
      (Real.sin (argument : ℝ) - (boundary : ℝ) * Real.cos (argument : ℝ))
      (fun n => by simpa only [Enclosure.Comparison.cacheIntervals_apply,
        Enclosure.sinSubCos] using Enclosure.contains_sinSubCos argument boundary (2 ^ n))
    rw [hc, hr, Rat.cast_zero]
    simp only [cmp_eq_gt_iff, Real.tan_eq_sin_div_cos]
    split
    · exact cmp_div_of_pos _ _ _ ‹_›
    · have hnegative : Real.cos (argument : ℝ) < 0 :=
        lt_of_le_of_ne (le_of_not_gt ‹_›) (Enclosure.cos_ratCast_ne_zero argument hzero)
      exact cmp_div_of_neg _ _ _ hnegative

/-- Tangent comparison terminates and agrees with the exact real value at every rational input. -/
theorem compareTan_eq_real (argument boundary : ℚ) :
    compareTan argument boundary = cmp (Real.tan (argument : ℝ)) (boundary : ℝ) :=
  prepareTan_eq_real argument 0 boundary

/-- Inverse sine comparison agrees with its real principal branch throughout `[-1, 1]`. -/
theorem prepareArcsin_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1) :
    (prepareArcsin argument levels).compare boundary =
      cmp (Real.arcsin (argument : ℝ)) (boundary : ℝ) := by
  have ha : (argument : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by exact_mod_cast hlower, by exact_mod_cast hupper⟩
  rw [prepareArcsin, Enclosure.Comparison.Prepared.compare]
  simp only [prepareArctan_eq_real, Rat.cast_one, Real.arctan_one,
    Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, cmp_eq_lt_iff]
  split
  · rename_i hb
    have hlt : Real.arcsin (argument : ℝ) < boundary :=
      (Real.arcsin_le_pi_div_two _).trans_lt (by linarith)
    exact hlt.cmp_eq_lt.symm
  · rename_i hbupper
    split
    · rename_i hb
      have hgt : (boundary : ℝ) < Real.arcsin (argument : ℝ) :=
        (show (boundary : ℝ) < -(Real.pi / 2) by linarith).trans_le
          (Real.neg_pi_div_two_le_arcsin _)
      exact hgt.cmp_eq_gt.symm
    · rename_i hblower
      have hb : (boundary : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [le_of_not_gt hblower], by linarith [le_of_not_gt hbupper]⟩
      rw [compareSin_eq_real, cmp_swap]
      simp only [cmp, cmpUsing, Real.arcsin_lt_iff_lt_sin ha hb,
        Real.lt_arcsin_iff_sin_lt hb ha]

/-- Inverse sine comparison is total on its real domain, including endpoints and exact zero. -/
theorem compareArcsin_eq_real (argument boundary : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1) :
    compareArcsin argument boundary =
      cmp (Real.arcsin (argument : ℝ)) (boundary : ℝ) :=
  prepareArcsin_eq_real argument 0 boundary hlower hupper

/-- Inverse cosine comparison agrees with its decreasing real principal branch on `[-1, 1]`. -/
theorem prepareArccos_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1) :
    (prepareArccos argument levels).compare boundary =
      cmp (Real.arccos (argument : ℝ)) (boundary : ℝ) := by
  have hlo : (-1 : ℝ) ≤ argument := by exact_mod_cast hlower
  have hhi : (argument : ℝ) ≤ 1 := by exact_mod_cast hupper
  rw [prepareArccos, Enclosure.Comparison.Prepared.compare]
  simp only [prepareArctan_eq_real, Rat.cast_one, Real.arctan_one,
    Rat.cast_div, Rat.cast_ofNat, cmp_eq_lt_iff]
  split
  · rename_i hb
    have hgt : (boundary : ℝ) < Real.arccos (argument : ℝ) :=
      (show (boundary : ℝ) < 0 by exact_mod_cast hb).trans_le (Real.arccos_nonneg _)
    exact hgt.cmp_eq_gt.symm
  · rename_i hbzero
    split
    · rename_i hb
      have hlt : Real.arccos (argument : ℝ) < boundary :=
        (Real.arccos_le_pi _).trans_lt (by linarith)
      exact hlt.cmp_eq_lt.symm
    · rename_i hbpi
      have hb : (boundary : ℝ) ∈ Set.Icc 0 Real.pi :=
        ⟨by exact_mod_cast le_of_not_gt hbzero, by linarith [le_of_not_gt hbpi]⟩
      have ha : Real.arccos (argument : ℝ) ∈ Set.Icc 0 Real.pi :=
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      have hlt : Real.cos (boundary : ℝ) < argument ↔
          Real.arccos (argument : ℝ) < boundary := by
        simpa only [Real.cos_arccos hlo hhi] using
          Real.strictAntiOn_cos.lt_iff_gt hb ha
      have hgt : (argument : ℝ) < Real.cos (boundary : ℝ) ↔
          (boundary : ℝ) < Real.arccos (argument : ℝ) := by
        simpa only [Real.cos_arccos hlo hhi] using
          Real.strictAntiOn_cos.lt_iff_gt ha hb
      rw [compareCos_eq_real]
      simp only [cmp, cmpUsing, hlt, hgt]

/-- Inverse cosine comparison is total on its real domain, including the exact value at one. -/
theorem compareArccos_eq_real (argument boundary : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1) :
    compareArccos argument boundary =
      cmp (Real.arccos (argument : ℝ)) (boundary : ℝ) :=
  prepareArccos_eq_real argument 0 boundary hlower hupper

end FloatLib.Numerics.TrigonometricComparison
