/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Hyperbolic.Runtime
public import FloatLib.Numerics.Exact.Elementary.Proof
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Real semantics of hyperbolic comparisons

Each comparator returns the exact real ordering, including equality at rational special
values. The inverse identities are used only on the appropriate real domains.
-/

public section

namespace FloatLib.Numerics.HyperbolicComparison

/-- Doubling the boundary gives the exact ordering of the inverse hyperbolic tangent. -/
theorem compareArtanh_eq_real (argument boundary : ℚ)
    (hlower : -1 < argument) (hupper : argument < 1) :
    compareArtanh argument boundary hlower hupper =
      cmp (Real.artanh (argument : ℝ)) (boundary : ℝ) := by
  have hlo : (-1 : ℝ) < argument := by exact_mod_cast hlower
  have hhi : (argument : ℝ) < 1 := by exact_mod_cast hupper
  have hformula := Real.artanh_eq_half_log ⟨hlo.le, hhi.le⟩
  rw [compareArtanh, ElementaryComparison.compareLog_eq_real]
  push_cast
  have hlt : Real.log ((1 + (argument : ℝ)) / (1 - (argument : ℝ))) < 2 * boundary ↔
      Real.artanh (argument : ℝ) < boundary := by constructor <;> intro h <;> linarith
  have hgt : 2 * (boundary : ℝ) < Real.log ((1 + argument) / (1 - argument)) ↔
      (boundary : ℝ) < Real.artanh argument := by constructor <;> intro h <;> linarith
  simp only [cmp, cmpUsing, hlt, hgt]

/-- Inverting the comparison on `(-1, 1)` gives the exact hyperbolic tangent ordering. -/
theorem compareTanh_eq_real (argument boundary : ℚ) :
    compareTanh argument boundary = cmp (Real.tanh (argument : ℝ)) (boundary : ℝ) := by
  unfold compareTanh
  split
  · rename_i hlower
    split
    · rename_i hupper
      have hb : (boundary : ℝ) ∈ Set.Ioo (-1) 1 := by
        constructor <;> exact_mod_cast ‹_›
      have ht : Real.tanh (argument : ℝ) ∈ Set.Ioo (-1) 1 :=
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
      rw [compareArtanh_eq_real, cmp_swap, ← Real.artanh_tanh (argument : ℝ)]
      simp only [cmp, cmpUsing, Real.artanh_lt_artanh_iff ht hb,
        Real.artanh_lt_artanh_iff hb ht, Real.tanh_artanh ht]
    · have hlt : Real.tanh (argument : ℝ) < boundary :=
        (Real.tanh_lt_one _).trans_le (by exact_mod_cast le_of_not_gt ‹_›)
      simp [cmp, cmpUsing, hlt]
  · have hgt : (boundary : ℝ) < Real.tanh (argument : ℝ) :=
      (show (boundary : ℝ) ≤ -1 by exact_mod_cast le_of_not_gt ‹_›).trans_lt
        (Real.neg_one_lt_tanh _)
    simp [cmp, cmpUsing, hgt, not_lt_of_ge hgt.le]

/-- The logarithmic preliminary bound and the adaptive hyperbolic sine comparison are both exact. -/
theorem compareSinhPositive_eq_real (argument boundary : ℚ) (hpositive : 0 < argument) :
    compareSinhPositive argument boundary hpositive =
      cmp (Real.sinh (argument : ℝ)) (boundary : ℝ) := by
  have hx : (0 : ℝ) < argument := by exact_mod_cast hpositive
  unfold compareSinhPositive
  split
  · have hgt : (boundary : ℝ) < Real.sinh (argument : ℝ) :=
      (show (boundary : ℝ) ≤ 0 by exact_mod_cast ‹_›).trans_lt
        (Real.sinh_pos_iff.mpr hx)
    simp [cmp, cmpUsing, hgt, not_lt_of_ge hgt.le]
  · split
    · split
      · exact Enclosure.Comparison.compare_eq_real _ _ _ _
          (fun n => Enclosure.contains_sinh argument (2 ^ n))
      · rename_i hfast
        rw [ElementaryComparison.compareExp_eq_real, cmp_eq_gt_iff] at hfast
        push_cast at hfast
        have hlt : Real.sinh (argument : ℝ) < boundary := by
          rw [Real.sinh_eq]
          linarith [le_of_not_gt hfast, Real.exp_pos (-(argument : ℝ))]
        simp [cmp, cmpUsing, hlt]
    · rename_i hfast
      rw [ElementaryComparison.compareExp_eq_real, cmp_eq_lt_iff] at hfast
      push_cast at hfast
      have hsmall : Real.exp (-(argument : ℝ)) < 1 :=
        Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
      have hgt : (boundary : ℝ) < Real.sinh (argument : ℝ) := by
        rw [Real.sinh_eq]
        linarith [le_of_not_gt hfast]
      simp [cmp, cmpUsing, hgt, not_lt_of_ge hgt.le]

/-- Odd reflection and the exact zero case preserve the full hyperbolic sine ordering. -/
theorem compareSinh_eq_real (argument boundary : ℚ) :
    compareSinh argument boundary = cmp (Real.sinh (argument : ℝ)) (boundary : ℝ) := by
  unfold compareSinh
  split
  · exact compareSinhPositive_eq_real argument boundary ‹_›
  · split
    · rw [compareSinhPositive_eq_real, Rat.cast_neg, Rat.cast_neg, Real.sinh_neg, cmp_swap]
      simp only [cmp, cmpUsing, neg_lt_neg_iff]
    · have hz : argument = 0 := le_antisymm (le_of_not_gt ‹_›) (le_of_not_gt ‹_›)
      subst argument
      simp [cmp, cmpUsing]

/-- The logarithmic preliminary bound and the adaptive hyperbolic cosine comparison are both exact. -/
theorem compareCoshPositive_eq_real (argument boundary : ℚ) (hpositive : 0 < argument) :
    compareCoshPositive argument boundary hpositive =
      cmp (Real.cosh (argument : ℝ)) (boundary : ℝ) := by
  have hx : (0 : ℝ) < argument := by exact_mod_cast hpositive
  unfold compareCoshPositive
  split
  · have hgt : (boundary : ℝ) < Real.cosh (argument : ℝ) :=
      (show (boundary : ℝ) ≤ 1 by exact_mod_cast ‹_›).trans_lt
        (Real.one_lt_cosh.mpr (ne_of_gt hx))
    simp [cmp, cmpUsing, hgt, not_lt_of_ge hgt.le]
  · split
    · split
      · exact Enclosure.Comparison.compare_eq_real _ _ _ _
          (fun n => Enclosure.contains_cosh argument (2 ^ n))
      · rename_i hfast
        rw [ElementaryComparison.compareExp_eq_real, cmp_eq_gt_iff] at hfast
        push_cast at hfast
        have hsmall : Real.exp (-(argument : ℝ)) < 1 :=
          Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
        have hlt : Real.cosh (argument : ℝ) < boundary := by
          rw [Real.cosh_eq]
          linarith [le_of_not_gt hfast]
        simp [cmp, cmpUsing, hlt]
    · rename_i hfast
      rw [ElementaryComparison.compareExp_eq_real, cmp_eq_lt_iff] at hfast
      push_cast at hfast
      have hgt : (boundary : ℝ) < Real.cosh (argument : ℝ) := by
        rw [Real.cosh_eq]
        linarith [le_of_not_gt hfast, Real.exp_pos (-(argument : ℝ))]
      simp [cmp, cmpUsing, hgt, not_lt_of_ge hgt.le]

/-- Even reflection and the exact zero case preserve the full hyperbolic cosine ordering. -/
theorem compareCosh_eq_real (argument boundary : ℚ) :
    compareCosh argument boundary = cmp (Real.cosh (argument : ℝ)) (boundary : ℝ) := by
  unfold compareCosh
  split
  · subst argument
    rw [Rat.cast_zero, Real.cosh_zero]
    have hlt : (1 : ℝ) < boundary ↔ (1 : ℚ) < boundary := by exact_mod_cast Iff.rfl
    have hgt : (boundary : ℝ) < 1 ↔ boundary < (1 : ℚ) := by exact_mod_cast Iff.rfl
    simp only [cmp, cmpUsing, hlt, hgt]
  · rw [compareCoshPositive_eq_real, Rat.cast_abs, Real.cosh_abs]

/-- Inverse hyperbolic sine comparison agrees with its exact real ordering. -/
theorem compareArsinh_eq_real (argument boundary : ℚ) :
    compareArsinh argument boundary = cmp (Real.arsinh (argument : ℝ)) (boundary : ℝ) := by
  rw [compareArsinh, compareSinh_eq_real, cmp_swap,
    ← Real.sinh_arsinh (argument : ℝ)]
  simp only [cmp, cmpUsing, Real.sinh_lt_sinh, Real.arsinh_sinh]

/-- Inverse hyperbolic cosine comparison uses the nonnegative branch on `[1, ∞)`. -/
theorem compareArcosh_eq_real (argument boundary : ℚ) (hargument : 1 ≤ argument) :
    compareArcosh argument boundary = cmp (Real.arcosh (argument : ℝ)) (boundary : ℝ) := by
  have ha : (1 : ℝ) ≤ argument := by exact_mod_cast hargument
  have hn := Real.arcosh_nonneg ha
  unfold compareArcosh
  split
  · have hb : (boundary : ℝ) < 0 := by exact_mod_cast ‹_›
    have hgt := hb.trans_le hn
    simp [cmp, cmpUsing, hgt, not_lt_of_ge hgt.le]
  · have hb : (0 : ℝ) ≤ boundary := by exact_mod_cast le_of_not_gt ‹_›
    have hlt : (argument : ℝ) < Real.cosh (boundary : ℝ) ↔
        Real.arcosh (argument : ℝ) < boundary := by
      rw [← Real.cosh_arcosh ha, Real.cosh_lt_cosh, abs_of_nonneg hn, abs_of_nonneg hb,
        Real.arcosh_cosh hn]
    have hgt : Real.cosh (boundary : ℝ) < argument ↔
        (boundary : ℝ) < Real.arcosh (argument : ℝ) := by
      rw [← Real.cosh_arcosh ha, Real.cosh_lt_cosh, abs_of_nonneg hn, abs_of_nonneg hb,
        Real.arcosh_cosh hn]
    rw [compareCosh_eq_real, cmp_swap]
    simp only [cmp, cmpUsing, hlt, hgt]

private theorem prepareLog_swap (argument boundary : ℚ) (levels : Nat)
    (hpositive : 0 < argument) :
    ((ElementaryComparison.prepareLog argument levels hpositive).compare boundary).swap =
      ElementaryComparison.compareExp boundary argument := by
  rw [ElementaryComparison.compareExp, dif_pos hpositive,
    ElementaryComparison.prepareLog_eq_real, ElementaryComparison.compareLog_eq_real]

/-- Cached logarithmic bounds preserve the inverse hyperbolic sine comparator at positive inputs. -/
theorem prepareArsinhPositive_eq_compare (argument boundary : ℚ) (levels : Nat)
    (hpositive : 0 < argument) :
    (prepareArsinhPositive argument levels hpositive).compare boundary =
      compareArsinh argument boundary := by
  rw [prepareArsinhPositive, Enclosure.Comparison.Prepared.compare]
  split
  · rename_i hboundary
    simp only [prepareLog_swap, compareArsinh, compareSinh, dif_pos hboundary,
      compareSinhPositive, not_le_of_gt hpositive, ↓reduceIte]
  · rfl

/-- Prepared inverse hyperbolic sine has the same exact real ordering at every boundary. -/
theorem prepareArsinh_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareArsinh argument levels).compare boundary =
      cmp (Real.arsinh (argument : ℝ)) (boundary : ℝ) := by
  unfold prepareArsinh
  split
  · rw [prepareArsinhPositive_eq_compare, compareArsinh_eq_real]
  · split
    · rw [Enclosure.Comparison.Prepared.compare, prepareArsinhPositive_eq_compare,
        compareArsinh_eq_real, Rat.cast_neg, Real.arsinh_neg, Rat.cast_neg, cmp_swap]
      simp only [cmp, cmpUsing, neg_lt_neg_iff]
    · have hzero : argument = 0 := by linarith
      subst argument
      simp [Enclosure.Comparison.Prepared.compare, cmp, cmpUsing]

/-- Prepared inverse hyperbolic cosine preserves its comparator on all rational inputs. -/
theorem prepareArcosh_eq_compare (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareArcosh argument levels).compare boundary = compareArcosh argument boundary := by
  unfold prepareArcosh
  split
  · rename_i hargument
    rw [Enclosure.Comparison.Prepared.compare]
    split
    · rename_i hboundary
      simp only [prepareLog_swap, compareArcosh, not_lt_of_ge hboundary.le, ↓reduceIte,
        compareCosh, ne_of_gt hboundary, ↓reduceDIte, abs_of_pos hboundary,
        compareCoshPositive, not_le_of_gt hargument]
    · rfl
  · rfl

/-- Prepared inverse hyperbolic cosine agrees with its nonnegative real branch on `[1, ∞)`. -/
theorem prepareArcosh_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ)
    (hargument : 1 ≤ argument) :
    (prepareArcosh argument levels).compare boundary =
      cmp (Real.arcosh (argument : ℝ)) (boundary : ℝ) := by
  rw [prepareArcosh_eq_compare, compareArcosh_eq_real argument boundary hargument]

/-- Caching the fixed logarithm preserves the inverse hyperbolic tangent comparison on `(-1, 1)`. -/
theorem prepareArtanh_eq_real (argument : ℚ) (levels : Nat)
    (hlower : -1 < argument) (hupper : argument < 1) (boundary : ℚ) :
    (prepareArtanh argument levels hlower hupper).compare boundary =
      cmp (Real.artanh (argument : ℝ)) (boundary : ℝ) := by
  rw [← compareArtanh_eq_real argument boundary hlower hupper]
  rw [prepareArtanh, Enclosure.Comparison.Prepared.compare, compareArtanh,
    ElementaryComparison.prepareLog_eq_real, ElementaryComparison.compareLog_eq_real]

end FloatLib.Numerics.HyperbolicComparison
