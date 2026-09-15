/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Correct rounding of integer posit roots

Raising nonnegative values to a positive integer power preserves order, so exact power comparisons
agree with comparison against the real root. The shared comparator-rounding theorem then supplies
correct rounding. The root-characterization theorem applies to any nonnegative real root.
Its real-power corollary supplies a root for every nonnegative rational radicand and
positive degree.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.RootRounding

private theorem cmp_pow_eq_real {q c : Rat} {x : ℝ} {n : Nat}
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hn : n ≠ 0) (heq : x ^ n = (q : ℝ)) :
    cmp q (c ^ n) = cmp x (c : ℝ) := by
  have hlt : q < c ^ n ↔ x < (c : ℝ) := by
    have hcast : q < c ^ n ↔ (q : ℝ) < (c : ℝ) ^ n := by norm_cast
    rw [hcast, ← heq, pow_lt_pow_iff_left₀ hx (by exact_mod_cast hc) hn]
  have hgt : c ^ n < q ↔ (c : ℝ) < x := by
    have hcast : c ^ n < q ↔ (c : ℝ) ^ n < (q : ℝ) := by norm_cast
    rw [hcast, ← heq, pow_lt_pow_iff_left₀ (by exact_mod_cast hc) hx hn]
  simp only [cmp, cmpUsing, hlt, hgt]

/-- Exact power comparison agrees with every rational comparison against a nonnegative root. -/
theorem compareRoot_eq_real (q : Rat) (n : Nat) (x : ℝ)
    (hx : 0 ≤ x) (hn : n ≠ 0) (heq : x ^ n = (q : ℝ)) (candidate : Rat) :
    compareRoot q n candidate = cmp x (candidate : ℝ) := by
  by_cases hnegative : candidate < 0
  · have hlt : (candidate : ℝ) < x :=
      lt_of_lt_of_le (by exact_mod_cast hnegative) hx
    simp [compareRoot, hnegative, (cmp_eq_gt_iff _ _).mpr hlt]
  · have hcompare := cmp_pow_eq_real (le_of_not_gt hnegative) hx hn heq
    by_cases hzero : candidate = 0
    · subst candidate
      simpa [compareRoot, zero_pow hn] using hcompare
    · simpa only [compareRoot, ite_eq_right hnegative, ite_eq_right hzero] using hcompare

/-- Model-valued exact root rounding agrees with real rounding of a characterized root. -/
theorem round_eq_real (format : Format) (q : Rat) (n : Nat) (x : ℝ)
    (hx : 0 ≤ x) (hn : n ≠ 0) (heq : x ^ n = (q : ℝ)) :
    round format q n = RealRounding.roundPositive format x := by
  exact ComparisonRounding.round_eq_real format _ x
    (compareRoot_eq_real q n x hx hn heq)

/-- For positive degree and nonnegative radicand, exact root rounding rounds `q ^ (1 / n)`. -/
theorem round_eq_rpow (format : Format) (q : Rat) (n : Nat)
    (hq : 0 ≤ q) (hn : n ≠ 0) :
    round format q n =
      RealRounding.roundPositive format ((q : ℝ) ^ (n : ℝ)⁻¹) := by
  have hqReal : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  exact round_eq_real format q n _ (Real.rpow_nonneg hqReal _) hn
    (Real.rpow_inv_natCast_pow hqReal hn)

end FloatLib.Floats.Formats.Posit.Model.RootRounding

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

private theorem root_radicand_rpow (q : Rat) (degree : Int) :
    ((if degree < 0 then q⁻¹ else q : Rat) : ℝ) ^ (degree.natAbs : ℝ)⁻¹ =
      (q : ℝ) ^ (degree : ℝ)⁻¹ := by
  by_cases hnegative : degree < 0
  · have hcast : (degree.natAbs : ℝ) = -(degree : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hnegative, Int.cast_neg]
    simp only [ite_eq_left hnegative, Rat.cast_inv, hcast, inv_neg,
      ← Real.rpow_neg_eq_inv_rpow, neg_neg]
  · have hcast : (degree.natAbs : ℝ) = (degree : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (le_of_not_gt hnegative)]
    simp [hnegative, hcast]

/--
A nonnegative finite integer root rounds the exact real power `q ^ (1 / degree)`.

The degree is nonzero; a zero radicand additionally requires positive degree. Negative degrees
are covered by inverting the exact rational radicand, before any rounding.
-/
theorem rootN_eq_roundPositive (value : Model format) {q : Rat} (degree : Int)
    (hvalue : value.toRat? = some q) (hq : 0 ≤ q) (hdegree : degree ≠ 0)
    (hdomain : q ≠ 0 ∨ 0 < degree) :
    rootN value degree =
      RealRounding.roundPositive format ((q : ℝ) ^ (degree : ℝ)⁻¹) := by
  have hzero : ¬(q = 0 ∧ degree < 0) := by
    rcases hdomain with hq | hdegree
    · exact fun h => hq h.1
    · exact fun h => (not_lt.mpr hdegree.le) h.2
  have hradicand : 0 ≤ (if degree < 0 then q⁻¹ else q : Rat) := by
    split_ifs
    · exact inv_nonneg.mpr hq
    · exact hq
  simp only [rootN, hvalue, ite_eq_right hdegree, ite_eq_right hzero, not_lt.mpr hq,
    false_and, ite_false, abs_of_nonneg hq]
  rw [RootRounding.round_eq_rpow format _ degree.natAbs hradicand
    (Int.natAbs_ne_zero.mpr hdegree), root_radicand_rpow]

/--
For a negative finite input and odd integer degree, the signed real root is rounded once.

Its magnitude is `(-q) ^ (1 / degree)`. This statement specifies the real branch explicitly,
including negative odd degrees, without relying on real powers of a negative base.
-/
theorem rootN_eq_neg_roundPositive (value : Model format) {q : Rat} (degree : Int)
    (hvalue : value.toRat? = some q) (hq : q < 0) (hodd : degree % 2 ≠ 0) :
    rootN value degree =
      neg (RealRounding.roundPositive format ((-(q : ℝ)) ^ (degree : ℝ)⁻¹)) := by
  have hdegree : degree ≠ 0 := by
    intro hzero
    exact hodd (by simp [hzero])
  have hradicand : 0 ≤ (if degree < 0 then (-q)⁻¹ else -q : Rat) := by
    split_ifs
    · exact inv_nonneg.mpr (neg_nonneg.mpr hq.le)
    · exact neg_nonneg.mpr hq.le
  simp only [rootN, hvalue, ite_eq_right hdegree, ne_of_lt hq, false_and, ite_false,
    hodd, and_false, abs_of_neg hq, ite_eq_left hq]
  rw [RootRounding.round_eq_rpow format _ degree.natAbs hradicand
    (Int.natAbs_ne_zero.mpr hdegree), root_radicand_rpow]
  simp

/-- Integer roots propagate NaR for every degree. -/
@[simp] theorem rootN_nar (degree : Int) : rootN (nar format) degree = nar format := by
  simp [rootN]

/-- Degree zero has no defined integer-root operation. -/
@[simp] theorem rootN_degree_zero (value : Model format) : rootN value 0 = nar format := by
  cases hvalue : value.toRat? <;> simp [rootN, hvalue]

/-- Negative-degree roots of zero are not finite real numbers. -/
theorem rootN_zero_of_neg (degree : Int) (hdegree : degree < 0) :
    rootN (zero format) degree = nar format := by
  simp [rootN, hdegree, ne_of_lt hdegree]

/-- Every positive-degree root of zero is zero. -/
theorem rootN_zero_of_pos (degree : Int) (hdegree : 0 < degree) :
    rootN (zero format) degree = zero format := by
  simp only [rootN, toRat?_zero]
  simp [RootRounding.round, ComparisonRounding.round, ComparisonRounding.roundCode,
    RootRounding.compareRoot, hdegree.not_gt, ne_of_gt hdegree]
  rfl

/-- Even-degree roots of a negative finite input are not real. -/
theorem rootN_eq_nar_of_neg_even (value : Model format) {q : Rat} (degree : Int)
    (hvalue : value.toRat? = some q) (hq : q < 0) (heven : degree % 2 = 0) :
    rootN value degree = nar format := by
  simp [rootN, hvalue, hq, heven]

end FloatLib.Floats.Formats.Posit.Model
