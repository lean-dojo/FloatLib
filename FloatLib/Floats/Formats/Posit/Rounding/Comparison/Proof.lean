/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Real

/-!
# Correctness of comparator-based posit rounding

A comparator agreeing with real order makes exactly the same decisions as the real rounding
specification. No assumption about irrationality, distance from a boundary, or search convergence
is needed: exact equality is one of the comparator's three results.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.ComparisonRounding

/-- An exact comparator selects the same lower code as real rounding. -/
theorem lowerCode_eq_real (format : Format) (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ q : Rat, compareTarget q = cmp target (q : ℝ)) :
    lowerCode format compareTarget = RealRounding.lowerCode format target := by
  unfold lowerCode RealRounding.lowerCode
  apply lowerCodeByBisection_congr
  intro code _ _
  simp only [hcompare, ne_eq, cmp_eq_lt_iff, not_lt, RealRounding.nonnegativeRealAt]
  rfl

/-- Exact rational comparisons suffice for the complete positive real rounding rule. -/
theorem roundCode_eq_real (format : Format) (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ q : Rat, compareTarget q = cmp target (q : ℝ)) :
    roundCode format compareTarget = RealRounding.roundPositiveCode format target := by
  unfold roundCode RealRounding.roundPositiveCode
  rw [lowerCode_eq_real format compareTarget target hcompare]
  simp only [hcompare, ne_eq, cmp_eq_lt_iff, cmp_eq_gt_iff, Rat.cast_zero, not_lt,
    RealRounding.minPositive, RealRounding.roundingThreshold, RealRounding.nonnegativeRealAt,
    minPositiveRat, roundingThreshold]
  rfl

/-- The executable model is the result selected by the real posit specification. -/
theorem round_eq_real (format : Format) (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ q : Rat, compareTarget q = cmp target (q : ℝ)) :
    round format compareTarget = RealRounding.roundPositive format target := by
  unfold round RealRounding.roundPositive
  rw [roundCode_eq_real format compareTarget target hcompare]

/-- Reversing comparisons with negated candidates compares the negated target. -/
theorem compare_neg_eq_real (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ q : Rat, compareTarget q = cmp target (q : ℝ)) (q : Rat) :
    (compareTarget (-q)).swap = cmp (-target) (q : ℝ) := by
  rw [hcompare, cmp_swap, Rat.cast_neg]
  simp only [cmp, cmpUsing, neg_lt, lt_neg]

/-- Exact target comparisons also suffice for the complete signed real rounding rule. -/
theorem roundSigned_eq_real (format : Format) (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ q : Rat, compareTarget q = cmp target (q : ℝ)) :
    roundSigned format compareTarget = RealRounding.round format target := by
  unfold roundSigned RealRounding.round
  simp only [hcompare 0, Rat.cast_zero, cmp_eq_lt_iff]
  split
  · rw [round_eq_real format _ (-target) (compare_neg_eq_real compareTarget target hcompare)]
  · rw [round_eq_real format compareTarget target hcompare]

end FloatLib.Floats.Formats.Posit.Model.ComparisonRounding
