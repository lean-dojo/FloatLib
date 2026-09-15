/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Runtime

import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

/-!
# Correctness of rational-free exact posit quotient rounding

The executable quotient rounder compares candidate codes by cross multiplication instead of
constructing the rational quotient. This module proves the positive-code search, threshold test,
ties-to-even decision, sign handling, zero, and NaR branches equal to the reference rational
specification.

The comparison remains exact: multiplying dyadics preserves their integer significands and
binary exponents without rational normalization. The final theorem identifies the result with
exact rational division followed by standard posit rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicQuotient

open FloatLib.Numerics

/-- Exact product comparisons follow the reference rational quotient search. -/
theorem lowerCode_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic)
    (hdenominator : 0 < denominator.toRat) :
    lowerCode format numerator denominator =
      Model.lowerCodeForPositive format
        (numerator.toRat / denominator.toRat) := by
  unfold lowerCode Model.lowerCodeForPositive
  congr 1
  funext code
  rw [FloatLib.Numerics.Dyadic.isLessOrEqual_eq_decide,
    FloatLib.Numerics.Dyadic.mul_toRat,
    DyadicRounding.nonnegativeDyadicAt_toRat]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (le_div_iff₀ hdenominator).symm

/--
Cross-multiplied quotient rounding selects exactly the rational specification's positive code.
-/
theorem roundPositiveCode_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumeratorSignificand : numerator.significand ≠ 0)
    (hnumeratorNegative : numerator.negative = false)
    (hdenominatorSignificand : denominator.significand ≠ 0)
    (hdenominatorNegative : denominator.negative = false) :
    roundPositiveCode format numerator denominator =
      Model.roundPositiveCode format
        (numerator.toRat / denominator.toRat) := by
  have hnumeratorPositive :=
    FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
      numerator hnumeratorSignificand hnumeratorNegative
  have hdenominatorPositive :=
    FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
      denominator hdenominatorSignificand hdenominatorNegative
  have hquotientPositive :
      0 < numerator.toRat / denominator.toRat :=
    div_pos hnumeratorPositive hdenominatorPositive
  have hnumeratorBool : (numerator.significand == 0) = false :=
    beq_eq_false_iff_ne.mpr hnumeratorSignificand
  have hdenominatorBool : (denominator.significand == 0) = false :=
    beq_eq_false_iff_ne.mpr hdenominatorSignificand
  unfold roundPositiveCode roundFromLowerCode Model.roundPositiveCode
  simp only [hnumeratorBool, hnumeratorNegative, hdenominatorBool,
    hdenominatorNegative, Bool.false_or, Bool.false_eq_true, if_false,
    not_le.mpr hquotientPositive,
    FloatLib.Numerics.Dyadic.isLess_eq_decide,
    FloatLib.Numerics.Dyadic.mul_toRat,
    DyadicRounding.minPositive_toRat,
    DyadicRounding.roundingThreshold_toRat,
    decide_eq_true_eq,
    div_lt_iff₀ hdenominatorPositive,
    lt_div_iff₀ hdenominatorPositive,
    lowerCode_eq_reference format numerator denominator hdenominatorPositive]

/-- Rational-free positive quotient rounding refines the reference rational model rounder. -/
theorem roundPositive_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumeratorSignificand : numerator.significand ≠ 0)
    (hnumeratorNegative : numerator.negative = false)
    (hdenominatorSignificand : denominator.significand ≠ 0)
    (hdenominatorNegative : denominator.negative = false) :
    roundPositive format numerator denominator =
      Model.roundPositiveRat format
        (numerator.toRat / denominator.toRat) := by
  unfold roundPositive Model.roundPositiveRat
  rw [roundPositiveCode_eq_reference format numerator denominator
    hnumeratorSignificand hnumeratorNegative
    hdenominatorSignificand hdenominatorNegative]

/-- Standard rounding of a signed quotient of positive magnitudes, by cases on the two signs. -/
private theorem roundRat_signed_div (format : Format) {left right : Rat}
    (hleft : 0 < left) (hright : 0 < right) (leftNegative rightNegative : Bool) :
    Model.roundRat format
        ((if leftNegative then -left else left) / (if rightNegative then -right else right)) =
      if Bool.xor leftNegative rightNegative then
        Model.neg (Model.roundPositiveRat format (left / right))
      else
        Model.roundPositiveRat format (left / right) := by
  have hquotient : 0 < left / right := div_pos hleft hright
  have hpositive :
      Model.roundRat format (left / right) = Model.roundPositiveRat format (left / right) := by
    rw [Model.roundRat, if_neg hquotient.ne', if_neg (not_lt.mpr hquotient.le)]
  have hnegative :
      Model.roundRat format (-(left / right)) =
        Model.neg (Model.roundPositiveRat format (left / right)) := by
    rw [Model.roundRat, if_neg (neg_ne_zero.mpr hquotient.ne'),
      if_pos (neg_lt_zero.mpr hquotient), neg_neg]
  cases leftNegative <;> cases rightNegative <;> simp [div_neg, neg_div, hpositive, hnegative]

/-- The exact rational value of a dyadic is its magnitude's value with the sign flag applied. -/
private theorem toRat_eq_signed_magnitude (value : FloatLib.Numerics.Dyadic) :
    value.toRat =
      if value.negative then -(DyadicRounding.magnitude value).toRat
      else (DyadicRounding.magnitude value).toRat := by
  rw [DyadicRounding.magnitude_toRat]
  cases value.negative <;> simp

/--
Any positive-magnitude rounder that refines the rational specification yields, through the shared
signed shell `roundSignedWith`, the complete signed quotient specification.

The two exact quotient kernels differ only in their positive-magnitude rounder, so this single
proof of the exceptional cases and the four sign cases serves both.
-/
theorem roundSignedWith_eq_reference
    (format : Format)
    (roundMagnitude :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Model format)
    (hmagnitude : ∀ numerator denominator : FloatLib.Numerics.Dyadic,
      numerator.significand ≠ 0 → numerator.negative = false →
      denominator.significand ≠ 0 → denominator.negative = false →
      roundMagnitude numerator denominator =
        Model.roundPositiveRat format (numerator.toRat / denominator.toRat))
    (numerator denominator : FloatLib.Numerics.Dyadic) :
    roundSignedWith format roundMagnitude numerator denominator =
      if denominator.toRat = 0 then
        Model.nar format
      else
        Model.roundRat format (numerator.toRat / denominator.toRat) := by
  by_cases hdenominator : denominator.significand = 0
  · have hdenominatorRat : denominator.toRat = 0 :=
      (FloatLib.Numerics.Dyadic.toRat_eq_zero_iff denominator).2 hdenominator
    simp [roundSignedWith, hdenominator, hdenominatorRat]
  have hdenominatorRat : denominator.toRat ≠ 0 :=
    mt (FloatLib.Numerics.Dyadic.toRat_eq_zero_iff denominator).1 hdenominator
  by_cases hnumerator : numerator.significand = 0
  · have hnumeratorRat : numerator.toRat = 0 :=
      (FloatLib.Numerics.Dyadic.toRat_eq_zero_iff numerator).2 hnumerator
    simp [roundSignedWith, hdenominator, hnumerator, hdenominatorRat, hnumeratorRat]
  have hnumeratorMagnitude : (DyadicRounding.magnitude numerator).significand ≠ 0 := by
    simpa using hnumerator
  have hdenominatorMagnitude : (DyadicRounding.magnitude denominator).significand ≠ 0 := by
    simpa using hdenominator
  rw [roundSignedWith]
  simp only [beq_eq_false_iff_ne.mpr hdenominator, beq_eq_false_iff_ne.mpr hnumerator,
    Bool.false_eq_true, if_false, hdenominatorRat]
  rw [hmagnitude _ _ hnumeratorMagnitude rfl hdenominatorMagnitude rfl,
    toRat_eq_signed_magnitude numerator, toRat_eq_signed_magnitude denominator,
    roundRat_signed_div format
      (FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero _ hnumeratorMagnitude rfl)
      (FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero _ hdenominatorMagnitude rfl)]

/--
Signed cross-multiplied quotient rounding refines exact rational division and standard rounding.
-/
theorem round_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    round format numerator denominator =
      if denominator.toRat = 0 then
        Model.nar format
      else
        Model.roundRat format (numerator.toRat / denominator.toRat) :=
  roundSignedWith_eq_reference format (roundPositive format)
    (roundPositive_eq_reference format) numerator denominator

end FloatLib.Floats.Formats.Posit.Model.DyadicQuotient
