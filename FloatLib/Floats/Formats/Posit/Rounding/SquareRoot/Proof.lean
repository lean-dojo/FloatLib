/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Real
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Runtime
public import Mathlib.Analysis.Real.Sqrt

import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of rational-free exact posit square-root rounding

A finite posit is dyadic, although its square root need not be. This module proves that exact
squared comparisons agree with the rational-comparison specification and then connects that
specification to rounding `Real.sqrt`. Real numbers remain confined to this proof layer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

private theorem rat_mul_self_le_iff_le_sqrt
    {value radicand : Rat} (hvalue : 0 ≤ value) (hradicand : 0 ≤ radicand) :
    value * value ≤ radicand ↔
      (value : ℝ) ≤ Real.sqrt (radicand : ℝ) := by
  rw [Real.le_sqrt]
  · norm_cast
    rw [pow_two]
  · exact_mod_cast hvalue
  · exact_mod_cast hradicand

private theorem rat_lt_mul_self_iff_sqrt_lt
    {radicand value : Rat} (hvalue : 0 < value) :
    radicand < value * value ↔
      Real.sqrt (radicand : ℝ) < (value : ℝ) := by
  rw [Real.sqrt_lt' (by exact_mod_cast hvalue)]
  norm_cast
  rw [pow_two]

private theorem rat_mul_self_lt_iff_lt_sqrt
    {value radicand : Rat} (hvalue : 0 ≤ value) :
    value * value < radicand ↔
      (value : ℝ) < Real.sqrt (radicand : ℝ) := by
  rw [Real.lt_sqrt (by exact_mod_cast hvalue)]
  norm_cast
  rw [pow_two]

private theorem sqrt_ratCast_eq_of_eq_mul_self
    {radicand value : Rat} (hvalue : 0 ≤ value)
    (heq : radicand = value * value) :
    Real.sqrt (radicand : ℝ) = (value : ℝ) := by
  rw [heq]
  push_cast
  rw [← pow_two, Real.sqrt_sq (by exact_mod_cast hvalue)]

private theorem nonnegativeRatAt_nonneg_of_lt_signMask
    (format : Format) {code : Nat} (hcode : code < format.signMaskNat) :
    0 ≤ nonnegativeRatAt format code := by
  by_cases hzero : code = 0
  · subst code
    simp [nonnegativeRatAt_zero]
  · exact le_of_lt
      (nonnegativeRatAt_pos format (Nat.pos_of_ne_zero hzero) hcode)

private theorem lowerSqrtCode_lt_signMask
    (format : Format) (radicand : Rat) :
    lowerSqrtCode format radicand < format.signMaskNat := by
  apply lowerCodeByBisection_lt_upper
  exact format.signMaskNat_pos

private theorem minPositiveRat_pos (format : Format) :
    0 < minPositiveRat format := by
  exact nonnegativeRatAt_pos format (by omega) format.one_lt_signMaskNat

/--
The squared rational search and the real square-root search select the same lower posit code.

This is the order-theoretic bridge behind executable square-root rounding: for nonnegative values,
`x² ≤ r` is equivalent to `x ≤ Real.sqrt r`.
-/
theorem lowerSqrtCode_eq_realRounding_lowerCode
    (format : Format) (radicand : Rat) (hradicand : 0 ≤ radicand) :
    lowerSqrtCode format radicand =
      RealRounding.lowerCode format (Real.sqrt (radicand : ℝ)) := by
  unfold lowerSqrtCode RealRounding.lowerCode
  apply lowerCodeByBisection_congr
  intro code _ hcode
  simp only [RealRounding.nonnegativeRealAt,
    rat_mul_self_le_iff_le_sqrt
      (nonnegativeRatAt_nonneg_of_lt_signMask format hcode) hradicand]
  rfl

/--
Squared-comparison square-root rounding is exactly real-valued rounding of `Real.sqrt`.

The proof covers the standard's nonzero-underflow saturation, exact roots, overflow saturation,
appended-bit boundary, and tie-to-even rule for every static posit width.
-/
theorem roundSqrtCode_eq_roundPositiveCode
    (format : Format) (radicand : Rat) (hradicand : 0 ≤ radicand) :
    roundSqrtCode format radicand =
      RealRounding.roundPositiveCode format (Real.sqrt (radicand : ℝ)) := by
  rcases hradicand.lt_or_eq with hpos | hzero
  swap
  · subst hzero
    simp [roundSqrtCode, RealRounding.roundPositiveCode]
  have hsqrtPos : 0 < Real.sqrt (radicand : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hpos)
  have hlowerLt := lowerSqrtCode_lt_signMask format radicand
  have hlowerValueNonneg :=
    nonnegativeRatAt_nonneg_of_lt_signMask format hlowerLt
  have hthresholdPos :
      0 < roundingThreshold format (lowerSqrtCode format radicand) := by
    apply nonnegativeRatAt_pos format.nextPrecision (by omega)
    rw [Format.nextPrecision_signMaskNat]
    omega
  have hunderflow :
      radicand < minPositiveRat format * minPositiveRat format ↔
        Real.sqrt (radicand : ℝ) < RealRounding.minPositive format :=
    rat_lt_mul_self_iff_sqrt_lt (minPositiveRat_pos format)
  have hbelow :
      radicand <
          roundingThreshold format (lowerSqrtCode format radicand) *
            roundingThreshold format (lowerSqrtCode format radicand) ↔
        Real.sqrt (radicand : ℝ) <
          RealRounding.roundingThreshold format
            (lowerSqrtCode format radicand) :=
    rat_lt_mul_self_iff_sqrt_lt hthresholdPos
  have habove :
      roundingThreshold format (lowerSqrtCode format radicand) *
          roundingThreshold format (lowerSqrtCode format radicand) <
          radicand ↔
        RealRounding.roundingThreshold format
            (lowerSqrtCode format radicand) <
          Real.sqrt (radicand : ℝ) :=
    rat_mul_self_lt_iff_lt_sqrt hthresholdPos.le
  have hexact :
      radicand =
          nonnegativeRatAt format (lowerSqrtCode format radicand) *
            nonnegativeRatAt format (lowerSqrtCode format radicand) →
        Real.sqrt (radicand : ℝ) <
          RealRounding.roundingThreshold format
            (lowerSqrtCode format radicand) := by
    intro heq
    rw [sqrt_ratCast_eq_of_eq_mul_self hlowerValueNonneg heq]
    exact Rat.cast_lt.mpr
      (nonnegativeRatAt_lt_roundingThreshold format hlowerLt)
  unfold roundSqrtCode RealRounding.roundPositiveCode
  rw [← lowerSqrtCode_eq_realRounding_lowerCode format radicand hpos.le]
  dsimp only
  simp only [not_le.mpr hpos, not_le.mpr hsqrtPos, if_false, hunderflow,
    hbelow, habove]
  split_ifs <;> first | rfl | (exfalso; exact ‹¬_› (hexact ‹_›))

/-- Model-valued squared-comparison rounding equals real rounding of `Real.sqrt`. -/
theorem roundSqrtRat_eq_roundPositive
    (format : Format) (radicand : Rat) (hradicand : 0 ≤ radicand) :
    roundSqrtRat format radicand =
      RealRounding.roundPositive format (Real.sqrt (radicand : ℝ)) := by
  unfold roundSqrtRat RealRounding.roundPositive
  rw [roundSqrtCode_eq_roundPositiveCode
    format radicand hradicand]

end FloatLib.Floats.Formats.Posit.Model

namespace FloatLib.Floats.Formats.Posit.Model.DyadicSquareRoot

open FloatLib.Numerics

/-- The dyadic square search follows exactly the reference rational search. -/
theorem lowerCode_eq_reference (format : Format) (radicand : FloatLib.Numerics.Dyadic) :
    lowerCode format radicand =
      Model.lowerSqrtCode format radicand.toRat := by
  unfold lowerCode Model.lowerSqrtCode
  congr 1
  funext code
  rw [FloatLib.Numerics.Dyadic.isLessOrEqual_eq_decide,
    FloatLib.Numerics.Dyadic.mul_toRat,
    DyadicRounding.nonnegativeDyadicAt_toRat]

/--
Dyadic squared-comparison rounding selects exactly the rational specification's code.

The sign premise is the domain condition for square root. Negative finite inputs are handled as
NaR by the arithmetic operation before reaching this rounder.
-/
theorem roundCode_eq_reference_of_nonnegative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    roundCode format radicand =
      Model.roundSqrtCode format radicand.toRat := by
  by_cases hsignificand : radicand.significand = 0
  · have hzero : radicand.toRat = 0 := by
      simp [FloatLib.Numerics.Dyadic.toRat,
        FloatLib.Numerics.Dyadic.signedSignificand, hsignificand]
    simp [roundCode, hsignificand, hzero, Model.roundSqrtCode]
  · have hpositive :=
      FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
        radicand hsignificand hnegative
    have hsignificandBool : (radicand.significand == 0) = false :=
      beq_eq_false_iff_ne.mpr hsignificand
    unfold roundCode Model.roundSqrtCode
    simp only [hsignificandBool, Bool.false_eq_true, if_false,
      not_le.mpr hpositive,
      FloatLib.Numerics.Dyadic.isLess_eq_decide,
      FloatLib.Numerics.Dyadic.isEqual_eq_decide,
      decide_eq_true_eq,
      FloatLib.Numerics.Dyadic.mul_toRat,
      DyadicRounding.minPositive_toRat,
      DyadicRounding.roundingThreshold_toRat,
      DyadicRounding.nonnegativeDyadicAt_toRat,
      lowerCode_eq_reference]


/-- Rational-free nonnegative square-root rounding refines the reference model rounder. -/
theorem round_eq_reference_of_nonnegative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    round format radicand =
      Model.roundSqrtRat format radicand.toRat := by
  unfold round Model.roundSqrtRat
  rw [roundCode_eq_reference_of_nonnegative format radicand hnegative]

/--
Exact-dyadic square-root execution equals real-valued rounding of the mathematical square root.

This theorem is the end-to-end semantic statement for the runtime rounder. It introduces
no real-number computation: `Real.sqrt` occurs only on the noncomputable specification side.
-/
theorem round_eq_realRounding_sqrt_of_nonnegative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    round format radicand =
      Model.RealRounding.roundPositive format
        (Real.sqrt (radicand.toRat : ℝ)) := by
  have hradicandNonnegative : 0 ≤ radicand.toRat := by
    by_cases hsignificand : radicand.significand = 0
    · have hzero : radicand.toRat = 0 :=
        (FloatLib.Numerics.Dyadic.toRat_eq_zero_iff radicand).2 hsignificand
      simp [hzero]
    · exact le_of_lt
        (FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
          radicand hsignificand hnegative)
  rw [round_eq_reference_of_nonnegative format radicand hnegative,
    Model.roundSqrtRat_eq_roundPositive
      format radicand.toRat hradicandNonnegative]

/--
A nonzero dyadic whose rational value is not negative carries a clear sign bit.

Square-root rounders state their domain condition as `¬radicand.toRat < 0`; this lemma converts
that condition into the sign-field premise used by the refinement theorems.
-/
theorem negative_eq_false_of_not_toRat_neg
    (radicand : FloatLib.Numerics.Dyadic)
    (hsignificand : radicand.significand ≠ 0)
    (hnonnegative : ¬radicand.toRat < 0) :
    radicand.negative = false := by
  cases hsign : radicand.negative
  · rfl
  · exfalso
    apply hnonnegative
    rw [← neg_neg radicand.toRat, ← FloatLib.Numerics.Dyadic.neg_toRat, neg_lt_zero]
    exact FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
      radicand.neg (by simpa using hsignificand) (by simp [hsign])

/--
The same refinement theorem stated by the mathematical square-root domain condition.

This form is convenient for arithmetic dispatch: exact comparison with zero proves the premise
without exposing the dyadic carrier's sign field.
-/
theorem round_eq_reference_of_not_negative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnonnegative : ¬radicand.toRat < 0) :
    round format radicand =
      Model.roundSqrtRat format radicand.toRat := by
  by_cases hsignificand : radicand.significand = 0
  · have hzero : radicand.toRat = 0 :=
      (FloatLib.Numerics.Dyadic.toRat_eq_zero_iff radicand).2 hsignificand
    rw [hzero, Model.roundSqrtRat_zero]
    simp [round, roundCode, hsignificand, Model.zero]
  · exact round_eq_reference_of_nonnegative format radicand
      (negative_eq_false_of_not_toRat_neg radicand hsignificand hnonnegative)

end FloatLib.Floats.Formats.Posit.Model.DyadicSquareRoot
