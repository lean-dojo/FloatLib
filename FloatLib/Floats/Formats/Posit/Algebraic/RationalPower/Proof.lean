/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.RationalPower.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Proof

/-!
# Real semantics of rational powers and fused minus-one exponentials

For nonnegative bases in the stated domain, the executable result equals Section 4.1
rounding of the exact real power. Negative bases with integral exponents round the exact rational
integer power. NaR, zero to a nonpositive power, and negative bases with nonintegral exponents
have explicit exceptional-value theorems.

The proofs establish correctness, including ties and saturation, without a claim about feasible
running time for large rational numerators or denominators.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

private theorem roundRat_eq_roundPositive_of_nonneg (q : Rat) (hq : 0 ≤ q) :
    roundRat format q = RealRounding.roundPositive format (q : ℝ) := by
  rw [RealRounding.roundPositive_ratCast]
  by_cases hq0 : q = 0
  · subst q
    simp [roundPositiveRat, roundPositiveCode, zero]
  · simp [roundRat, hq0, not_lt.mpr hq]

/-- Certified boundary comparisons round a positive-base real power exactly once. -/
theorem roundPositiveRatPower_eq_roundPositive (base exponent : Rat) (hbase : 0 < base) :
    roundPositiveRatPower format base exponent =
      RealRounding.roundPositive format ((base : ℝ) ^ (exponent : ℝ)) := by
  unfold roundPositiveRatPower
  split
  · rename_i hinteger
    have he : (exponent : ℝ) = (exponent.num : ℝ) := by
      simp [Rat.cast_def, hinteger.1]
    rw [he, Real.rpow_intCast, ← Rat.cast_zpow]
    exact roundRat_eq_roundPositive_of_nonneg _ (zpow_nonneg hbase.le _)
  · apply ComparisonRounding.round_eq_real
    intro candidate
    exact FloatLib.Numerics.RationalPower.compareWithEnclosure_eq_real
      base exponent candidate (format.bits + 8) hbase

private theorem roundPositiveRatPower_eq_roundRat (base exponent : Rat) (hbase : 0 < base)
    (hinteger : exponent.den = 1) :
    roundPositiveRatPower format base exponent = roundRat format (base ^ exponent.num) := by
  have he : (exponent : ℝ) = (exponent.num : ℝ) := by simp [Rat.cast_def, hinteger]
  rw [roundPositiveRatPower_eq_roundPositive base exponent hbase, he, Real.rpow_intCast,
    ← Rat.cast_zpow, ← roundRat_eq_roundPositive_of_nonneg _ (zpow_nonneg hbase.le _)]

/--
In its nonnegative real domain, the executable power rounds the exact real power once.
A zero base requires a positive exponent; every exponent is allowed for a positive base.
-/
theorem roundRatPower_eq_roundPositive (base exponent : Rat) (hbase : 0 ≤ base)
    (hdomain : base ≠ 0 ∨ 0 < exponent) :
    roundRatPower format base exponent =
      RealRounding.roundPositive format ((base : ℝ) ^ (exponent : ℝ)) := by
  by_cases hzero : base = 0
  · subst base
    have he : 0 < exponent := hdomain.resolve_left (by simp)
    have heReal : (exponent : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp only [roundRatPower, he, if_true, Rat.cast_zero, Real.zero_rpow heReal]
    simpa using roundRat_eq_roundPositive_of_nonneg (format := format) 0 (by decide)
  by_cases hone : base = 1
  · subst base
    simp only [roundRatPower, one_ne_zero, if_false, Rat.cast_one, Real.one_rpow]
    simpa using roundRat_eq_roundPositive_of_nonneg (format := format) 1 (by decide)
  simp only [roundRatPower, hzero, hone, if_false, not_lt.mpr hbase]
  exact roundPositiveRatPower_eq_roundPositive base exponent (lt_of_le_of_ne hbase (Ne.symm hzero))

/-- A negative base with an integral exponent rounds the exact rational integer power once. -/
theorem roundRatPower_eq_roundRat_of_neg (base exponent : Rat) (hbase : base < 0)
    (hinteger : exponent.den = 1) :
    roundRatPower format base exponent = roundRat format (base ^ exponent.num) := by
  have hone : base ≠ 1 := by linarith
  simp only [roundRatPower, hbase.ne, hone, hbase, hinteger, if_false, if_true]
  rw [roundPositiveRatPower_eq_roundRat (-base) exponent (neg_pos.mpr hbase) hinteger]
  split
  · rename_i heven
    rw [(Int.even_iff.mpr heven).neg_zpow]
  · rename_i hodd
    have he : Odd exponent.num := Int.not_even_iff_odd.mp (by simpa [Int.even_iff] using hodd)
    have hq : 0 < (-base) ^ exponent.num := zpow_pos (neg_pos.mpr hbase) _
    have hpower : base ^ exponent.num = -((-base) ^ exponent.num) := by
      simpa using he.neg_zpow (-base)
    rw [hpower]
    simp [roundRat, hq.ne', not_lt.mpr hq.le, neg_ne_zero.mpr hq.ne',
      neg_lt_zero.mpr hq]

/-- A negative base with nonintegral exponent is outside the supported real branch. -/
theorem roundRatPower_eq_nar_of_neg_nonintegral (base exponent : Rat) (hbase : base < 0)
    (hinteger : exponent.den ≠ 1) :
    roundRatPower format base exponent = nar format := by
  have hone : base ≠ 1 := by linarith
  simp [roundRatPower, hbase.ne, hone, hinteger, hbase]

/-- Zero to zero or a negative exponent produces NaR, excluding total-field conventions. -/
theorem roundRatPower_zero_of_nonpositive (exponent : Rat) (hexponent : exponent ≤ 0) :
    roundRatPower format 0 exponent = nar format := by
  simp [roundRatPower, not_lt.mpr hexponent]

/-- Zero to a positive exponent is represented exactly. -/
theorem roundRatPower_zero_of_pos (exponent : Rat) (hexponent : 0 < exponent) :
    roundRatPower format 0 exponent = zero format := by
  simp [roundRatPower, hexponent]

/-- A base of one returns rounded one without expanding denominator-sized boundary powers. -/
@[simp] theorem roundRatPower_one (exponent : Rat) :
    roundRatPower format 1 exponent = roundRat format 1 := by
  simp [roundRatPower]

/-- Finite nonnegative posit powers round the exact real power once in its real domain. -/
theorem pow_eq_roundPositive (base exponent : Model format) {b e : Rat}
    (hbase : base.toRat? = some b) (hexponent : exponent.toRat? = some e)
    (hb : 0 ≤ b) (hdomain : b ≠ 0 ∨ 0 < e) :
    pow base exponent = RealRounding.roundPositive format ((b : ℝ) ^ (e : ℝ)) := by
  simp only [pow, hbase, hexponent]
  exact roundRatPower_eq_roundPositive b e hb hdomain

/-- A finite negative posit base with an integral exponent rounds its exact rational power. -/
theorem pow_eq_roundRat_of_neg (base exponent : Model format) {b e : Rat}
    (hbase : base.toRat? = some b) (hexponent : exponent.toRat? = some e)
    (hb : b < 0) (hinteger : e.den = 1) :
    pow base exponent = roundRat format (b ^ e.num) := by
  simp only [pow, hbase, hexponent]
  exact roundRatPower_eq_roundRat_of_neg b e hb hinteger

/-- Negative bases with finite nonintegral posit exponents produce NaR. -/
theorem pow_eq_nar_of_neg_nonintegral (base exponent : Model format) {b e : Rat}
    (hbase : base.toRat? = some b) (hexponent : exponent.toRat? = some e)
    (hb : b < 0) (hinteger : e.den ≠ 1) :
    pow base exponent = nar format := by
  simp only [pow, hbase, hexponent]
  exact roundRatPower_eq_nar_of_neg_nonintegral b e hb hinteger

/-- Zero to a finite nonpositive posit exponent produces NaR, including zero to zero. -/
theorem pow_zero_of_nonpositive (exponent : Model format) {e : Rat}
    (hexponent : exponent.toRat? = some e) (he : e ≤ 0) :
    pow (zero format) exponent = nar format := by
  simp only [pow, toRat?_zero, hexponent]
  exact roundRatPower_zero_of_nonpositive e he

/-- Zero to a finite positive posit exponent is zero. -/
theorem pow_zero_of_pos (exponent : Model format) {e : Rat}
    (hexponent : exponent.toRat? = some e) (he : 0 < e) :
    pow (zero format) exponent = zero format := by
  simp only [pow, toRat?_zero, hexponent]
  exact roundRatPower_zero_of_pos e he

/-- An exceptional base propagates even when its exponent is zero. -/
@[simp] theorem pow_nar_left (exponent : Model format) :
    pow (nar format) exponent = nar format := by
  simp [pow]

/-- An exceptional exponent propagates even when its base is one. -/
@[simp] theorem pow_nar_right (base : Model format) :
    pow base (nar format) = nar format := by
  simp [pow]

/-- Base-two exponential rounds the exact real power for every finite input. -/
theorem exp2_eq_roundPositive (value : Model format) {e : Rat}
    (hvalue : value.toRat? = some e) :
    exp2 value = RealRounding.roundPositive format ((2 : ℝ) ^ (e : ℝ)) := by
  simp only [exp2, hvalue]
  simpa using roundRatPower_eq_roundPositive (format := format) 2 e (by norm_num) (by norm_num)

/-- Base-ten exponential rounds the exact real power for every finite input. -/
theorem exp10_eq_roundPositive (value : Model format) {e : Rat}
    (hvalue : value.toRat? = some e) :
    exp10 value = RealRounding.roundPositive format ((10 : ℝ) ^ (e : ℝ)) := by
  simp only [exp10, hvalue]
  simpa using roundRatPower_eq_roundPositive (format := format) 10 e (by norm_num) (by norm_num)

/-- Base-two exponential propagates NaR. -/
@[simp] theorem exp2_nar : exp2 (nar format) = nar format := by simp [exp2]

/-- Base-ten exponential propagates NaR. -/
@[simp] theorem exp10_nar : exp10 (nar format) = nar format := by simp [exp10]

/-- Shifting the rational candidates fuses subtraction with the final signed real rounding. -/
theorem roundRatPowerMinusOne_eq_round (base exponent : Rat) (hbase : 0 < base) :
    roundRatPowerMinusOne format base exponent =
      RealRounding.round format ((base : ℝ) ^ (exponent : ℝ) - 1) := by
  unfold roundRatPowerMinusOne
  split
  · rename_i hinteger
    have he : (exponent : ℝ) = (exponent.num : ℝ) := by
      simp [Rat.cast_def, hinteger.1]
    rw [he, Real.rpow_intCast, ← Rat.cast_zpow]
    simpa only [Rat.cast_sub, Rat.cast_one] using
      (RealRounding.round_ratCast format (base ^ exponent.num - 1)).symm
  · apply ComparisonRounding.roundSigned_eq_real
    intro candidate
    rw [FloatLib.Numerics.RationalPower.compareWithEnclosure_eq_real
      base exponent (candidate + 1) (format.bits + 8) hbase, Rat.cast_add, Rat.cast_one]
    simp only [cmp, cmpUsing, sub_lt_iff_lt_add, lt_sub_iff_add_lt]

/-- Every finite input gives a single rounding of the exact base-two power minus one. -/
theorem exp2Minus1_eq_round (value : Model format) {e : Rat}
    (hvalue : value.toRat? = some e) :
    exp2Minus1 value = RealRounding.round format ((2 : ℝ) ^ (e : ℝ) - 1) := by
  simp only [exp2Minus1, hvalue]
  simpa using roundRatPowerMinusOne_eq_round (format := format) 2 e (by norm_num)

/-- Every finite input gives a single rounding of the exact base-ten power minus one. -/
theorem exp10Minus1_eq_round (value : Model format) {e : Rat}
    (hvalue : value.toRat? = some e) :
    exp10Minus1 value = RealRounding.round format ((10 : ℝ) ^ (e : ℝ) - 1) := by
  simp only [exp10Minus1, hvalue]
  simpa using roundRatPowerMinusOne_eq_round (format := format) 10 e (by norm_num)

/-- Base-two exponential minus one propagates NaR. -/
@[simp] theorem exp2Minus1_nar : exp2Minus1 (nar format) = nar format := by simp [exp2Minus1]

/-- Base-ten exponential minus one propagates NaR. -/
@[simp] theorem exp10Minus1_nar : exp10Minus1 (nar format) = nar format := by simp [exp10Minus1]

end FloatLib.Floats.Formats.Posit.Model
