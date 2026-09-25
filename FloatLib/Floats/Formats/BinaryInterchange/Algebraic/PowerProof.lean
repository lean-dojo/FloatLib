/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import
  FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable

/-!
# Real semantics of exact integer powers

The power is evaluated in the rationals before any format rounding. Casting commutes with
integer exponentiation, including negative exponents, so the established rational-rounding
theorem proves a single rounding of the exact real power. IEEE overflow has no real denotation
and is excluded by the finite-result premise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

namespace Algebraic

/-- A successful rational decode is the exact real value of the stored operand. -/
theorem toReal_of_toRat?_eq_some {fmt : FloatFormat}
    {value : Model fmt} {q : Rat} (hvalue : toRat? value = some q) :
    toReal value = (q : ℝ) := by
  cases hdecode : toDyadic? value with
  | none => simp [toRat?, hdecode] at hvalue
  | some exact =>
    have hq : exact.toRat = q := by simpa [toRat?, hdecode] using hvalue
    rw [toReal_eq, hdecode, ← hq, Numerics.Dyadic.cast_toRat]

/-- Successful rational decoding characterizes a finite operand. -/
theorem isFinite_of_toRat?_eq_some {fmt : FloatFormat}
    {value : Model fmt} {q : Rat} (hvalue : toRat? value = some q) :
    isFinite value = true := by
  cases hdecode : toDyadic? value with
  | none => simp [toRat?, hdecode] at hvalue
  | some exact => exact isFinite_eq_true_of_toDyadic?_some hdecode

private theorem signedScaledRatToReal_eq_cast (value : Rat) :
    signedScaledRatToReal (decide (value < 0)) value.num.natAbs value.den 0 =
      (value : ℝ) := by
  have hmagnitude : (value.num.natAbs : ℝ) / value.den = |(value : ℝ)| := by
    simp [Rat.cast_def, abs_div]
  simp only [signedScaledRatToReal, scaledRatToReal, bpow_zero, mul_one, hmagnitude]
  by_cases hnegative : value < 0
  · have hreal : (value : ℝ) < 0 := by exact_mod_cast hnegative
    simp [hnegative, abs_of_neg hreal]
  · have hreal : 0 ≤ (value : ℝ) := by exact_mod_cast le_of_not_gt hnegative
    simp [hnegative, abs_of_nonneg hreal]

end Algebraic

/-- The exact rational boundary rounds once to the independent nearest-even real grid. -/
theorem toReal_roundAlgebraicRat (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (value : Rat) (hfinite : isFinite (roundAlgebraicRat fmt value) = true) :
    toReal (roundAlgebraicRat fmt value) = roundAt fmt (value : ℝ) := by
  by_cases hzero : value = 0
  · simp [hzero, roundAlgebraicRat]
  · have hnumerator : value.num.natAbs ≠ 0 := by simpa using hzero
    rw [roundAlgebraicRat, roundRat, toReal_roundRatScaled_eq_roundAt
      fmt (decide (value < 0)) value.num.natAbs value.den 0
      hfmt hnumerator value.den_nz hfinite, Algebraic.signedScaledRatToReal_eq_cast]

/-- A signaling NaN is quieted before every exponent case, including exponent zero. -/
theorem powInt_of_isSNaN {fmt : FloatFormat} (value : Model fmt) (exponent : Int)
    (hsignaling : isSNaN value = true) :
    powInt value exponent = quietNaN value := by
  have hnan : isNaN value = true := by
    cases hclass : isNaN value
    · have := isSNaN_eq_false_of_isNaN_eq_false value hclass
      simp [hsignaling] at this
    · rfl
  simp [powInt, hsignaling, chooseNaN1, hnan]

/-- The zero exponent returns one unless the base is a signaling NaN. -/
@[simp] theorem powInt_zero {fmt : FloatFormat} (value : Model fmt)
    (hnan : isSNaN value = false) :
    powInt value 0 = posOne fmt := by
  simp [powInt, hnan]

/-- A finite nonzero base uses exactly one rational rounding for every nonzero exponent. -/
theorem powInt_eq_roundAlgebraicRat {fmt : FloatFormat} (value : Model fmt)
    (exponent : Int) {q : Rat} (hvalue : toRat? value = some q)
    (hzero : isZero value = false) (hexponent : exponent ≠ 0) :
    powInt value exponent = roundAlgebraicRat fmt (q ^ exponent) := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hvalue
  have hnan : chooseNaN1 value = none := by
    simp [chooseNaN1, isNaN_eq_false_of_isFinite_eq_true value hfinite]
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  simp [powInt, isSNaN_eq_false_of_toDyadic?_some hd, hexponent, hnan, hzero,
    isInf_eq_false_of_toDyadic?_some hd, hvalue]

/--
Integer powers of finite nonzero inputs round the exact real power once, for positive, negative
and zero integer exponents. The output may be subnormal or zero; only overflow is excluded.
-/
theorem toReal_powInt_eq_roundAt {fmt : FloatFormat} (value : Model fmt) (exponent : Int)
    (hfmt : fmt.isIEEE = true) (hvalue : isFinite value = true)
    (hzero : isZero value = false) (hfinite : isFinite (powInt value exponent) = true) :
    toReal (powInt value exponent) = roundAt fmt (toReal value ^ exponent) := by
  by_cases hexponent : exponent = 0
  · subst exponent
    have hone : roundAt fmt 1 = 1 := by
      simpa using roundAt_toReal_eq (posOne fmt) (isFinite_posOne fmt)
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hvalue
    simp [isSNaN_eq_false_of_toDyadic?_some hd, hone]
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hvalue
    have hq : toRat? value = some d.toRat := by simp [toRat?, hd]
    rw [powInt_eq_roundAlgebraicRat value exponent hq hzero hexponent] at hfinite ⊢
    rw [toReal_roundAlgebraicRat fmt hfmt _ hfinite,
      Algebraic.toReal_of_toRat?_eq_some hq, Rat.cast_zpow]

end FloatLib.Floats.Formats.BinaryInterchange.Model
