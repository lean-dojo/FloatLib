/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.SqrtProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.PowerProof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite

/-!
# Real rounding and exceptional policies for binary roots

Reciprocal square root rounds the square root of the exact reciprocal radicand. Integer roots
round the nonnegative root of the exact magnitude, inverting that magnitude before rounding
for negative degrees. Negative odd roots restore the sign after choosing the real branch.
The theorems include subnormal outputs and exact midpoint ties; only IEEE overflow is excluded.

Zero policies are stated separately because the real numbers have neither signed zero nor
infinity. In particular `rsqrt(-0)` has the negative overflow sign.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Reciprocal square root preserves the sign of a zero pole, including negative zero. -/
theorem rsqrt_of_isZero {fmt : FloatFormat} (value : Model fmt)
    (hzero : isZero value = true) :
    rsqrt value = nativeOverflow fmt (signBit value) := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true value hzero
  simp [rsqrt, chooseNaN1_none_of_isFinite value hfinite, hzero]

/-- Degree zero is invalid for every input, including infinities and signed zeros. -/
@[simp] theorem rootN_zero {fmt : FloatFormat} (value : Model fmt) :
    rootN value 0 = invalidResult fmt := by
  simp [rootN]

/-- Odd roots retain the sign of zero; even roots select a positive zero or positive pole. -/
theorem rootN_of_isZero {fmt : FloatFormat} (value : Model fmt) (degree : Int)
    (hzero : isZero value = true) (hdegree : degree ≠ 0) :
    rootN value degree =
      if degree < 0 then nativeOverflow fmt (signBit value && degree % 2 != 0)
      else zero fmt (signBit value && degree % 2 != 0) := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true value hzero
  simp [rootN, hdegree, chooseNaN1_none_of_isFinite value hfinite, hzero]

/--
Reciprocal square root of a finite positive operand is one nearest-even rounding of `1 / sqrt x`.
The reciprocal radicand is exact, so an intermediate rounded square root cannot affect the result.
-/
theorem toReal_rsqrt_eq_roundAt {fmt : FloatFormat} (value : Model fmt)
    (hfmt : fmt.isIEEE = true) (hvalue : isFinite value = true)
    (hzero : isZero value = false) (hsign : signBit value = false)
    (hfinite : isFinite (rsqrt value) = true) :
    toReal (rsqrt value) = roundAt fmt (Real.sqrt (toReal value))⁻¹ := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hvalue
  have hdsign : d.negative = false := (sign_eq_signBit_of_toDyadic?_some hd).trans hsign
  have hq : toRat? value = some d.toRat := by simp [toRat?, hd]
  have hrad : 0 ≤ d.toRat := by
    have hreal : 0 ≤ (d.toRat : ℝ) := by
      rw [Numerics.Dyadic.cast_toRat, Numerics.Dyadic.toReal]
      simp only [Numerics.Dyadic.cast_signedSignificand, hdsign, Bool.false_eq_true,
        ite_false, one_mul]
      positivity
    exact_mod_cast hreal
  have heq : rsqrt value = AlgebraicRounding.sqrtRat fmt false d.toRat⁻¹ := by
    simp [rsqrt, chooseNaN1_none_of_isFinite value hvalue, hzero, hsign,
      isInf_eq_false_of_toDyadic?_some hd, hq]
  rw [heq] at hfinite ⊢
  rw [AlgebraicRounding.toReal_sqrtRat_eq_roundAt fmt hfmt false _ (inv_nonneg.mpr hrad)
    hfinite, Algebraic.toReal_of_toRat?_eq_some hq]
  simp [Real.sqrt_inv]

namespace Algebraic

/-- Negative integer degrees invert the radicand before taking its nonnegative root. -/
theorem root_radicand_rpow (q : Rat) (degree : Int) :
    ((if degree < 0 then q⁻¹ else q : Rat) : ℝ) ^ (degree.natAbs : ℝ)⁻¹ =
      (q : ℝ) ^ (degree : ℝ)⁻¹ := by
  by_cases hnegative : degree < 0
  · have hcast : (degree.natAbs : ℝ) = -(degree : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hnegative, Int.cast_neg]
    simp only [ite_eq_left hnegative, Rat.cast_inv, hcast, inv_neg,
      ← Real.rpow_neg_eq_inv_rpow, _root_.neg_neg]
  · have hcast : (degree.natAbs : ℝ) = (degree : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (le_of_not_gt hnegative)]
    simp [hnegative, hcast]

end Algebraic

/--
A finite nonzero integer root rounds the chosen real branch once.

Even degrees require a clear sign bit; odd degrees allow either sign. Negative degrees are
reciprocal roots. The absolute value and explicit sign select the negative odd real branch
without relying on the convention for real exponentiation of negative bases.
-/
theorem toReal_rootN_eq_roundAt {fmt : FloatFormat} (value : Model fmt) (degree : Int)
    (hfmt : fmt.isIEEE = true) (hvalue : isFinite value = true)
    (hzero : isZero value = false) (hdegree : degree ≠ 0)
    (hdomain : signBit value = false ∨ degree % 2 ≠ 0)
    (hfinite : isFinite (rootN value degree) = true) :
    toReal (rootN value degree) =
      roundAt fmt (if signBit value then -(|toReal value| ^ (degree : ℝ)⁻¹)
        else |toReal value| ^ (degree : ℝ)⁻¹) := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hvalue
  have hq : toRat? value = some d.toRat := by simp [toRat?, hd]
  have hsign : (signBit value && degree % 2 != 0) = signBit value := by
    rcases hdomain with hs | hn
    · simp [hs]
    · simp [hn]
  have hbad : (signBit value && degree % 2 == 0) = false := by
    rcases hdomain with hs | hn
    · simp [hs]
    · simp [hn]
  let radicand := if degree < 0 then |d.toRat|⁻¹ else |d.toRat|
  have hrad : 0 ≤ radicand := by
    dsimp [radicand]
    split_ifs <;> positivity
  have heq : rootN value degree =
      AlgebraicRounding.root fmt (signBit value) radicand degree.natAbs := by
    calc
      _ = AlgebraicRounding.rootWithSqrt fmt (signBit value) radicand degree.natAbs := by
        simp [rootN, hdegree, chooseNaN1_none_of_isFinite value hvalue, hzero, hbad,
          isInf_eq_false_of_toDyadic?_some hd, hq, hsign, radicand]
      _ = _ := AlgebraicRounding.rootWithSqrt_eq_root fmt _ _ _ hrad
  rw [heq] at hfinite ⊢
  rw [AlgebraicRounding.toReal_root_eq_roundAt_rpow fmt hfmt _ _ _
    hrad (Int.natAbs_ne_zero.mpr hdegree) hfinite]
  have hpow : (radicand : ℝ) ^ (degree.natAbs : ℝ)⁻¹ =
      |(d.toRat : ℝ)| ^ (degree : ℝ)⁻¹ := by
    simpa only [radicand, Rat.cast_abs] using Algebraic.root_radicand_rpow |d.toRat| degree
  rw [hpow, Algebraic.toReal_of_toRat?_eq_some hq]

end FloatLib.Floats.Formats.BinaryInterchange.Model
