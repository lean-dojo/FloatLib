/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Predicates
import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Numerical meaning of binary classification

For a finite value, normality means its magnitude reaches `2 ^ minNormalExponent`.
Subnormals have positive magnitude below that threshold. These equivalences hold for every
descriptor, including arbitrary valid biases and finite encodings with normal all-ones exponents.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

variable {fmt : FloatFormat}

/-- The exact magnitude of any finite word, expressed in its stored magnitude fields. -/
theorem abs_toRat_eq_fields {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    |d.toRat| =
      if expField x = 0 then
        (fracField x : ℚ) * (2 : ℚ) ^ fmt.minSubnormalExponent
      else
        ((2 : ℚ) ^ fmt.fracWidth + fracField x) *
          (2 : ℚ) ^ ((expField x : ℤ) - fmt.exponentBias - fmt.fracWidth) := by
  have habs (sign : Bool) (m : Nat) (e : ℤ) :
      |(Numerics.Dyadic.mk sign m e).toRat| = (m : ℚ) * (2 : ℚ) ^ e := by
    cases sign <;>
      simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, abs_mul,
        abs_of_nonneg (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) e)]
  have hd := toDyadic?_ofFields_of_isFinite fmt (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)
    (by simpa only [ofFields_signBit_expField_fracField] using
      isFinite_eq_true_of_toDyadic?_some hx)
  rw [ofFields_signBit_expField_fracField, hx] at hd
  split_ifs at hd with he hf
  all_goals
    cases Option.some.inj hd
    simp_all only [pow2_eq_two_pow, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_zero, zero_mul, ite_true, ite_false]
  rfl

private theorem normal_scale (fmt : FloatFormat) (e : ℤ) :
    (2 : ℚ) ^ fmt.fracWidth * (2 : ℚ) ^ (e - fmt.fracWidth) = (2 : ℚ) ^ e := by
  rw [← zpow_natCast (2 : ℚ), ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  omega

/-- A decoded finite value is normal exactly when its magnitude reaches the normal threshold. -/
theorem isNormal_iff_le_abs_toRat {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    isNormal x = true ↔ (2 : ℚ) ^ fmt.minNormalExponent ≤ |d.toRat| := by
  have hf := isFinite_eq_true_of_toDyadic?_some hx
  simp only [isNormal_iff_fields, hf, true_and]
  rw [abs_toRat_eq_fields hx]
  by_cases he : expField x = 0
  · simp only [he, ne_eq, not_true_eq_false, if_true, false_iff, not_le]
    have hfrac : (fracField x : ℚ) < (2 : ℚ) ^ fmt.fracWidth := by
      exact_mod_cast fracField_lt_pow2 x
    calc
      (fracField x : ℚ) * (2 : ℚ) ^ fmt.minSubnormalExponent <
          (2 : ℚ) ^ fmt.fracWidth * (2 : ℚ) ^ fmt.minSubnormalExponent :=
        mul_lt_mul_of_pos_right hfrac (zpow_pos (by norm_num) _)
      _ = (2 : ℚ) ^ fmt.minNormalExponent := normal_scale fmt _
  · simp only [he, ne_eq, not_false_eq_true, if_false, true_iff]
    have hemin : fmt.minNormalExponent ≤ (expField x : ℤ) - fmt.exponentBias := by
      change 1 - (fmt.exponentBias : ℤ) ≤ (expField x : ℤ) - fmt.exponentBias
      omega
    calc
      (2 : ℚ) ^ fmt.minNormalExponent ≤
          (2 : ℚ) ^ ((expField x : ℤ) - fmt.exponentBias) :=
        zpow_le_zpow_right₀ (by norm_num) hemin
      _ = (2 : ℚ) ^ fmt.fracWidth *
          (2 : ℚ) ^ ((expField x : ℤ) - fmt.exponentBias - fmt.fracWidth) :=
        (normal_scale fmt _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _))
        (zpow_nonneg (by norm_num) _)

/-- Zero classification of a decoded value is exactly numerical zero. -/
theorem isZero_iff_toRat_eq_zero {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    isZero x = true ↔ d.toRat = 0 := by
  rw [isZero_eq_beq_zero_of_toDyadic?_some hx, beq_iff_eq,
    Numerics.Dyadic.toRat_eq_zero_iff]

/-- Subnormal classification is precisely positive magnitude below the normal threshold. -/
theorem isSubnormal_iff_abs_toRat {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    isSubnormal x = true ↔
      0 < |d.toRat| ∧ |d.toRat| < (2 : ℚ) ^ fmt.minNormalExponent := by
  have hf := isFinite_eq_true_of_toDyadic?_some hx
  have hn := isNormal_iff_le_abs_toRat hx
  have hz := isZero_iff_toRat_eq_zero hx
  constructor
  · intro hs
    constructor
    · apply abs_pos.mpr
      intro hd
      have := isSubnormal_eq_false_of_isZero (hz.mpr hd)
      simp [hs] at this
    · apply lt_of_not_ge
      intro hd
      have := ((isNormal_iff x).mp (hn.mpr hd)).2.2
      simp [hs] at this
  · rintro ⟨hpos, hlt⟩
    have hzero : isZero x = false := by
      apply Bool.eq_false_iff.mpr
      intro hzero
      exact (abs_pos.mp hpos) (hz.mp hzero)
    have hnormal : isNormal x = false :=
      Bool.eq_false_iff.mpr fun h => (not_le.mpr hlt) (hn.mp h)
    simpa [hf, hzero, hnormal] using (isFinite_eq_zero_or_subnormal_or_normal x).symm

/-- Normality depends on the exact finite denotation, with NaNs and infinities excluded. -/
theorem isNormal_iff_exists_toDyadic (x : Model fmt) :
    isNormal x = true ↔ ∃ d, toDyadic? x = some d ∧
      (2 : ℚ) ^ fmt.minNormalExponent ≤ |d.toRat| := by
  constructor
  · intro hn
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite ((isNormal_iff x).mp hn).1
    exact ⟨d, hd, (isNormal_iff_le_abs_toRat hd).mp hn⟩
  · rintro ⟨d, hd, hn⟩
    exact (isNormal_iff_le_abs_toRat hd).mpr hn

/-- A subnormal is finite, with magnitude strictly between zero and the normal threshold. -/
theorem isSubnormal_iff_exists_toDyadic (x : Model fmt) :
    isSubnormal x = true ↔ ∃ d, toDyadic? x = some d ∧
      0 < |d.toRat| ∧ |d.toRat| < (2 : ℚ) ^ fmt.minNormalExponent := by
  constructor
  · intro hs
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite (isFinite_of_isSubnormal hs)
    exact ⟨d, hd, (isSubnormal_iff_abs_toRat hd).mp hs⟩
  · rintro ⟨d, hd, hs⟩
    exact (isSubnormal_iff_abs_toRat hd).mpr hs

/-- Real-valued normality uses the declared bias, independently of encoding policy. -/
theorem isNormal_iff_le_abs_toReal (x : Model fmt) :
    isNormal x = true ↔ isFinite x = true ∧
      (2 : ℝ) ^ fmt.minNormalExponent ≤ |toReal x| := by
  have hpow : (2 : ℝ) ^ fmt.minNormalExponent =
      (↑((2 : ℚ) ^ fmt.minNormalExponent) : ℝ) := by
    simp only [Rat.cast_zpow, Rat.cast_ofNat]
  rw [hpow]
  constructor
  · intro hn
    have hf := ((isNormal_iff x).mp hn).1
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hf
    refine ⟨hf, ?_⟩
    simp only [toReal_eq, hd, ← Numerics.Dyadic.cast_toRat]
    exact_mod_cast (isNormal_iff_le_abs_toRat hd).mp hn
  · rintro ⟨hf, hn⟩
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hf
    apply (isNormal_iff_le_abs_toRat hd).mpr
    simp only [toReal_eq, hd, ← Numerics.Dyadic.cast_toRat] at hn
    exact_mod_cast hn

/-- Real-valued subnormality is strict positive magnitude below the normal threshold. -/
theorem isSubnormal_iff_abs_toReal (x : Model fmt) :
    isSubnormal x = true ↔ isFinite x = true ∧
      0 < |toReal x| ∧ |toReal x| < (2 : ℝ) ^ fmt.minNormalExponent := by
  have hpow : (2 : ℝ) ^ fmt.minNormalExponent =
      (↑((2 : ℚ) ^ fmt.minNormalExponent) : ℝ) := by
    simp only [Rat.cast_zpow, Rat.cast_ofNat]
  rw [hpow]
  constructor
  · intro hs
    have hf := isFinite_of_isSubnormal hs
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hf
    refine ⟨hf, ?_⟩
    simp only [toReal_eq, hd, ← Numerics.Dyadic.cast_toRat]
    exact_mod_cast (isSubnormal_iff_abs_toRat hd).mp hs
  · rintro ⟨hf, hs⟩
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hf
    apply (isSubnormal_iff_abs_toRat hd).mpr
    simp only [toReal_eq, hd, ← Numerics.Dyadic.cast_toRat] at hs
    exact_mod_cast hs

end FloatLib.Floats.Formats.BinaryInterchange.Model
