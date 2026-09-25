/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Sqrt.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.SqrtNormalRounding

/-!
# Correctness of wide-limb square root

The integer candidate is certified by square inequalities. For positive normal inputs, its
exact root and remainder implement the shared square-root rounding theorem. All other inputs
retain the reference operation, including its signed-zero and NaN payload behavior.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- The direct significand read agrees with the stored normal significand. -/
theorem sqrtMantissa_eq_normalMantissa (x : Value fmt) :
    sqrtMantissa x = (normalMantissa x).toNat := by
  unfold sqrtMantissa
  rw [normalMantissa_toNat, LimbArray.toNatImpl_eq, Nat.shiftLeft_eq, Nat.one_mul,
    Model.fracField_eq_fracFieldImpl_apply, Model.fracFieldImpl, toNatBits_toModel,
    FloatFormat.fracMaskNat]

private theorem toModel_pack_sqrt_fields (h : fmt.expWidth ≤ 32) (exponent fraction : Nat) :
    toModel (pack fmt false (UInt32.ofNat exponent)
      (LimbArray.ofNat fraction (limbCount fmt))) =
      Model.ofFields fmt false exponent fraction := by
  have hfrac : fmt.fracWidth ≤ 32 * limbCount fmt := by
    have := bitWidth_le_limbBits fmt
    have := bitWidth_eq fmt
    omega
  rw [toModel_pack _ _ _ h, UInt32.toNat_ofNat', LimbArray.toNat_ofNat, LimbArray.radix_eq]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), ← pow_mul,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hfrac)]
  simpa only [Model.signBit_ofFields, Model.expField_ofFields, Model.fracField_ofFields] using
    Model.ofFields_signBit_expField_fracField (Model.ofFields fmt false exponent fraction)

private theorem sqrt_model_minExponent (fmt : FloatFormat) :
    (FloatFormat.toModel fmt).minExponent = 1 - (fmt.bias : Int) - fmt.fracWidth := by
  have hbias : (fmt.bias : Int) = 2 ^ (fmt.expWidth - 1) - 1 := by
    unfold FloatFormat.bias
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rfl
  unfold Float.Model.Format.minExponent Float.Model.Format.mantissaBits FloatFormat.toModel
  rw [hbias]
  push_cast
  omega

private theorem sqrt_normal_target (fmt : FloatFormat) (m e : Nat)
    (he : 0 < e) (hm : m.log2 = fmt.fracWidth) :
    min (((e : Int) - (fmt.bias + fmt.fracWidth : Nat)).ediv 2)
      ((FloatFormat.toModel fmt).targetExponent
        ((Float.Model.totalExponent m ((e : Int) - (fmt.bias + fmt.fracWidth : Nat)) + 1).ediv
          2)) =
      ((e + fmt.bias) / 2 : Nat) - (fmt.bias : Int) - fmt.fracWidth := by
  have hbias := fmt.bias_pos
  have hfrac := fmt.fracWidth_pos
  unfold Float.Model.Format.targetExponent Float.Model.totalExponent
  rw [hm, sqrt_model_minExponent]
  simp only [Float.Model.Format.mantissaBits, FloatFormat.toModel]
  push_cast
  change min (((e : Int) - (fmt.bias + fmt.fracWidth)) / 2)
      (max
        ((((fmt.fracWidth : Int) + 1 + ((e : Int) - (fmt.bias + fmt.fracWidth)) + 1) / 2) -
          (1 + fmt.fracWidth))
        (1 - fmt.bias - fmt.fracWidth)) =
    ((e : Int) + fmt.bias) / 2 - fmt.bias - fmt.fracWidth
  have htotal :
      ((fmt.fracWidth : Int) + 1 + ((e : Int) - (fmt.bias + fmt.fracWidth)) + 1) / 2 -
        (1 + fmt.fracWidth) =
      ((e : Int) + fmt.bias) / 2 - fmt.bias - fmt.fracWidth := by omega
  have hnormal :
      1 - (fmt.bias : Int) - fmt.fracWidth ≤
        ((e : Int) + fmt.bias) / 2 - fmt.bias - fmt.fracWidth := by omega
  have htarget :
      ((e : Int) + fmt.bias) / 2 - fmt.bias - fmt.fracWidth ≤
        ((e : Int) - (fmt.bias + fmt.fracWidth)) / 2 := by omega
  rw [htotal, max_eq_left hnormal, min_eq_right htarget]

private theorem sqrt_normal_shift (fmt : FloatFormat) (e : Nat) :
    (((e : Int) - (fmt.bias + fmt.fracWidth : Nat)) -
      2 * (((e + fmt.bias) / 2 : Nat) - (fmt.bias : Int) - fmt.fracWidth)).toNat =
      fmt.fracWidth + (e + fmt.bias) % 2 := by
  push_cast
  omega

private theorem sqrtNormalValue_eq_model (h : Eligible fmt) (exponent mantissa : Nat)
    (he : 0 < exponent) (hefinite : exponent < fmt.expAllOnesNat)
    (hlower : 2 ^ fmt.fracWidth ≤ mantissa)
    (hupper : mantissa < 2 ^ (fmt.fracWidth + 1)) :
    toModel (sqrtNormalValue fmt exponent mantissa) =
      Model.ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
          (.finite .positive mantissa
            ((exponent : Int) - (fmt.bias + fmt.fracWidth : Nat))
            ((Nat.two_pow_pos _).trans_le hlower))) := by
  have hm : 0 < mantissa := (Nat.two_pow_pos _).trans_le hlower
  have hleading : mantissa.log2 = fmt.fracWidth :=
    (Nat.log2_eq_iff hm.ne').2 ⟨hlower, hupper⟩
  have hbias := fmt.bias_pos
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hround := Model.ofModel_sqrt_finite_positive_eq_ofFields fmt mantissa
    (fmt.fracWidth + (exponent + fmt.bias) % 2) ((exponent + fmt.bias) / 2)
    ((exponent : Int) - (fmt.bias + fmt.fracWidth : Nat)) hm
    (by omega) (by omega) (by omega) (by omega)
    (sqrt_normal_target fmt mantissa exponent he hleading)
    (sqrt_normal_shift fmt exponent)
  rw [hround]
  unfold sqrtNormalValue
  dsimp only
  rw [FixedWord.IntegerSquareRoot.sqrtRem_eq]
  dsimp only
  rw [toModel_pack_sqrt_fields h.exp_le]
  simp only [Nat.shiftLeft_eq, Nat.one_mul, pow2_eq_two_pow, beq_iff_eq, ← pow_succ]
  simp only [ite_sub, Nat.sub_self]

private theorem sqrt_toModel_positive_normal (h : Eligible fmt) (x : Value fmt)
    (hsign : signBit x = false) (hezero : expField x ≠ 0)
    (hefinite : expField x ≠ fmt.expAllOnesNat) (hm : 0 < sqrtMantissa x) :
    Model.toModel (toModel x) =
      .finite .positive (sqrtMantissa x)
        ((expField x : Int) - (fmt.bias + fmt.fracWidth : Nat)) hm := by
  have hdyadic :
      Model.toDyadic? (toModel x) =
        some ({ negative := false
                significand := sqrtMantissa x
                exponent := (expField x : Int) - (fmt.bias + fmt.fracWidth : Nat) } :
          Numerics.Dyadic) := by
    rw [FiniteKernel.toDyadic_eq_decode, decode?_toModel x h.isIEEE h.exp_le hefinite,
      decodeMantissa_eq_normalMantissa x hezero, ← sqrtMantissa_eq_normalMantissa]
    simp [FiniteKernel.Components.toDyadic, FiniteKernel.dyadicExponent, hsign, hezero,
      hm.ne', FloatFormat.exponentBias_eq_bias_of_isIEEE fmt h.isIEEE]
    omega
  have hieee :
      Model.ieeeToDyadic? (toModel x) =
        some ({ negative := false
                significand := sqrtMantissa x
                exponent := (expField x : Int) - (fmt.bias + fmt.fracWidth : Nat) } :
          Numerics.Dyadic) := by
    simpa [Model.toDyadic?, h.isIEEE] using hdyadic
  simpa [Model.modelSign] using
    Model.toModel_eq_finite_of_ieeeToDyadic?_eq_some (toModel x) false (sqrtMantissa x)
      ((expField x : Int) - (fmt.bias + fmt.fracWidth : Nat)) hm.ne' hieee

/-- Every accepted normal candidate has exactly the reference square-root encoding. -/
theorem sqrtNormal?_refines (h : Eligible fmt) (x result : Value fmt)
    (hresult : sqrtNormal? fmt x = some result) :
    toModel result = Spec.sqrt (toModel x) := by
  have hsign : signBit x = false := by
    by_contra hs
    have hs' : signBit x = true := Bool.eq_true_of_not_eq_false hs
    simp [sqrtNormal?, hs'] at hresult
  have hezero : expWord x ≠ 0 := by
    intro he
    simp [sqrtNormal?, hsign, he] at hresult
  have hefinite : expWord x ≠ expAllOnes fmt := by
    intro he
    simp [sqrtNormal?, hsign, he] at hresult
  have hvalue : result = sqrtNormalValue fmt (expField x) (sqrtMantissa x) := by
    simpa [sqrtNormal?, hsign, hezero, hefinite, expField] using hresult.symm
  have hexp := normalExponent_of_expWord h x hezero hefinite
  have hexpLt : expField x < fmt.expAllOnesNat := by
    have := expField_lt x h.exp_le
    unfold FloatFormat.expAllOnesNat at *
    omega
  have hbounds : 2 ^ fmt.fracWidth ≤ sqrtMantissa x ∧
      sqrtMantissa x < 2 ^ (fmt.fracWidth + 1) := by
    rw [sqrtMantissa_eq_normalMantissa]
    exact normalMantissa_bounds x
  have hm : 0 < sqrtMantissa x := (Nat.two_pow_pos _).trans_le hbounds.1
  have hfinite : Model.isFinite (toModel x) = true := by
    rw [isFinite_toModel x h.isIEEE h.exp_le]
    simpa using hexp.2
  have hnonzero : Model.isZero (toModel x) = false := by
    have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp h.isIEEE).1
    simp [Model.isZero, hencoding, Model.IEEE.isZero, ← expField_eq x h.exp_le, hexp.1]
  have hmodelSign : Model.signBit (toModel x) = false := by
    rw [← signBit_eq]
    exact hsign
  rw [hvalue, Spec.sqrt_eq_model h.isIEEE (toModel x) hfinite hnonzero hmodelSign,
    sqrt_toModel_positive_normal h x hsign hexp.1 hexp.2 hm]
  exact sqrtNormalValue_eq_model h (expField x) (sqrtMantissa x)
    (Nat.pos_of_ne_zero hexp.1) hexpLt hbounds.1 hbounds.2

/--
The general wide-limb square root agrees with the public specification on every eligible value.
The equality includes exact rounding, special values, signed zeros, and NaN payloads.
-/
theorem toModel_sqrt (h : Eligible fmt) (x : Value fmt) :
    toModel (sqrt fmt x) = Spec.sqrt (toModel x) := by
  unfold sqrt
  cases hc : sqrtNormal? fmt x with
  | none => exact toModel_ofModel _
  | some result => exact sqrtNormal?_refines h x result hc

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
