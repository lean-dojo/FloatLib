/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Addition.Proof

/-!
# Verified wide-limb fused multiply-add

An accepted result is the compact finite kernel `FiniteKernel.fma?` on the operand models
(`fmaNormal?_refines`): the exact limb product is the product of the decoded significands, and the
alignment core computes the unsigned-scale exact sum `FiniteScaleAdd.roundSum` that
`FiniteKernel.fmaComponentsImpl` evaluates. `toModel_fma` then closes with the reference operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- An accepted normal fused multiply-add is the compact finite kernel on the operand models. -/
theorem fmaNormal?_refines (h : Eligible fmt) (x y z r : Value fmt)
    (hr : fmaNormal? fmt x y z = some r) :
    FiniteKernel.fma? (toModel x) (toModel y) (toModel z) = some (toModel r) := by
  unfold fmaNormal? at hr
  by_cases hcond : (expWord x == 0 || expWord x == expAllOnes fmt ||
      expWord y == 0 || expWord y == expAllOnes fmt ||
      expWord z == 0 || expWord z == expAllOnes fmt) = true
  · rw [ite_eq_left hcond] at hr
    exact absurd hr (by simp)
  · rw [ite_eq_right hcond] at hr
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hcond
    obtain ⟨⟨⟨⟨⟨hx0, hxAll⟩, hy0⟩, hyAll⟩, hz0⟩, hzAll⟩ := hcond
    obtain ⟨hxe0, hxeFinite⟩ := normalExponent_of_expWord h x hx0 hxAll
    obtain ⟨hye0, hyeFinite⟩ := normalExponent_of_expWord h y hy0 hyAll
    obtain ⟨hze0, hzeFinite⟩ := normalExponent_of_expWord h z hz0 hzAll
    have hxBounds := normalMantissa_bounds x
    have hyBounds := normalMantissa_bounds y
    have hzBounds := normalMantissa_bounds z
    have hproduct : ((normalMantissa x).mul (normalMantissa y)).toNat =
        (normalMantissa x).toNat * (normalMantissa y).toNat := LimbArray.toNat_mul _ _
    have hproductLow : 2 ^ fmt.fracWidth ≤ ((normalMantissa x).mul (normalMantissa y)).toNat := by
      rw [hproduct]
      calc
        2 ^ fmt.fracWidth = 2 ^ fmt.fracWidth * 1 := (Nat.mul_one _).symm
        _ ≤ (normalMantissa x).toNat * (normalMantissa y).toNat :=
          Nat.mul_le_mul hxBounds.1 (by have := Nat.two_pow_pos fmt.fracWidth; omega)
    have hsum := alignAndRound?_refines h 0 (Bool.xor (signBit x) (signBit y))
      ((normalMantissa x).mul (normalMantissa y)) ((expWord x).toNat - 1 + ((expWord y).toNat - 1))
      (signBit z) (normalMantissa z) ((expWord z).toNat - 1 + FiniteKernel.finiteScaleOffset fmt)
      hproductLow hzBounds.1 r hr
    unfold FiniteKernel.fma?
    rw [decode?_normal h x hxeFinite hxe0, decode?_normal h y hyeFinite hye0,
      decode?_normal h z hzeFinite hze0]
    simp only [Option.some.injEq]
    rw [← FiniteKernel.fmaComponentsImpl_eq]
    unfold FiniteKernel.fmaComponentsImpl
    rw [ite_eq_left h.isIEEE, hsum, hproduct]
    have hxe0' : (expField x == 0) = false := by simpa using hxe0
    have hye0' : (expField y == 0) = false := by simpa using hye0
    have hze0' : (expField z == 0) = false := by simpa using hze0
    simp only [FiniteKernel.scale, hxe0', hye0', hze0', Bool.false_eq_true, ite_false]
    rfl

/-- Wide-limb fused multiply-add is the reference fused multiply-add of the operand models. -/
theorem toModel_fma (h : Eligible fmt) (x y z : Value fmt) :
    toModel (fma fmt x y z) = Spec.fma (toModel x) (toModel y) (toModel z) := by
  unfold fma
  cases hfast : fmaNormal? fmt x y z with
  | none =>
      simp only
      rw [toModel_ofModel]
  | some r =>
      simp only
      exact (spec_fma_of_fma?_eq_some _ _ _ _ (fmaNormal?_refines h x y z r hfast)).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
