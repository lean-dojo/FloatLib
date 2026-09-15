/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Multiplication.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Round.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Finite.Proof

/-!
# Verified wide-limb multiplication

An accepted normal product is the compact finite kernel `FiniteKernel.mul?` on the models of the
operands (`mulNormal?_refines`): the operands decode to their limb significands
(`Core.Proof.decode?_toModel`), the schoolbook product is exact (`LimbArray.toNat_mul`), and the
limb rounder is the exact rounder (`Round.Proof`). The total operation then equals `Model.Spec.mul`
because both its branches do: the accepted branch through `Finite.Proof.spec_mul_of_mul?_eq_some`,
the declined branch through the codec laws.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- An accepted normal product is the compact finite multiplication of the operand models. -/
theorem mulNormal?_refines (h : Eligible fmt) (x y r : Value fmt)
    (hr : mulNormal? fmt x y = some r) :
    FiniteKernel.mul? (toModel x) (toModel y) = some (toModel r) := by
  unfold mulNormal? at hr
  by_cases hcond : (expWord x == 0 || expWord x == expAllOnes fmt ||
      expWord y == 0 || expWord y == expAllOnes fmt) = true
  · rw [ite_eq_left hcond] at hr
    exact absurd hr (by simp)
  · rw [ite_eq_right hcond] at hr
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hcond
    obtain ⟨⟨⟨hx0, hxAll⟩, hy0⟩, hyAll⟩ := hcond
    obtain ⟨hxe0, hxeFinite⟩ := normalExponent_of_expWord h x hx0 hxAll
    obtain ⟨hye0, hyeFinite⟩ := normalExponent_of_expWord h y hy0 hyAll
    have hxBounds := normalMantissa_bounds x
    have hyBounds := normalMantissa_bounds y
    have hxNe : (normalMantissa x).toNat ≠ 0 := by
      have := Nat.two_pow_pos fmt.fracWidth
      omega
    have hyNe : (normalMantissa y).toNat ≠ 0 := by
      have := Nat.two_pow_pos fmt.fracWidth
      omega
    have hproduct : ((normalMantissa x).mul (normalMantissa y)).toNat =
        (normalMantissa x).toNat * (normalMantissa y).toNat := LimbArray.toNat_mul _ _
    have hproductNe : ((normalMantissa x).mul (normalMantissa y)).toNat ≠ 0 := by
      rw [hproduct]
      exact Nat.mul_ne_zero hxNe hyNe
    have hjammed := roundNormal?_map_toModel h.exp_le (Bool.xor (signBit x) (signBit y))
      ((normalMantissa x).mul (normalMantissa y)) 0
      ((expWord x).toNat - 1 + ((expWord y).toNat - 1)) hproductNe
    rw [hr, Option.map_some] at hjammed
    have hround := round_eq_of_roundJammed (Bool.xor (signBit x) (signBit y))
      ((normalMantissa x).mul (normalMantissa y)).toNat 0
      ((expWord x).toNat - 1 + ((expWord y).toNat - 1)) hproductNe (Or.inl rfl) (toModel r)
      (by rw [shiftRightJam_zero]; exact hjammed.symm)
    unfold FiniteKernel.mul?
    rw [decode?_toModel x h.isIEEE h.exp_le hxeFinite, decode?_toModel y h.isIEEE h.exp_le hyeFinite,
      decodeMantissa_eq_normalMantissa x hxe0,
      decodeMantissa_eq_normalMantissa y hye0]
    have hx0' : ((normalMantissa x).toNat == 0) = false := by simpa using hxNe
    have hy0' : ((normalMantissa y).toNat == 0) = false := by simpa using hyNe
    have hxe0' : (expField x == 0) = false := by simpa using hxe0
    have hye0' : (expField y == 0) = false := by simpa using hye0
    simp only [hx0', hy0', Bool.or_self, Bool.false_eq_true, ite_false, h.isIEEE, ite_true,
      FiniteKernel.scale, hxe0', hye0', Option.some.injEq]
    rw [← hround, hproduct]
    rfl

/-- Wide-limb multiplication is the reference multiplication of the operand models. -/
theorem toModel_mul (h : Eligible fmt) (x y : Value fmt) :
    toModel (mul fmt x y) = Spec.mul (toModel x) (toModel y) := by
  unfold mul
  cases hfast : mulNormal? fmt x y with
  | none =>
      simp only
      rw [toModel_ofModel]
  | some r =>
      simp only
      exact (spec_mul_of_mul?_eq_some _ _ _ (mulNormal?_refines h x y r hfast)).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
