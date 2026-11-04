/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel

/-!
# Multiplication and division through Lean's floating-point model

Lean's `roundWithAccuracy` requires an exponent that needs no left shift. That holds if and only if
the exponent is at or below the format's minimum exponent or the mantissa has at least as many
bits as the precision. Finite nonzero values unpacked from format words satisfy it, their products
keep it, and `divCore` satisfies it for all nonzero mantissas. When the provisional quotient is
zero, the sign, the selected exponent, and the remainder accuracy still determine the rounding.

So `toReal_ofModel_mul_toModel_eq_roundAt` and `toReal_ofModel_div_toModel_eq_roundAt` need only
a conventional IEEE descriptor and a finite result, plus a finite divisor for division. Arbitrary
unpacked operands need not satisfy the precondition, which is why
`toReal_ofModel_mul_finite_eq_roundAt` keeps its exponent hypothesis. These bridges are checked
against the logical floating-point model shipped with Lean.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/--
If two nonzero mantissas and their exponents satisfy Lean's `roundWithAccuracy` precondition, so
do the product of the mantissas and the sum of the exponents.
-/
theorem add_le_targetExponent_totalExponent_mul (spec : Float.Model.Format)
    {mantissa₁ mantissa₂ : Nat} {exponent₁ exponent₂ : Int}
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂)
    (hle₁ :
      exponent₁ ≤ spec.targetExponent (Float.Model.totalExponent mantissa₁ exponent₁))
    (hle₂ :
      exponent₂ ≤ spec.targetExponent (Float.Model.totalExponent mantissa₂ exponent₂)) :
    exponent₁ + exponent₂ ≤
      spec.targetExponent
        (Float.Model.totalExponent (mantissa₁ * mantissa₂) (exponent₁ + exponent₂)) := by
  rw [le_targetExponent_totalExponent_iff] at hle₁ hle₂ ⊢
  have hmin : spec.minExponent ≤ 0 := by
    have hwidth := spec.hm
    have hpow : (1 : Int) ≤ 2 ^ (spec.exponentBits - 1) := by
      exact_mod_cast Nat.two_pow_pos (spec.exponentBits - 1)
    simp only [Float.Model.Format.minExponent, Float.Model.Format.mantissaBits]
    omega
  rcases hle₁ with hle₁ | hle₁
  · rcases hle₂ with hle₂ | hle₂
    · exact Or.inl (by omega)
    · exact Or.inr (hle₂.trans (Nat.le_mul_of_pos_left mantissa₂ hmantissa₁))
  · exact Or.inr (hle₁.trans (Nat.le_mul_of_pos_right mantissa₁ hmantissa₂))

/--
A finite nonzero value unpacked from a format word satisfies Lean's `roundWithAccuracy`
precondition: a subnormal has the minimum exponent and a normal has its leading bit set.
-/
theorem le_targetExponent_totalExponent_of_toModel_eq_finite {fmt : FloatFormat} (x : Model fmt)
    {sign : Sign} {mantissa : Nat} {exponent : Int} {hmantissa : 0 < mantissa}
    (hx : toModel x = .finite sign mantissa exponent hmantissa) :
    exponent ≤
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent mantissa exponent) := by
  rw [le_targetExponent_totalExponent_iff, toModel_minExponent]
  change exponent ≤ FloatFormat.ieeeMinSubnormalExponent fmt ∨ 2 ^ fmt.fracWidth ≤ mantissa
  have hdecode := ieeeToDyadic?_eq_unpackedToDyadic?_toModel x
  rw [hx] at hdecode
  simp only [unpackedToDyadic?, ieeeToDyadic?] at hdecode
  split_ifs at hdecode
  · simp only [Option.some.injEq, Numerics.Dyadic.mk.injEq] at hdecode
    exact absurd hdecode.2.1.symm hmantissa.ne'
  · simp only [Option.some.injEq, Numerics.Dyadic.mk.injEq] at hdecode
    exact Or.inl hdecode.2.2.symm.le
  · simp only [Option.some.injEq, Numerics.Dyadic.mk.injEq] at hdecode
    refine Or.inr ?_
    rw [← hdecode.2.1, pow2_eq_two_pow]
    exact Nat.le_add_right _ _

/--
For a conventional IEEE descriptor, Lean core's finiteness test on the unpacked value agrees with
`isFinite` on the format word.
-/
theorem isFinite_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt) :
    (toModel x).isFinite = isFinite x := by
  rw [← toDyadic?_isSome_eq_isFinite, toDyadic?_ieee_eq_model fmt hfmt x]
  cases toModel x <;> rfl

/-- The word packed from Lean's NaN is not finite under a conventional IEEE descriptor. -/
theorem isFinite_ofModel_notANumber (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    isFinite (ofModel fmt .notANumber) = false := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hexponent : expField (ofModel fmt .notANumber) = FloatFormat.expAllOnesNat fmt := by
    rw [← unpackExponent_toNat]
    unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack packedNaN
    rw [unpackExponent_packComponents]
    exact toNat_neg_one_exponentBits fmt
  simp [isFinite, IEEE.isFinite, hencoding, hexponent]

/--
For a conventional IEEE descriptor and a finite result, Lean core's unpacked multiplication of the
values unpacked from two format words has the same independent nearest-even real semantics as
`Model.mul`.

The finite result already excludes NaN and infinite factors, and signed zeros are allowed. Unlike
`toReal_ofModel_mul_finite_eq_roundAt`, there is no exponent premise. Values unpacked from format
words satisfy the `roundWithAccuracy` precondition, while arbitrary unpacked operands need not.
-/
theorem toReal_ofModel_mul_toModel_eq_roundAt {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt)
            (toModel x) (toModel y))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt)
            (toModel x) (toModel y))) =
      roundAt fmt (toReal x * toReal y) := by
  have hnan := isFinite_ofModel_notANumber fmt hfmt
  have hzero := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  have hinfinity := isFinite_ofModel_infinity fmt
    (FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt)
  obtain ⟨ux, hux⟩ : ∃ ux, toModel x = ux := ⟨_, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ uy, toModel y = uy := ⟨_, rfl⟩
  rw [hux, huy] at hfinite
  rw [toReal_eq_unpackedToReal_toModel hfmt x, toReal_eq_unpackedToReal_toModel hfmt y,
    hux, huy]
  cases ux with
  | notANumber => cases uy <;> simp [Float.Model.UnpackedFloat.mul, hnan] at hfinite
  | infinity _ =>
    cases uy <;> simp [Float.Model.UnpackedFloat.mul, hnan, hinfinity] at hfinite
  | zero sign₁ =>
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.mul, hnan] at hfinite
    | infinity _ => simp [Float.Model.UnpackedFloat.mul, hnan] at hfinite
    | zero sign₂ =>
      simp only [Float.Model.UnpackedFloat.mul, unpackedToReal_zero, zero_mul, roundAt_zero]
      exact toReal_ofModel_zero fmt hzero _
    | finite sign₂ mantissa₂ exponent₂ hmantissa₂ =>
      simp only [Float.Model.UnpackedFloat.mul, unpackedToReal_zero, zero_mul, roundAt_zero]
      exact toReal_ofModel_zero fmt hzero _
  | finite sign₁ mantissa₁ exponent₁ hmantissa₁ =>
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.mul, hnan] at hfinite
    | infinity _ => simp [Float.Model.UnpackedFloat.mul, hinfinity] at hfinite
    | zero sign₂ =>
      simp only [Float.Model.UnpackedFloat.mul, unpackedToReal_zero, mul_zero, roundAt_zero]
      exact toReal_ofModel_zero fmt hzero _
    | finite sign₂ mantissa₂ exponent₂ hmantissa₂ =>
      exact toReal_ofModel_mul_finite_eq_roundAt fmt hfmt sign₁ sign₂ mantissa₁ mantissa₂
        exponent₁ exponent₂ hmantissa₁ hmantissa₂
        (add_le_targetExponent_totalExponent_mul _ hmantissa₁ hmantissa₂
          (le_targetExponent_totalExponent_of_toModel_eq_finite x hux)
          (le_targetExponent_totalExponent_of_toModel_eq_finite y huy))
        hfinite

/--
For a conventional IEEE descriptor, a finite divisor, and a finite result, Lean core's unpacked
division of the values unpacked from two format words has the same independent nearest-even real
semantics as `Model.div`.

`hy` excludes a NaN or infinite divisor, and the finite result excludes a NaN or infinite dividend
and a zero divisor. A finite dividend over an infinite divisor is a signed zero, but the equation
would then hold only because `toReal` maps infinity to `0`, so that case stays outside. A zero
dividend gives a signed zero, and finite nonzero operands reduce to
`toReal_ofModel_div_finite_eq_roundAt`.
-/
theorem toReal_ofModel_div_toModel_eq_roundAt {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hy : isFinite y = true)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
            (toModel x) (toModel y))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
            (toModel x) (toModel y))) =
      roundAt fmt (toReal x / toReal y) := by
  have hnan := isFinite_ofModel_notANumber fmt hfmt
  have hzero := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  have hinfinity := isFinite_ofModel_infinity fmt
    (FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt)
  obtain ⟨ux, hux⟩ : ∃ ux, toModel x = ux := ⟨_, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ uy, toModel y = uy := ⟨_, rfl⟩
  rw [← isFinite_toModel hfmt, huy] at hy
  rw [hux, huy] at hfinite
  rw [toReal_eq_unpackedToReal_toModel hfmt x, toReal_eq_unpackedToReal_toModel hfmt y,
    hux, huy]
  cases uy with
  | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hy
  | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hy
  | zero _ =>
    cases ux <;> simp [Float.Model.UnpackedFloat.div, hnan, hinfinity] at hfinite
  | finite sign₂ mantissa₂ exponent₂ hmantissa₂ =>
    cases ux with
    | notANumber => simp [Float.Model.UnpackedFloat.div, hnan] at hfinite
    | infinity _ => simp [Float.Model.UnpackedFloat.div, hinfinity] at hfinite
    | zero sign₁ =>
      simp only [Float.Model.UnpackedFloat.div, unpackedToReal_zero, zero_div, roundAt_zero]
      exact toReal_ofModel_zero fmt hzero _
    | finite sign₁ mantissa₁ exponent₁ hmantissa₁ =>
      exact toReal_ofModel_div_finite_eq_roundAt fmt hfmt sign₁ sign₂
        mantissa₁ mantissa₂ exponent₁ exponent₂ hmantissa₁ hmantissa₂ hfinite

end Model
end FloatLib.Floats.Formats.BinaryInterchange
