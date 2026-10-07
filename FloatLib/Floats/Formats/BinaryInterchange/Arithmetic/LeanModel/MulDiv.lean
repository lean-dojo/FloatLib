/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel

/-!
# Multiplication and division through Lean's floating-point model

Lean's `roundWithAccuracy` requires an exponent that needs no left shift. That holds exactly when
the exponent is at or below the format's minimum exponent or the mantissa has at least as many
bits as the precision. Finite nonzero values unpacked from format words satisfy it, their products
keep it, and `divCore` satisfies it for all nonzero mantissas. When the provisional quotient is
zero, the sign, the selected exponent, and the remainder accuracy still determine the rounding.

`toReal_ofModel_mul_toModel_eq_roundAt` and `toReal_ofModel_div_toModel_eq_roundAt` therefore
need only a conventional IEEE descriptor and a finite result, plus a finite divisor for division.
Arbitrary unpacked operands need not satisfy the precondition, so
`toReal_ofModel_mul_finite_eq_roundAt` keeps its exponent hypothesis. These bridges are checked
against the logical floating-point model shipped with Lean 4.34.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/--
Lean's `roundWithAccuracy` precondition holds exactly when the exponent is at or below the
format's minimum exponent or the mantissa has at least as many bits as the precision.
-/
theorem le_targetExponent_totalExponent_iff (spec : Float.Model.Format)
    (mantissa : Nat) (exponent : Int) :
    exponent ≤ spec.targetExponent (Float.Model.totalExponent mantissa exponent) ↔
      exponent ≤ spec.minExponent ∨ 2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa := by
  have hlog : spec.mantissaBitsWithoutImplicit ≤ mantissa.log2 ↔
      2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa := by
    rcases Nat.eq_zero_or_pos mantissa with rfl | hmantissa
    · have hwidth := spec.hm
      have hpow := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
      rw [Nat.log2_zero]
      omega
    · exact Nat.le_log2 hmantissa.ne'
  rw [← hlog]
  simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
    Float.Model.Format.mantissaBits]
  omega

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
For nonzero mantissas, the provisional quotient and exponent returned by Lean's `divCore` satisfy
the `roundWithAccuracy` precondition. Above the minimum exponent, the numerator is shifted far
enough for the provisional quotient to have at least as many bits as the precision, so a zero
provisional quotient occurs only at or below the minimum exponent.
-/
theorem divCore_exponent_le_targetExponent (spec : Float.Model.Format)
    {mantissa₁ mantissa₂ : Nat} (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂) :
    (Float.Model.UnpackedFloat.divCore spec mantissa₁ exponent₁ mantissa₂ exponent₂).2.1 ≤
      spec.targetExponent
        (Float.Model.totalExponent
          (Float.Model.UnpackedFloat.divCore spec mantissa₁ exponent₁ mantissa₂ exponent₂).1
          (Float.Model.UnpackedFloat.divCore
            spec mantissa₁ exponent₁ mantissa₂ exponent₂).2.1) := by
  rw [le_targetExponent_totalExponent_iff]
  obtain ⟨targetExponent, htarget⟩ : ∃ targetExponent : Int, targetExponent =
      min (exponent₁ - exponent₂)
        (spec.targetExponent
          (Float.Model.totalExponent mantissa₁ exponent₁ -
            Float.Model.totalExponent mantissa₂ exponent₂)) := ⟨_, rfl⟩
  obtain ⟨shiftAmount, hshift⟩ : ∃ shiftAmount : Nat, shiftAmount =
      (exponent₁ - exponent₂ - targetExponent).toNat := ⟨_, rfl⟩
  have hcore :
      Float.Model.UnpackedFloat.divCore spec mantissa₁ exponent₁ mantissa₂ exponent₂ =
        ((mantissa₁ <<< shiftAmount) / mantissa₂, targetExponent,
          accuracyOfFraction ((mantissa₁ <<< shiftAmount) % mantissa₂) mantissa₂) := by
    rw [hshift, htarget]
    rfl
  rw [hcore]
  change targetExponent ≤ spec.minExponent ∨
    2 ^ spec.mantissaBitsWithoutImplicit ≤ (mantissa₁ <<< shiftAmount) / mantissa₂
  by_cases hfloor : targetExponent ≤ spec.minExponent
  · exact Or.inl hfloor
  · refine Or.inr ?_
    simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
      Float.Model.Format.mantissaBits] at htarget
    have hlower := Nat.log2_self_le hmantissa₁.ne'
    have hupper := Nat.lt_log2_self (n := mantissa₂)
    rw [Nat.le_div_iff_mul_le hmantissa₂, Nat.shiftLeft_eq]
    calc
      2 ^ spec.mantissaBitsWithoutImplicit * mantissa₂ ≤
          2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ (mantissa₂.log2 + 1) :=
        Nat.mul_le_mul_left _ hupper.le
      _ = 2 ^ (spec.mantissaBitsWithoutImplicit + (mantissa₂.log2 + 1)) :=
        (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (mantissa₁.log2 + shiftAmount) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ mantissa₁.log2 * 2 ^ shiftAmount := Nat.pow_add _ _ _
      _ ≤ mantissa₁ * 2 ^ shiftAmount := Nat.mul_le_mul_right _ hlower

/--
For a conventional IEEE descriptor and an accuracy that represents `value` at a zero mantissa,
Lean's signed `roundWithAccuracy` result has the same real value as independent nearest-even
rounding of the represented signed real. This is the case excluded by the nonzero-mantissa premise
of `toReal_ofModel_roundWithAccuracy_eq_roundAt`, under the same exponent premise. The result is
a signed zero or a signed least subnormal, so no finiteness premise is needed.
-/
theorem toReal_ofModel_roundWithAccuracy_zero_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (exponent : Int) (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents 0 accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent)) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) sign 0 exponent accuracy)) =
      roundAt fmt
        ((if modelSignBit sign then (-1 : Real) else 1) *
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)) := by
  have hfloor : exponent ≤ FloatFormat.ieeeMinSubnormalExponent fmt := by
    rw [← toModel_minExponent]
    exact ((le_targetExponent_totalExponent_iff _ 0 exponent).mp hle).resolve_right
      (Nat.not_le.mpr (Nat.two_pow_pos _))
  have htarget :
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent) =
        FloatFormat.ieeeMinSubnormalExponent fmt := by
    apply targetExponent_eq_minSubnormal_of_lt_minNormal
    have hwidth := fmt.fracWidth_pos
    unfold FloatFormat.ieeeMinSubnormalExponent at hfloor
    unfold FloatFormat.ieeeMinNormalExponent
    simp only [Nat.log2_zero, Int.ofNat_eq_natCast, Nat.cast_zero] at hfloor ⊢
    omega
  have hnonneg : 0 ≤ value := by
    simpa using (accuracyRepresents_bounds haccuracy).1
  have hbelow : value < 1 := by
    simpa using (accuracyRepresents_bounds haccuracy).2
  obtain ⟨rounded, hrounded⟩ : ∃ rounded : Nat, rounded =
      (Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) 0 exponent accuracy).1.roundedMantissa := ⟨_, rfl⟩
  have hnearest :
      Int.ofNat rounded =
        nearestEven (value * bpow Numerics.binaryRadix
          (exponent - FloatFormat.ieeeMinSubnormalExponent fmt)) := by
    rw [hrounded, ← htarget]
    exact roundedMantissa_shiftToTargetExponent_eq_nearestEven
      fmt 0 exponent accuracy value haccuracy hle
  have hunitPos :=
    bpow.pos Numerics.binaryRadix (exponent - FloatFormat.ieeeMinSubnormalExponent fmt)
  have hunit :
      bpow Numerics.binaryRadix (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤ 1 := by
    have horder := (bpow_le_bpow_iff Numerics.binaryRadix
      (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) 0).mpr (by omega)
    simpa [bpow] using horder
  have hsmall : rounded ≤ pow2 fmt.fracWidth := by
    have hscaled :
        value * bpow Numerics.binaryRadix
            (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤ ((1 : Nat) : Real) := by
      rw [Nat.cast_one]
      exact (mul_le_mul hbelow.le hunit hunitPos.le zero_le_one).trans_eq (one_mul 1)
    have hone : rounded ≤ 1 :=
      Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaled))
    exact hone.trans (by rw [pow2_eq_two_pow]; exact Nat.one_le_two_pow)
  have hpositive :
      roundAt fmt (value * bpow Numerics.binaryRadix exponent) =
        (rounded : Real) *
          bpow Numerics.binaryRadix (FloatFormat.ieeeMinSubnormalExponent fmt) := by
    rcases hnonneg.eq_or_lt with hzero | hpos
    · subst hzero
      have hscaled :
          (0 : Real) * bpow Numerics.binaryRadix
              (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤ ((0 : Nat) : Real) := by
        simp
      have hroundedZero : rounded = 0 :=
        Nat.le_zero.mp
          (Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaled)))
      rw [zero_mul, roundAt_zero, hroundedZero, Nat.cast_zero, zero_mul]
    · have hexactPos : 0 < value * bpow Numerics.binaryRadix exponent :=
        mul_pos hpos (bpow.pos _ _)
      have hcexp :
          cexp Numerics.binaryRadix (fexpOf fmt) (value * bpow Numerics.binaryRadix exponent) =
            FloatFormat.ieeeMinSubnormalExponent fmt := by
        have hmagnitude :
            magnitude Numerics.binaryRadix (value * bpow Numerics.binaryRadix exponent) ≤
              FloatFormat.ieeeMinSubnormalExponent fmt := by
          apply magnitude_le_of_abs_lt_bpow _ _ _ hexactPos.ne'
          rw [abs_of_pos hexactPos]
          have horder := (bpow_le_bpow_iff Numerics.binaryRadix exponent
            (FloatFormat.ieeeMinSubnormalExponent fmt)).mpr hfloor
          exact (mul_lt_mul_of_pos_right hbelow (bpow.pos _ _)).trans_le
            ((one_mul _).trans_le horder)
        simp only [cexp, fexpOf, fltExp, FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]
        apply max_eq_right
        omega
      unfold roundAt FloatLib.Floats.Formats.Flocq.round FloatLib.Floats.Formats.Flocq.toReal
      rw [scaledMantissa, hcexp, mul_assoc, ← bpow.add_exp, ← sub_eq_add_neg, ← hnearest]
      norm_num
  have hroundAt :
      roundAt fmt
          ((if modelSignBit sign then (-1 : Real) else 1) *
            (value * bpow Numerics.binaryRadix exponent)) =
        (if modelSignBit sign then (-1 : Real) else 1) *
          ((rounded : Real) *
            bpow Numerics.binaryRadix (FloatFormat.ieeeMinSubnormalExponent fmt)) := by
    cases sign <;> simp [modelSignBit, hpositive, roundAt_neg]
  rw [hroundAt, roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt 0 exponent accuracy hle]
  rw [shiftToTargetExponent_eq_of_le_targetExponent fmt 0 exponent accuracy hle] at hrounded
  dsimp only at hrounded ⊢
  rw [← hrounded, htarget]
  exact toReal_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt sign rounded hsmall

/--
Lean's remainder classification locates a proper fraction relative to a zero integer quotient.
-/
private theorem accuracyRepresents_zero_accuracyOfFraction
    (numerator denominator : Nat) (hlt : numerator < denominator) :
    accuracyRepresents 0 (accuracyOfFraction numerator denominator)
      ((numerator : Real) / denominator) := by
  simpa only [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] using
    accuracyRepresents_accuracyOfFraction numerator denominator (Nat.zero_lt_of_lt hlt).ne'

/--
For a conventional IEEE descriptor, finite nonzero operands, and a finite result, Lean core's
unpacked division has the same independent nearest-even real semantics as `Model.div`.

This is `toReal_ofModel_div_finite_eq_roundAt` without its `divCore` premises. A zero provisional
quotient is rounded from its sign, selected exponent, and remainder accuracy by
`toReal_ofModel_roundWithAccuracy_zero_eq_roundAt`.
-/
theorem toReal_ofModel_div_finite_eq_roundAt_of_isFinite
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign)
    (mantissa₁ mantissa₂ : Nat)
    (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁)
    (hmantissa₂ : 0 < mantissa₂)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) =
      roundAt fmt
        (unpackedToReal (.finite sign₁ mantissa₁ exponent₁ hmantissa₁) /
          unpackedToReal (.finite sign₂ mantissa₂ exponent₂ hmantissa₂)) := by
  have hle := divCore_exponent_le_targetExponent
    (FloatFormat.toModel fmt) exponent₁ exponent₂ hmantissa₁ hmantissa₂
  by_cases hquotient :
      (Float.Model.UnpackedFloat.divCore
        (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂).1 = 0
  · let targetExponent :=
      min (exponent₁ - exponent₂)
        ((FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa₁ exponent₁ -
            Float.Model.totalExponent mantissa₂ exponent₂))
    let shiftAmount := (exponent₁ - exponent₂ - targetExponent).toNat
    let numerator := mantissa₁ <<< shiftAmount
    have hcore :
        Float.Model.UnpackedFloat.divCore
            (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂ =
          (numerator / mantissa₂, targetExponent,
            accuracyOfFraction (numerator % mantissa₂) mantissa₂) := by
      rfl
    rw [hcore] at hquotient hle
    dsimp only at hquotient hle
    rw [hquotient] at hle
    have hlt : numerator < mantissa₂ := (Nat.div_eq_zero_iff_lt hmantissa₂).mp hquotient
    have haccuracy :
        accuracyRepresents 0 (accuracyOfFraction (numerator % mantissa₂) mantissa₂)
          ((numerator : Real) / mantissa₂) := by
      rw [Nat.mod_eq_of_lt hlt]
      exact accuracyRepresents_zero_accuracyOfFraction numerator mantissa₂ hlt
    have hround :=
      toReal_ofModel_roundWithAccuracy_zero_eq_roundAt
        fmt hfmt (sign₁ / sign₂) targetExponent
        (accuracyOfFraction (numerator % mantissa₂) mantissa₂)
        ((numerator : Real) / mantissa₂) haccuracy hle
    change
      toReal
          (ofModel fmt
            (Float.Model.UnpackedFloat.roundWithAccuracy
              (FloatFormat.toModel fmt) (sign₁ / sign₂)
              (numerator / mantissa₂) targetExponent
              (accuracyOfFraction (numerator % mantissa₂) mantissa₂))) =
        _
    rw [hquotient, hround]
    congr 1
    have htargetLe : targetExponent ≤ exponent₁ - exponent₂ :=
      min_le_left _ _
    have hshift :
        (shiftAmount : Int) = exponent₁ - exponent₂ - targetExponent := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr htargetLe)
    have hnumerator :
        (numerator : Real) =
          (mantissa₁ : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (shiftAmount : Int) := by
      dsimp only [numerator]
      rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal]
    have hscale :
        ((numerator : Real) / mantissa₂) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix targetExponent =
          ((mantissa₁ : Real) *
              FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₁) /
            ((mantissa₂ : Real) *
              FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₂) := by
      have hmantissa₂Real : (mantissa₂ : Real) ≠ 0 := by
        exact_mod_cast hmantissa₂.ne'
      have hbpow₂ :
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₂ ≠ 0 :=
        FloatLib.Floats.Formats.Flocq.bpow.ne_zero _ _
      rw [hnumerator, div_mul_eq_mul_div, mul_assoc,
        ← FloatLib.Floats.Formats.Flocq.bpow.add_exp,
        show (shiftAmount : Int) + targetExponent = exponent₁ - exponent₂ by omega,
        FloatLib.Floats.Formats.Flocq.bpow.sub_exp]
      field_simp
    rw [hscale]
    cases sign₁ <;> cases sign₂ <;>
      simp [unpackedToReal_finite, modelSignBit, neg_div, div_neg,
        show Sign.negative / Sign.negative = Sign.positive from rfl,
        show Sign.negative / Sign.positive = Sign.negative from rfl,
        show Sign.positive / Sign.negative = Sign.negative from rfl,
        show Sign.positive / Sign.positive = Sign.positive from rfl]
  · exact toReal_ofModel_div_finite_eq_roundAt fmt hfmt sign₁ sign₂ mantissa₁ mantissa₂
      exponent₁ exponent₂ hmantissa₁ hmantissa₂ hquotient hle hfinite

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

The finite result already excludes NaN and infinite factors; signed zeros are allowed. Unlike
`toReal_ofModel_mul_finite_eq_roundAt`, there is no exponent premise: values unpacked from format
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
      exact toReal_ofModel_zero fmt hfmt _
    | finite sign₂ mantissa₂ exponent₂ hmantissa₂ =>
      simp only [Float.Model.UnpackedFloat.mul, unpackedToReal_zero, zero_mul, roundAt_zero]
      exact toReal_ofModel_zero fmt hfmt _
  | finite sign₁ mantissa₁ exponent₁ hmantissa₁ =>
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.mul, hnan] at hfinite
    | infinity _ => simp [Float.Model.UnpackedFloat.mul, hinfinity] at hfinite
    | zero sign₂ =>
      simp only [Float.Model.UnpackedFloat.mul, unpackedToReal_zero, mul_zero, roundAt_zero]
      exact toReal_ofModel_zero fmt hfmt _
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

The finite result already excludes a NaN or infinite dividend and a zero divisor. It does not
exclude an infinite divisor: a finite dividend over an infinite divisor is a signed zero. Unlike
`toReal_ofModel_div_finite_eq_roundAt`, there is no `divCore` premise: a quotient below the least
positive subnormal in magnitude rounds to a signed zero or a signed least subnormal.
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
      exact toReal_ofModel_zero fmt hfmt _
    | finite sign₁ mantissa₁ exponent₁ hmantissa₁ =>
      exact toReal_ofModel_div_finite_eq_roundAt_of_isFinite fmt hfmt sign₁ sign₂
        mantissa₁ mantissa₂ exponent₁ exponent₂ hmantissa₁ hmantissa₂ hfinite

end Model
end FloatLib.Floats.Formats.BinaryInterchange
