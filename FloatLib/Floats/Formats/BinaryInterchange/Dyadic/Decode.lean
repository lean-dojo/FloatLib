/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Core

/-!
# Correctness of exact IEEE decoding

Binary arithmetic proofs need an exact value that is cheaper and more concrete than a real
number. `toDyadic?` decodes every finite encoding to that value and rejects exceptional
encodings. Conventional IEEE descriptors use the IEEE layout reading `ieeeToDyadic?`, and
configurable descriptors follow their declared bias and exceptional-value policy.

This file's theorems are about `ieeeToDyadic?`, which reads any layout with the conventional bias
and the IEEE exceptional patterns and is `toDyadic?` only when `fmt.isIEEE`. Its central theorem,
`ieeeToDyadic?_eq_unpackedToDyadic?_toModel`, proves that this field decoding agrees with Lean's
logical floating model. Later lemmas recover IEEE finiteness, sign, zero, and sign-toggle facts
from a successful IEEE decode, though for a custom bias or a finite-only, maximum-NaN, or
unsigned-zero encoding they do not describe the declared semantics.

The descriptor-aware facts about `toDyadic?` are in `Dyadic.Classification`
(`toDyadic?_isSome_eq_isFinite`, `toDyadic?_ieee_eq_model`, and the sign and zero lemmas), and
`toDyadic?_neg_of_toDyadic?_some` covers negation. We chose this direction on purpose. Optimized
kernels may inspect fields, while their proofs can move at once to one canonical exact dyadic
semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-! ## Complete-format decoding -/

/--
Decode a finite `Model` into an exact dyadic under its complete format descriptor.

The conventional IEEE case delegates to the established decoder. Other encodings use their
declared exponent bias and exceptional-value policy.
-/
@[inline] def toDyadic? {fmt : FloatFormat} (x : Model fmt) : Option Numerics.Dyadic :=
  if fmt.isIEEE then
    ieeeToDyadic? x
  else if !isFinite x then
    none
  else if isZero x then
    some { negative := signBit x, significand := 0, exponent := 0 }
  else
    let exponent := expField x
    let fraction := fracField x
    if exponent == 0 then
      some
        { negative := signBit x
          significand := fraction
          exponent := fmt.minSubnormalExponent }
    else
      some
        { negative := signBit x
          significand := pow2 fmt.fracWidth + fraction
          exponent := Int.ofNat exponent - Int.ofNat fmt.exponentBias -
            Int.ofNat fmt.fracWidth }

/-- Exact rational value of a finite executable float, or `none` for NaN or infinity. -/
@[inline] def toRat? {fmt : FloatFormat} (x : Model fmt) : Option Rat :=
  (toDyadic? x).map Numerics.Dyadic.toRat

private theorem unpackMantissa_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    Float.Model.UnpackedFloat.unpackMantissa (spec := FloatFormat.toModel fmt) (toModelBits x) =
        0#_ ↔ fracField x = 0 := by
  rw [← BitVec.toNat_inj, unpackMantissa_toNat x, BitVec.toNat_zero]

private theorem unpackExponent_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    Float.Model.UnpackedFloat.unpackExponent (spec := FloatFormat.toModel fmt) (toModelBits x) =
        0#_ ↔ expField x = 0 := by
  rw [← BitVec.toNat_inj, unpackExponent_toNat x, BitVec.toNat_zero]

private theorem unpackExponent_eq_neg_one_iff {fmt : FloatFormat} (x : Model fmt) :
    Float.Model.UnpackedFloat.unpackExponent (spec := FloatFormat.toModel fmt) (toModelBits x) =
        -1#_ ↔ expField x = FloatFormat.expAllOnesNat fmt := by
  rw [← BitVec.toNat_inj, unpackExponent_toNat x, toNat_neg_one_exponentBits fmt]

/--
The IEEE field decoder agrees with Lean's logical IEEE model.

The theorem is width-generic. Both sides use the conventional IEEE interpretation of the layout,
and `toDyadic?` handles the descriptor's custom bias and exceptional-value policy.
-/
theorem ieeeToDyadic?_eq_unpackedToDyadic?_toModel {fmt : FloatFormat} (x : Model fmt) :
    ieeeToDyadic? x = unpackedToDyadic? (toModel x) := by
  have hModelFracWidth :
      (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit = fmt.fracWidth := rfl
  have hModelBias :
      (FloatFormat.toModel fmt).exponentBias = fmt.bias := rfl
  simp only [toModel, Float.Model.UnpackedFloat.unpack]
  split <;> rename_i hExponentOnes
  · have hExpField := (unpackExponent_eq_neg_one_iff x).1 hExponentOnes
    split <;> rename_i hMantissa
    · have hFracField := (unpackMantissa_eq_zero_iff x).1 hMantissa
      simp [unpackedToDyadic?, ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, hExpField, hFracField]
    · have hFracField := mt (unpackMantissa_eq_zero_iff x).2 hMantissa
      simp [unpackedToDyadic?, ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, hExpField, hFracField]
  · have hExpField := mt (unpackExponent_eq_neg_one_iff x).2 hExponentOnes
    have hNaN : IEEE.isNaN x = false := by simp [IEEE.isNaN, hExpField]
    have hInf : IEEE.isInf x = false := by simp [IEEE.isInf, hExpField]
    split <;> rename_i hExponentZero
    · have hExpFieldZero := (unpackExponent_eq_zero_iff x).1 hExponentZero
      split <;> rename_i hMantissa
      · have hFracField := (unpackMantissa_eq_zero_iff x).1 hMantissa
        simp [unpackedToDyadic?, ieeeToDyadic?, hNaN, hInf, hExpFieldZero,
          hFracField, modelSignBit_ofBitVec_unpackSign]
      · have hFracField := mt (unpackMantissa_eq_zero_iff x).2 hMantissa
        have hMantissaNat := unpackMantissa_toNat x
        have hExponentNat :
            (Float.Model.UnpackedFloat.unpackExponent
              (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat = 0 := by
          exact congrArg BitVec.toNat hExponentZero
        have hSubnormalExp :
            FloatFormat.ieeeMinSubnormalExponent fmt =
              Int.ofNat (Float.Model.UnpackedFloat.unpackExponent
                (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat -
                  (Int.ofNat (FloatFormat.toModel fmt).exponentBias +
                    Int.ofNat (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit) + 1 := by
          rw [hExponentNat, hModelBias, hModelFracWidth]
          unfold FloatFormat.ieeeMinSubnormalExponent
          simp only [Int.sub_eq_add_neg, Int.neg_add]
          ac_rfl
        simp [unpackedToDyadic?, ieeeToDyadic?, hNaN, hInf, hExpFieldZero,
          hFracField, hModelFracWidth, hModelBias]
        constructor
        · exact (modelSignBit_ofBitVec_unpackSign x).symm
        constructor
        · exact hMantissaNat.symm
        · exact hSubnormalExp
    · have hExpFieldZero := mt (unpackExponent_eq_zero_iff x).2 hExponentZero
      have hMantissaNat := unpackMantissa_toNat x
      have hExponentNat := unpackExponent_toNat x
      have hAppended :
          (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa
            (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat =
            2 ^ fmt.fracWidth +
              (Float.Model.UnpackedFloat.unpackMantissa
                (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat := by
        rw [BitVec.toNat_append]
        rw [← Nat.shiftLeft_add_eq_or_of_lt
          (Float.Model.UnpackedFloat.unpackMantissa
            (spec := FloatFormat.toModel fmt) (toModelBits x)).isLt]
        simp [Nat.shiftLeft_eq, FloatFormat.toModel]
      have hNormalMantissa :
          pow2 fmt.fracWidth + fracField x =
            (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa
              (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat := by
        rw [hAppended, hMantissaNat]
        simp [pow2, Nat.shiftLeft_eq]
      simp [unpackedToDyadic?, ieeeToDyadic?, hNaN, hInf, hExpFieldZero,
        hModelFracWidth, hModelBias, FloatFormat.ieeeNormalMantissaExpOffset]
      constructor
      · exact (modelSignBit_ofBitVec_unpackSign x).symm
      constructor
      · exact hNormalMantissa
      · exact hExponentNat.symm

/--
A successful decode of Lean's unpacked model is a signed zero or a finite value, read field for
field with its sign bit.
-/
theorem unpackedToDyadic?_eq_some_cases {value : Float.Model.UnpackedFloat}
    {d : Numerics.Dyadic} (h : unpackedToDyadic? value = some d) :
    (∃ sign, value = .zero sign ∧
        d = { negative := modelSignBit sign, significand := 0, exponent := 0 }) ∨
      ∃ sign mantissa exponent hmantissa,
        value = .finite sign mantissa exponent hmantissa ∧
          d = { negative := modelSignBit sign, significand := mantissa, exponent } := by
  cases value with
  | notANumber | infinity _ => simp [unpackedToDyadic?] at h
  | zero sign => exact Or.inl ⟨sign, rfl, (Option.some.inj h).symm⟩
  | finite sign mantissa exponent hmantissa =>
      exact Or.inr ⟨sign, mantissa, exponent, hmantissa, rfl, (Option.some.inj h).symm⟩

/--
A nonzero successful dyadic decode determines the corresponding finite logical model value.
-/
theorem toModel_eq_finite_of_ieeeToDyadic?_eq_some
    {fmt : FloatFormat} (x : Model fmt) (sign : Bool)
    (mantissa : Nat) (exponent : Int) (hmantissa : mantissa ≠ 0)
    (hdecode :
      ieeeToDyadic? x = some ({ negative := sign, significand := mantissa, exponent := exponent } : Numerics.Dyadic)) :
    toModel x =
      .finite (modelSign sign) mantissa exponent
        (Nat.pos_of_ne_zero hmantissa) := by
  rw [ieeeToDyadic?_eq_unpackedToDyadic?_toModel x] at hdecode
  rcases unpackedToDyadic?_eq_some_cases hdecode with ⟨_, -, hd⟩ | ⟨s, _, _, _, hmodel, hd⟩
  · exact absurd (congrArg Numerics.Dyadic.significand hd) hmantissa
  · simp only [Numerics.Dyadic.mk.injEq] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    rw [hmodel]
    cases s <;> rfl

/-- A zero dyadic decode determines the corresponding signed model zero. -/
theorem toModel_eq_zero_of_ieeeToDyadic?_eq_some
    {fmt : FloatFormat} (x : Model fmt) (sign : Bool) (exponent : Int)
    (hdecode :
      ieeeToDyadic? x = some ({ negative := sign, significand := 0, exponent := exponent } : Numerics.Dyadic)) :
    toModel x = .zero (modelSign sign) := by
  rw [ieeeToDyadic?_eq_unpackedToDyadic?_toModel x] at hdecode
  rcases unpackedToDyadic?_eq_some_cases hdecode with ⟨s, hmodel, hd⟩ | ⟨_, _, _, hm, -, hd⟩
  · simp only [Numerics.Dyadic.mk.injEq] at hd
    obtain ⟨rfl, -, -⟩ := hd
    rw [hmodel]
    cases s <;> rfl
  · exact absurd (congrArg Numerics.Dyadic.significand hd).symm (Nat.ne_of_gt hm)

/-!
## Decoding and finiteness
-/

/-- A successful dyadic decode rules out NaN. -/
theorem isNaN_eq_false_of_ieeeToDyadic?_some {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) : IEEE.isNaN x = false := by
  cases h : IEEE.isNaN x
  · rfl
  · simp [ieeeToDyadic?, h] at hx

/-- A successful dyadic decode rules out infinity. -/
theorem isInf_eq_false_of_ieeeToDyadic?_some {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) : IEEE.isInf x = false := by
  cases h : IEEE.isInf x
  · rfl
  · simp [ieeeToDyadic?, h] at hx

/--
A successful IEEE decode is one of the three finite shapes: a signed zero, a subnormal read at the
least subnormal exponent, or a normal value with its implicit leading bit.
-/
theorem ieeeToDyadic?_eq_some_cases {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) :
    (expField x = 0 ∧ fracField x = 0 ∧
        d = { negative := signBit x, significand := 0, exponent := 0 }) ∨
      (expField x = 0 ∧ fracField x ≠ 0 ∧
        d = { negative := signBit x
              significand := fracField x
              exponent := FloatFormat.ieeeMinSubnormalExponent fmt }) ∨
      (expField x ≠ 0 ∧
        d = { negative := signBit x
              significand := pow2 fmt.fracWidth + fracField x
              exponent := Int.ofNat (expField x) -
                Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt) }) := by
  have hnan := isNaN_eq_false_of_ieeeToDyadic?_some hx
  have hinf := isInf_eq_false_of_ieeeToDyadic?_some hx
  unfold ieeeToDyadic? at hx
  simp only [hnan, hinf, Bool.false_or, Bool.false_eq_true, ite_false] at hx
  split at hx <;> rename_i hexponent
  · split at hx <;> rename_i hfraction
    · exact Or.inl ⟨beq_iff_eq.1 hexponent, beq_iff_eq.1 hfraction, (Option.some.inj hx).symm⟩
    · exact Or.inr (Or.inl ⟨beq_iff_eq.1 hexponent, fun h => hfraction (beq_iff_eq.2 h),
        (Option.some.inj hx).symm⟩)
  · exact Or.inr (Or.inr ⟨fun h => hexponent (beq_iff_eq.2 h), (Option.some.inj hx).symm⟩)

/-- IEEE decoding preserves magnitude and exponent when the storage sign bit is toggled. -/
theorem ieeeToDyadic?_toggleSign_of_ieeeToDyadic?_some
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) :
    ieeeToDyadic? (toggleSign x) =
      some { negative := !d.negative, significand := d.significand, exponent := d.exponent } := by
  have hxNaN : IEEE.isNaN x = false :=
    isNaN_eq_false_of_ieeeToDyadic?_some hx
  have hxInf : IEEE.isInf x = false :=
    isInf_eq_false_of_ieeeToDyadic?_some hx
  unfold ieeeToDyadic?
  rcases ieeeToDyadic?_eq_some_cases hx with ⟨he, hf, rfl⟩ | ⟨he, hf, rfl⟩ | ⟨he, rfl⟩ <;>
    simp (config := { zeta := true })
      [signBit_toggleSign, expField_toggleSign, fracField_toggleSign, *]

/-- IEEE dyadic decoding preserves the stored sign bit. -/
theorem sign_eq_signBit_of_ieeeToDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) : d.negative = signBit x := by
  rcases ieeeToDyadic?_eq_some_cases hx with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- A decoded dyadic has zero mantissa only when the source is an IEEE signed zero. -/
theorem isZero_eq_true_of_ieeeToDyadic?_some_of_mant_eq_zero
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) (hmant : d.significand = 0) :
    IEEE.isZero x = true := by
  rcases ieeeToDyadic?_eq_some_cases hx with ⟨he, hf, -⟩ | ⟨-, hf, rfl⟩ | ⟨-, rfl⟩
  · simp [IEEE.isZero, he, hf]
  · exact absurd hmant hf
  · simp [pow2_eq_two_pow] at hmant

/-- A successful dyadic decode certifies that the source bit pattern is finite. -/
theorem isFinite_eq_true_of_ieeeToDyadic?_some {fmt : FloatFormat}
    {x : Model fmt} {d : Numerics.Dyadic} (hx : ieeeToDyadic? x = some d) : IEEE.isFinite x = true := by
  unfold IEEE.isFinite
  apply (bne_iff_ne).2
  intro hexp
  have hexpB : (expField x == FloatFormat.expAllOnesNat fmt) = true :=
    (beq_iff_eq).2 hexp
  by_cases hfrac : fracField x = 0
  · have hinf : IEEE.isInf x = true := by simp [IEEE.isInf, hexpB, hfrac]
    have hnotInf := isInf_eq_false_of_ieeeToDyadic?_some hx
    simp [hinf] at hnotInf
  · have hnan : IEEE.isNaN x = true := by simp [IEEE.isNaN, hexpB, hfrac]
    have hnotNaN := isNaN_eq_false_of_ieeeToDyadic?_some hx
    simp [hnan] at hnotNaN

/-- Every bit pattern that is neither NaN nor infinity has an exact dyadic decode. -/
theorem exists_ieeeToDyadic?_of_not_isNaN_not_isInf {fmt : FloatFormat} {x : Model fmt}
    (hnan : IEEE.isNaN x = false) (hinf : IEEE.isInf x = false) :
    ∃ d, ieeeToDyadic? x = some d := by
  by_cases hexp : expField x = 0
  · by_cases hfrac : fracField x = 0
    · exact ⟨Numerics.Dyadic.mk (signBit x) 0 0,
        by simp [ieeeToDyadic?, hnan, hinf, hexp, hfrac]⟩
    · exact ⟨Numerics.Dyadic.mk (signBit x) (fracField x) (FloatFormat.ieeeMinSubnormalExponent fmt),
        by simp [ieeeToDyadic?, hnan, hinf, hexp, hfrac]⟩
  · exact ⟨Numerics.Dyadic.mk (signBit x) (pow2 fmt.fracWidth + fracField x)
        (Int.ofNat (expField x) - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)),
      by simp [ieeeToDyadic?, hnan, hinf, hexp]⟩

/-- Every bit pattern classified as finite by IEEE rules has an exact dyadic decode. -/
theorem exists_ieeeToDyadic?_of_isFinite {fmt : FloatFormat} {x : Model fmt}
    (hx : IEEE.isFinite x = true) : ∃ d, ieeeToDyadic? x = some d := by
  have hexp : expField x ≠ FloatFormat.expAllOnesNat fmt := (bne_iff_ne).mp hx
  have hnan : IEEE.isNaN x = false := by simp [IEEE.isNaN, hexp]
  have hinf : IEEE.isInf x = false := by simp [IEEE.isInf, hexp]
  exact exists_ieeeToDyadic?_of_not_isNaN_not_isInf hnan hinf

/-- IEEE dyadic decoding succeeds if and only if IEEE rules classify the bit pattern as finite. -/
theorem ieeeToDyadic?_isSome_eq_isFinite {fmt : FloatFormat} (x : Model fmt) :
    (ieeeToDyadic? x).isSome = IEEE.isFinite x := by
  cases hdy : ieeeToDyadic? x with
  | some d =>
      have hfin := isFinite_eq_true_of_ieeeToDyadic?_some hdy
      simp [hfin]
  | none =>
      cases hfin : IEEE.isFinite x with
      | false => rfl
      | true =>
          obtain ⟨d, hd⟩ := exists_ieeeToDyadic?_of_isFinite hfin
          rw [hdy] at hd
          contradiction


end Model

end FloatLib.Floats.Formats.BinaryInterchange
