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
encodings. Conventional IEEE descriptors reuse the established unpacked model; configurable
descriptors follow their declared bias and exceptional-value policy.

The central theorem proves that executable field decoding agrees with Lean's logical floating
model. Later lemmas recover finiteness, sign, zero, and sign-toggle facts from successful
decoding. This direction is deliberate: optimized kernels may inspect fields, while their proofs
can immediately move to one canonical exact dyadic semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-! ## Complete-format decoding -/

/--
Decode a finite `Model` into an exact dyadic under its complete format descriptor.

The conventional IEEE case delegates to the established decoder. Other encodings use their
declared exponent bias and exceptional-value policy directly.
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

/-- Exact rational value of a finite executable float; returns `none` for NaN or infinity. -/
def toRat? {fmt : FloatFormat} (x : Model fmt) : Option Rat :=
  (toDyadic? x).map Numerics.Dyadic.toRat

/--
The IEEE field decoder agrees with Lean's logical IEEE model.

The theorem is width-generic. Both sides use the conventional IEEE interpretation of the layout;
the descriptor's custom bias and exceptional-value policy are handled separately by `toDyadic?`.
-/
theorem ieeeToDyadic?_eq_unpackedToDyadic?_toModel {fmt : FloatFormat} (x : Model fmt) :
    ieeeToDyadic? x = unpackedToDyadic? (toModel x) := by
  have hModelFracWidth :
      (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit = fmt.fracWidth := rfl
  have hModelBias :
      (FloatFormat.toModel fmt).exponentBias = fmt.bias := rfl
  simp only [toModel, Float.Model.UnpackedFloat.unpack]
  split <;> rename_i hExponentOnes
  · have hExpField : expField x = FloatFormat.expAllOnesNat fmt := by
      rw [← unpackExponent_toNat x, hExponentOnes]
      exact toNat_neg_one_exponentBits fmt
    split <;> rename_i hMantissa
    · have hFracField : fracField x = 0 := by
        rw [← unpackMantissa_toNat x, hMantissa]
        rfl
      simp [unpackedToDyadic?, ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, hExpField, hFracField]
    · have hFracField : fracField x ≠ 0 := by
        intro h
        apply hMantissa
        apply BitVec.toNat_inj.mp
        rw [unpackMantissa_toNat x, h]
        rfl
      simp [unpackedToDyadic?, ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, hExpField, hFracField]
  · have hExpField : expField x ≠ FloatFormat.expAllOnesNat fmt := by
      intro h
      apply hExponentOnes
      apply BitVec.toNat_inj.mp
      rw [unpackExponent_toNat x, h]
      exact (toNat_neg_one_exponentBits fmt).symm
    have hNaN : IEEE.isNaN x = false := by simp [IEEE.isNaN, hExpField]
    have hInf : IEEE.isInf x = false := by simp [IEEE.isInf, hExpField]
    split <;> rename_i hExponentZero
    · have hExpFieldZero : expField x = 0 := by
        rw [← unpackExponent_toNat x, hExponentZero]
        rfl
      split <;> rename_i hMantissa
      · have hFracField : fracField x = 0 := by
          rw [← unpackMantissa_toNat x, hMantissa]
          rfl
        simp [unpackedToDyadic?, ieeeToDyadic?, hNaN, hInf, hExpFieldZero,
          hFracField, modelSignBit_ofBitVec_unpackSign]
      · have hFracField : fracField x ≠ 0 := by
          intro h
          apply hMantissa
          apply BitVec.toNat_inj.mp
          rw [unpackMantissa_toNat x, h]
          rfl
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
    · have hExpFieldZero : expField x ≠ 0 := by
        intro h
        apply hExponentZero
        apply BitVec.toNat_inj.mp
        rw [unpackExponent_toNat x, h]
        rfl
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
  have hdecodedModel :
      unpackedToDyadic? (toModel x) =
        some ({ negative := sign, significand := mantissa, exponent := exponent } : Numerics.Dyadic) := by
    rw [← ieeeToDyadic?_eq_unpackedToDyadic?_toModel x]
    exact hdecode
  generalize hmodel : toModel x = value at hdecodedModel ⊢
  cases value with
  | infinity modelSign =>
      simp [unpackedToDyadic?] at hdecodedModel
  | notANumber =>
      simp [unpackedToDyadic?] at hdecodedModel
  | zero modelSign =>
      simp [unpackedToDyadic?] at hdecodedModel
      exact (hmantissa hdecodedModel.2.1.symm).elim
  | finite modelSign modelMantissa modelExponent modelMantissaPositive =>
      simp only [unpackedToDyadic?, Option.some.injEq, Numerics.Dyadic.mk.injEq] at hdecodedModel
      rcases hdecodedModel with ⟨hsign, hmantissaValue, hexponent⟩
      subst modelMantissa
      subst modelExponent
      have hmodelSign : modelSign = Model.modelSign sign := by
        cases modelSign <;> cases sign <;> simp_all
      subst modelSign
      rfl

/-- A zero dyadic decode determines the corresponding signed model zero. -/
theorem toModel_eq_zero_of_ieeeToDyadic?_eq_some
    {fmt : FloatFormat} (x : Model fmt) (sign : Bool) (exponent : Int)
    (hdecode :
      ieeeToDyadic? x = some ({ negative := sign, significand := 0, exponent := exponent } : Numerics.Dyadic)) :
    toModel x = .zero (modelSign sign) := by
  have hdecodedModel :
      unpackedToDyadic? (toModel x) =
        some ({ negative := sign, significand := 0, exponent := exponent } : Numerics.Dyadic) := by
    rw [← ieeeToDyadic?_eq_unpackedToDyadic?_toModel x]
    exact hdecode
  generalize hmodel : toModel x = value at hdecodedModel ⊢
  cases value with
  | infinity modelSign =>
      simp [unpackedToDyadic?] at hdecodedModel
  | notANumber =>
      simp [unpackedToDyadic?] at hdecodedModel
  | zero modelSign =>
      simp only [unpackedToDyadic?, Option.some.injEq, Numerics.Dyadic.mk.injEq] at hdecodedModel
      have hmodelSign : modelSign = Model.modelSign sign := by
        cases modelSign <;> cases sign <;> simp_all
      subst modelSign
      rfl
  | finite modelSign modelMantissa modelExponent modelMantissaPositive =>
      simp only [unpackedToDyadic?, Option.some.injEq, Numerics.Dyadic.mk.injEq] at hdecodedModel
      exact (Nat.ne_of_gt modelMantissaPositive hdecodedModel.2.1).elim

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
  have hnaninf : (IEEE.isNaN x || IEEE.isInf x) = false := by
    simp [hxNaN, hxInf]
  unfold ieeeToDyadic? at hx ⊢
  simp (config := { zeta := true })
    [hnaninf, signBit_toggleSign, expField_toggleSign, fracField_toggleSign] at hx ⊢
  by_cases he : expField x = 0
  · by_cases hf : fracField x = 0
    · have hx' : some { negative := signBit x, significand := 0, exponent := 0 } = some d := by
        simpa [he, hf] using hx
      have hd : d = { negative := signBit x, significand := 0, exponent := 0 } :=
        (Option.some.inj hx').symm
      simp [he, hf, hd]
    · have hx' : some {
          negative := signBit x
          significand := fracField x
          exponent := FloatFormat.ieeeMinSubnormalExponent fmt } = some d := by
        simpa [he, hf] using hx
      have hd : d = {
          negative := signBit x
          significand := fracField x
          exponent := FloatFormat.ieeeMinSubnormalExponent fmt } := (Option.some.inj hx').symm
      simp [he, hf, hd]
  · have hx' : some {
        negative := signBit x
        significand := pow2 fmt.fracWidth + fracField x
        exponent := Int.ofNat (expField x) -
          Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt) } = some d := by
      simpa [he] using hx
    have hd : d = {
        negative := signBit x
        significand := pow2 fmt.fracWidth + fracField x
        exponent := Int.ofNat (expField x) -
          Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt) } := (Option.some.inj hx').symm
    simp [he, hd]

/-- IEEE dyadic decoding preserves the stored sign bit. -/
theorem sign_eq_signBit_of_ieeeToDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) : d.negative = signBit x := by
  have hnan := isNaN_eq_false_of_ieeeToDyadic?_some hx
  have hinf := isInf_eq_false_of_ieeeToDyadic?_some hx
  unfold ieeeToDyadic? at hx
  simp only [hnan, hinf, Bool.false_or, Bool.false_eq_true, ite_false] at hx
  split at hx
  · split at hx
    · simpa using congrArg Numerics.Dyadic.negative (Option.some.inj hx.symm)
    · simpa using congrArg Numerics.Dyadic.negative (Option.some.inj hx.symm)
  · simpa using congrArg Numerics.Dyadic.negative (Option.some.inj hx.symm)

/-- A decoded dyadic has zero mantissa only when the source is an IEEE signed zero. -/
theorem isZero_eq_true_of_ieeeToDyadic?_some_of_mant_eq_zero
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : ieeeToDyadic? x = some d) (hmant : d.significand = 0) :
    IEEE.isZero x = true := by
  have hnan := isNaN_eq_false_of_ieeeToDyadic?_some hx
  have hinf := isInf_eq_false_of_ieeeToDyadic?_some hx
  unfold ieeeToDyadic? at hx
  simp only [hnan, hinf, Bool.false_or, Bool.false_eq_true, ite_false] at hx
  split at hx <;> rename_i hexponent
  · split at hx <;> rename_i hfraction
    · simp [IEEE.isZero, hexponent, hfraction]
    · have hdMant :
          d.significand = fracField x := by
        simpa using congrArg Numerics.Dyadic.significand (Option.some.inj hx.symm)
      simp [hmant] at hdMant
      exact (hfraction (beq_iff_eq.2 hdMant.symm)).elim
  · have hdMant :
        d.significand = pow2 fmt.fracWidth + fracField x := by
      simpa using congrArg Numerics.Dyadic.significand (Option.some.inj hx.symm)
    simp [hmant, pow2_eq_two_pow] at hdMant
    have hpow : 0 < 2 ^ fmt.fracWidth := Nat.pow_pos (by decide)
    omega

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

/-- IEEE dyadic decoding succeeds exactly on bit patterns classified as finite by IEEE rules. -/
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
