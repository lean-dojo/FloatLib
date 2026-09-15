/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Complete-format decoding and classification

The exact dyadic decoder determines finiteness, sign, and zero status for arithmetic proofs.
Successful decoding is equivalent to finiteness, and the decoded dyadic recovers the encoding's
sign and zero status. The same statements cover IEEE encodings, finite-only encodings, and
finite encodings with an unsigned-zero policy.

NaN selection is handled here as classification rather than arithmetic. That keeps exceptional
control flow out of the exact finite kernels and gives unary, binary, and ternary operations one
shared account of when `chooseNaN` can return `none`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-! ## Complete-format decoding theorems -/

/-- Exact decoding succeeds precisely for values that are finite under the complete format. -/
theorem toDyadic?_isSome_eq_isFinite {fmt : FloatFormat} (x : Model fmt) :
    (toDyadic? x).isSome = isFinite x := by
  by_cases hieee : fmt.isIEEE = true
  · have hencoding : fmt.encoding = .ieee := by
      simp [FloatFormat.isIEEE] at hieee
      exact hieee.1
    simpa [toDyadic?, hieee, isFinite, hencoding] using
      ieeeToDyadic?_isSome_eq_isFinite x
  · simp only [toDyadic?, hieee, Bool.false_eq_true, if_false]
    cases hfinite : isFinite x
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      split
      · rfl
      · split <;> rfl

/-- Every finite value has an exact dyadic decoding. -/
theorem exists_toDyadic?_of_isFinite {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = true) :
    ∃ d, toDyadic? x = some d := by
  have hsome : (toDyadic? x).isSome = true := by
    rw [toDyadic?_isSome_eq_isFinite, hfinite]
  cases hdecode : toDyadic? x with
  | none => simp [hdecode] at hsome
  | some d => exact ⟨d, rfl⟩

/--
Extract the exact dyadic represented by a value already proved finite.

Complete binary descriptors make this operation total: `toDyadic?` succeeds exactly on finite
encodings. The proof argument is erased, and extraction requires no default dyadic.
-/
@[inline] def finiteDyadic {fmt : FloatFormat}
    (x : Model fmt) (hfinite : isFinite x = true) : Numerics.Dyadic :=
  (toDyadic? x).get (by
    rw [toDyadic?_isSome_eq_isFinite, hfinite])

/-- Proof-guided finite extraction returns the dyadic produced by exact decoding. -/
@[simp] theorem finiteDyadic_eq_of_toDyadic
    {fmt : FloatFormat} {x : Model fmt} {exact : Numerics.Dyadic}
    (hfinite : isFinite x = true) (hdecode : toDyadic? x = some exact) :
    finiteDyadic x hfinite = exact := by
  unfold finiteDyadic
  exact Option.get_of_eq_some _ hdecode

/-- For a conventional IEEE descriptor, policy-aware decoding agrees with Lean's model. -/
theorem toDyadic?_ieee_eq_model (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (x : Model fmt) :
    toDyadic? x = unpackedToDyadic? (toModel x) := by
  simpa [toDyadic?, hfmt] using
    ieeeToDyadic?_eq_unpackedToDyadic?_toModel x

/-! ## Complete-format classification -/

/-- Every value denoting zero is finite under the same complete format. -/
theorem isFinite_eq_true_of_isZero_eq_true {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    isFinite x = true := by
  have hall : FloatFormat.expAllOnesNat fmt ≠ 0 :=
    (FloatFormat.expAllOnesNat_pos fmt).ne'
  cases hencoding : fmt.encoding
  · simp only [isZero, hencoding] at hx
    simp only [isFinite, hencoding]
    have hfields : expField x = 0 ∧ fracField x = 0 := by
      simpa [IEEE.isZero, Bool.and_eq_true] using hx
    simp only [IEEE.isFinite, hfields.1]
    exact (bne_iff_ne).2 (fun hzero => hall hzero.symm)
  · simp only [isZero, hencoding] at hx
    have hfields : expField x = 0 ∧ fracField x = 0 := by
      simpa [IEEE.isZero, Bool.and_eq_true] using hx
    have hzeroNe : (0 : Nat) ≠ fmt.expAllOnesNat :=
      fun hzero => hall hzero.symm
    simp [isFinite, isNaN, hencoding, hfields.1, hzeroNe]
  · have hbits : x.bits = 0 := by
      simpa [isZero, hencoding] using hx
    have hzeroNe : (0 : FloatFormat.ExecWord fmt) ≠ fmt.signMask :=
      fun hzero => FloatFormat.signMask_ne_zero fmt hzero.symm
    simp only [isFinite, isNaN, hencoding, hbits]
    exact (bne_iff_ne).2 hzeroNe
  · simp [isFinite, hencoding]

/-- Finite values are not NaNs. -/
theorem isNaN_eq_false_of_isFinite_eq_true {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    isNaN x = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hxIEEE : IEEE.isFinite x = true := by
        simpa [isFinite, hencoding] using hx
      have hexp : expField x ≠ FloatFormat.expAllOnesNat fmt :=
        (bne_iff_ne).1 hxIEEE
      simp [isNaN, hencoding, IEEE.isNaN, hexp]
  | finiteMaxNaN | finiteUnsignedZero =>
      simpa [isFinite, hencoding] using hx
  | finite =>
      simp [isNaN, hencoding]

/-- A non-NaN, non-infinite bit pattern is finite. -/
theorem isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) (hinf : isInf x = false) :
    isFinite x = true := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hnanIEEE : IEEE.isNaN x = false := by
        simpa [isNaN, hencoding] using hnan
      have hinfIEEE : IEEE.isInf x = false := by
        simpa [isInf, hencoding] using hinf
      by_cases hexp : expField x = FloatFormat.expAllOnesNat fmt
      · by_cases hfrac : fracField x = 0
        · have : IEEE.isInf x = true := by simp [IEEE.isInf, hexp, hfrac]
          simp [hinfIEEE] at this
        · have : IEEE.isNaN x = true := by simp [IEEE.isNaN, hexp, hfrac]
          simp [hnanIEEE] at this
      · simpa [isFinite, hencoding, IEEE.isFinite] using (bne_iff_ne).2 hexp
  | finiteMaxNaN | finiteUnsignedZero =>
      simp [isFinite, hencoding, hnan]
  | finite =>
      simp [isFinite, hencoding]

/-! ## NaN-selection classification -/

/-- Unary NaN selection returns `none` exactly when its operand is not a NaN. -/
theorem chooseNaN1_eq_none_iff {fmt : FloatFormat} (x : Model fmt) :
    chooseNaN1 x = none ↔ isNaN x = false := by
  simp [chooseNaN1]

/-- Binary NaN selection returns `none` exactly when neither operand is a NaN. -/
theorem chooseNaN2_eq_none_iff {fmt : FloatFormat} (x y : Model fmt) :
    chooseNaN2 x y = none ↔ isNaN x = false ∧ isNaN y = false := by
  constructor
  · intro hnone
    cases hxSNaN : isSNaN x <;>
      cases hySNaN : isSNaN y <;>
      cases hxNaN : isNaN x <;>
      cases hyNaN : isNaN y <;>
      simp_all [chooseNaN2]
  · rintro ⟨hxNaN, hyNaN⟩
    have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hxNaN
    have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hyNaN
    simp [chooseNaN2, hxSNaN, hySNaN, hxNaN, hyNaN]

/-- Ternary NaN selection returns `none` exactly when none of its operands is a NaN. -/
theorem chooseNaN3_eq_none_iff {fmt : FloatFormat} (x y z : Model fmt) :
    chooseNaN3 x y z = none ↔
      isNaN x = false ∧ isNaN y = false ∧ isNaN z = false := by
  constructor
  · intro hnone
    cases hxSNaN : isSNaN x <;>
      cases hySNaN : isSNaN y <;>
      cases hzSNaN : isSNaN z <;>
      cases hxNaN : isNaN x <;>
      cases hyNaN : isNaN y <;>
      cases hzNaN : isNaN z <;>
      simp_all [chooseNaN3]
  · rintro ⟨hxNaN, hyNaN, hzNaN⟩
    have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hxNaN
    have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hyNaN
    have hzSNaN := isSNaN_eq_false_of_isNaN_eq_false z hzNaN
    simp [chooseNaN3, hxSNaN, hySNaN, hzSNaN, hxNaN, hyNaN, hzNaN]

/-- A finite-only encoding contains no NaN bit pattern. -/
theorem isNaN_eq_false_of_encoding_finite {fmt : FloatFormat}
    (hfmt : fmt.encoding = .finite) (x : Model fmt) :
    isNaN x = false := by
  simp [isNaN, hfmt]

/-- Every bit pattern of a finite-only encoding denotes a finite value. -/
theorem isFinite_eq_true_of_encoding_finite {fmt : FloatFormat}
    (hfmt : fmt.encoding = .finite) (x : Model fmt) :
    isFinite x = true := by
  simp [isFinite, hfmt]

/-- Every non-IEEE encoding in this library excludes infinity. -/
theorem isInf_eq_false_of_encoding_ne_ieee {fmt : FloatFormat}
    (hfmt : fmt.encoding ≠ .ieee) (x : Model fmt) :
    isInf x = false := by
  cases h : fmt.encoding <;> simp_all [isInf]

/-- In FNUZ, a value is zero exactly when all stored bits are zero. -/
theorem isZero_eq_true_iff_of_encoding_finiteUnsignedZero {fmt : FloatFormat}
    (hfmt : fmt.encoding = .finiteUnsignedZero) (x : Model fmt) :
    isZero x = true ↔ x.bits = 0 := by
  simp [isZero, hfmt]

/-- In FNUZ, the would-be negative-zero word is NaN rather than a second zero. -/
theorem signMask_isNaN_of_encoding_finiteUnsignedZero {fmt : FloatFormat}
    (hfmt : fmt.encoding = .finiteUnsignedZero) :
    isNaN (ofBits fmt.signMask : Model fmt) = true := by
  simp [isNaN, hfmt, ofBits]

/-- A NaN bit pattern is not finite under the same format descriptor. -/
theorem isFinite_eq_false_of_isNaN {fmt : FloatFormat} {x : Model fmt}
    (hx : isNaN x = true) : isFinite x = false := by
  cases hencoding : fmt.encoding
  · simp only [isNaN, hencoding] at hx
    simp only [isFinite, hencoding]
    simp [IEEE.isNaN, IEEE.isFinite] at hx ⊢
    exact hx.1
  · simp [isFinite, hencoding, hx]
  · simp [isFinite, hencoding, hx]
  · simp [isNaN, hencoding] at hx

/-- A NaN bit pattern cannot be decoded as a finite dyadic. -/
theorem toDyadic?_eq_none_of_isNaN {fmt : FloatFormat} {x : Model fmt}
    (hx : isNaN x = true) : toDyadic? x = none := by
  have hfinite := isFinite_eq_false_of_isNaN hx
  have hsome : (toDyadic? x).isSome = false := by
    rw [toDyadic?_isSome_eq_isFinite, hfinite]
  cases hdecode : toDyadic? x with
  | none => rfl
  | some value => simp [hdecode] at hsome

/-- Successful exact decoding excludes the format's NaN encodings. -/
theorem isNaN_eq_false_of_toDyadic?_some {fmt : FloatFormat}
    {x : Model fmt} {d : Numerics.Dyadic} (hx : toDyadic? x = some d) :
    isNaN x = false := by
  cases hnan : isNaN x
  · rfl
  · have hnone := toDyadic?_eq_none_of_isNaN hnan
    rw [hx] at hnone
    contradiction

/-- Successful exact decoding characterizes a finite stored value. -/
theorem isFinite_eq_true_of_toDyadic?_some {fmt : FloatFormat}
    {x : Model fmt} {d : Numerics.Dyadic} (hx : toDyadic? x = some d) :
    isFinite x = true := by
  have hsome := congrArg Option.isSome hx
  rw [toDyadic?_isSome_eq_isFinite] at hsome
  simpa using hsome

/-- Successful exact decoding excludes signaling NaNs. -/
theorem isSNaN_eq_false_of_toDyadic?_some {fmt : FloatFormat}
    {x : Model fmt} {d : Numerics.Dyadic} (hx : toDyadic? x = some d) :
    isSNaN x = false :=
  isSNaN_eq_false_of_isNaN_eq_false x
    (isNaN_eq_false_of_toDyadic?_some hx)

/-- Successful exact decoding excludes infinity. -/
theorem isInf_eq_false_of_toDyadic?_some {fmt : FloatFormat}
    {x : Model fmt} {d : Numerics.Dyadic} (hx : toDyadic? x = some d) :
    isInf x = false := by
  have hfinite : isFinite x = true := by
    have hsome := congrArg Option.isSome hx
    rw [toDyadic?_isSome_eq_isFinite] at hsome
    simpa using hsome
  cases hencoding : fmt.encoding
  · simp only [isFinite, hencoding] at hfinite
    simp only [isInf, hencoding]
    simp [IEEE.isFinite, IEEE.isInf] at hfinite ⊢
    exact fun hinf _ => hfinite hinf
  · simp [isInf, hencoding]
  · simp [isInf, hencoding]
  · simp [isInf, hencoding]

/-- Complete-format dyadic decoding preserves the stored sign bit. -/
theorem sign_eq_signBit_of_toDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    d.negative = signBit x := by
  by_cases hieee : fmt.isIEEE = true
  · apply sign_eq_signBit_of_ieeeToDyadic?_some
    simpa [toDyadic?, hieee] using hx
  · simp only [toDyadic?, hieee, Bool.false_eq_true, if_false] at hx
    split at hx
    · simp at hx
    · split at hx
      · simpa using congrArg Numerics.Dyadic.negative (Option.some.inj hx.symm)
      · split at hx <;>
          simpa using congrArg Numerics.Dyadic.negative (Option.some.inj hx.symm)

/-- A complete-format dyadic decode has zero mantissa only for a policy zero. -/
theorem isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) (hmant : d.significand = 0) :
    isZero x = true := by
  by_cases hieee : fmt.isIEEE = true
  · have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
    have hdecode : ieeeToDyadic? x = some d := by
      simpa [toDyadic?, hieee] using hx
    have hzero :=
      isZero_eq_true_of_ieeeToDyadic?_some_of_mant_eq_zero hdecode hmant
    simpa [isZero, hencoding] using hzero
  · simp only [toDyadic?, hieee, Bool.false_eq_true, if_false] at hx
    split at hx <;> rename_i hfinite
    · simp at hx
    · have hfiniteTrue : isFinite x = true := by
        cases h : isFinite x <;> simp_all
      split at hx <;> rename_i hzero
      · exact hzero
      · split at hx <;> rename_i hexponent
        · have hdMant : d.significand = fracField x := by
            simpa using congrArg Numerics.Dyadic.significand (Option.some.inj hx.symm)
          have hexponentZero : expField x = 0 := by
            simpa using hexponent
          have hfraction : fracField x = 0 := by
            simpa [hmant] using hdMant.symm
          have hzeroTrue : isZero x = true := by
            have hreconstruct := ofFields_signBit_expField_fracField x
            have hreconstructZero :
                ofFields fmt (signBit x) 0 0 = x := by
              simpa [hexponentZero, hfraction] using hreconstruct
            cases hencoding : fmt.encoding with
            | ieee | finiteMaxNaN | finite =>
                simp [isZero, hencoding, IEEE.isZero, hexponent, hfraction]
            | finiteUnsignedZero =>
                cases hsign : signBit x with
                | false =>
                    have hbits : x.bits = 0 := by
                      simpa [hsign, posZero, ofNatBits, ofBits,
                        FloatFormat.ofWordNat] using
                        (congrArg (fun value : Model fmt => value.bits)
                          hreconstructZero).symm
                    simp [isZero, hencoding, hbits]
                | true =>
                    have hbits : x.bits = fmt.signMask := by
                      simpa [hsign, negZero, ofBits] using
                        (congrArg (fun value : Model fmt => value.bits)
                          hreconstructZero).symm
                    have hnan : isNaN x = true := by
                      simp [isNaN, hencoding, hbits]
                    have hfiniteFalse := isFinite_eq_false_of_isNaN hnan
                    rw [hfiniteTrue] at hfiniteFalse
                    contradiction
          exact (hzero hzeroTrue).elim
        · have hdMant :
              d.significand = pow2 fmt.fracWidth + fracField x := by
            simpa using congrArg Numerics.Dyadic.significand (Option.some.inj hx.symm)
          have hpow : 0 < pow2 fmt.fracWidth := by
            simp [pow2_eq_two_pow]
          omega

/-- A zero value decodes to the zero dyadic, preserving its meaningful sign bit. -/
theorem toDyadic?_eq_zero_of_isZero_eq_true {fmt : FloatFormat}
    (x : Model fmt) (hx : isZero x = true) :
    toDyadic? x = some { negative := signBit x, significand := 0, exponent := 0 } := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  by_cases hieee : fmt.isIEEE = true
  · have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
    have hfields : expField x = 0 ∧ fracField x = 0 := by
      simpa [isZero, hencoding, IEEE.isZero, Bool.and_eq_true] using hx
    have hzeroNotAll : (0 : Nat) ≠ fmt.expAllOnesNat :=
      fun hzero => (FloatFormat.expAllOnesNat_pos fmt).ne' hzero.symm
    simp [toDyadic?, hieee, ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, hfields,
      hzeroNotAll]
  · simp [toDyadic?, hieee, hfinite, hx]

/-- For an exactly decoded finite value, zero classification is the significand-zero test. -/
theorem isZero_eq_beq_zero_of_toDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    isZero x = (d.significand == 0) := by
  by_cases hmant : d.significand = 0
  · simp [hmant, isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hx]
  · have hzero : isZero x = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hxzero
      have hdecode := toDyadic?_eq_zero_of_isZero_eq_true x hxzero
      rw [hx] at hdecode
      have hd :=
        congrArg Numerics.Dyadic.significand (Option.some.inj hdecode)
      exact hmant (by simpa using hd)
    simp [hmant, hzero]

/-- The policy-aware zero constructor always denotes zero. -/
@[simp] theorem isZero_zero (fmt : FloatFormat) (sign : Bool) :
    isZero (zero fmt sign) = true := by
  cases hencoding : fmt.encoding
  · cases sign <;>
      simp [zero, FloatFormat.supportsSignedZero, hencoding, isZero, IEEE.isZero,
        ← ofFields_false_zero_zero, ← ofFields_true_zero_zero]
  · cases sign <;>
      simp [zero, FloatFormat.supportsSignedZero, hencoding, isZero, IEEE.isZero,
        ← ofFields_false_zero_zero, ← ofFields_true_zero_zero]
  · cases sign <;>
      simp [zero, FloatFormat.supportsSignedZero, hencoding, isZero, posZero,
        ofNatBits, ofBits, FloatFormat.ofWordNat]
  · cases sign <;>
      simp [zero, FloatFormat.supportsSignedZero, hencoding, isZero, IEEE.isZero,
        ← ofFields_false_zero_zero, ← ofFields_true_zero_zero]

/-- The policy-aware zero constructor is never a NaN. -/
@[simp] theorem isNaN_zero (fmt : FloatFormat) (sign : Bool) :
    isNaN (zero fmt sign) = false :=
  isNaN_eq_false_of_isFinite_eq_true _ <|
    isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)

/-- The policy-aware zero constructor decodes to the exact zero dyadic. -/
@[simp] theorem toDyadic?_zero (fmt : FloatFormat) (sign : Bool) :
    toDyadic? (zero fmt sign) =
      some { negative := signBit (zero fmt sign), significand := 0, exponent := 0 } :=
  toDyadic?_eq_zero_of_isZero_eq_true (zero fmt sign) (isZero_zero fmt sign)


end Model

end FloatLib.Floats.Formats.BinaryInterchange
