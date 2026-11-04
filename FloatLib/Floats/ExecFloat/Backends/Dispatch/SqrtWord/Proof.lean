/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.SqrtWord.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Sqrt.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Sqrt.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.SquareRoot
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Sqrt.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Sqrt.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Packing
/-!
# Correctness of word-specialized square-root dispatch

Binary32 and binary64 have word kernels of their own. Other descriptors use native one-word decoding
when eligible, or else the generic square-root kernel, and `word_eq_spec` proves that all these
routes agree with `Model.Spec.sqrt` for every input. Fixed-format theorems cover the NaN, infinity,
signed-zero, and negative-input cases, and the positive finite cases reuse the matching kernel
refinements.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Direct binary32 kernel -/

namespace NativeBinary32

/--
Native binary32 square root equals `Model.Spec.sqrt` on every input, including NaNs, infinities,
signed zeros and negative operands.
-/
theorem sqrt_eq_spec (x : Value) :
    sqrt x = Model.Spec.sqrt x := by
  have hcanonical :
      ofUInt32 0x7fc00000 = Model.canonicalNaN FloatFormat.binary32 := by
    decide
  have hexpAll :
      FloatFormat.expAllOnesNat FloatFormat.binary32 = 255 := by
    decide
  unfold NativeBinary32.sqrt
  dsimp only
  rw [expField_beq_allOnes, expField_beq_zero, fracField_beq_zero, signBit_eq]
  by_cases hexponentAllOnes : Model.expField x = 255
  · by_cases hfractionZero : Model.fracField x = 0
    · have hnan : Model.isNaN x = false := by
        change Model.IEEE.isNaN x = false
        simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes, hfractionZero]
      have hinf : Model.isInf x = true := by
        change Model.IEEE.isInf x = true
        simp [Model.IEEE.isInf, hexpAll, hexponentAllOnes, hfractionZero]
      cases hsign : Model.signBit x
      · simp only [hexponentAllOnes, hfractionZero, beq_self_eq_true, ite_true]
        simp [Model.Spec.sqrt, Model.chooseNaN1, hnan, hinf, hsign]
        rw [← ofUInt32_toUInt32 x, ← mkBits_fields (toUInt32 x)]
        rw [signBit_eq, expField_toNat, fracField_toNat, hsign,
          hexponentAllOnes, hfractionZero]
        decide
      · simp [hexponentAllOnes, hfractionZero, hsign, Model.Spec.sqrt,
          Model.chooseNaN1, hnan, hinf, hcanonical]
    · have hnanIEEE : Model.IEEE.isNaN x = true := by
        simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes, hfractionZero]
      have hnan : Model.isNaN x = true := by
        change Model.IEEE.isNaN x = true
        exact hnanIEEE
      have hencoding :
          FloatFormat.binary32.encoding = .ieee := by
        rfl
      simp [hexponentAllOnes, hfractionZero, Model.Spec.sqrt,
        Model.chooseNaN1, Model.quietNaN, hnan, hnanIEEE,
        ofUInt32_or_quietBit, hencoding]
  · have hexponentNotAllOnes :
        Model.expField x ≠
          FloatFormat.expAllOnesNat FloatFormat.binary32 := by
      change Model.expField x ≠ 255
      exact hexponentAllOnes
    have hnan : Model.isNaN x = false := by
      change Model.IEEE.isNaN x = false
      simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes]
    have hinf : Model.isInf x = false := by
      change Model.IEEE.isInf x = false
      simp [Model.IEEE.isInf, hexpAll, hexponentAllOnes]
    by_cases hzeroFields : Model.expField x = 0 ∧ Model.fracField x = 0
    · have hzero : Model.isZero x = true := by
        change Model.IEEE.isZero x = true
        simp [Model.IEEE.isZero, hzeroFields]
      simp [hzeroFields, Model.Spec.sqrt, Model.chooseNaN1, hnan, hinf, hzero]
    have hnonzero : Model.isZero x = false := by
      change Model.IEEE.isZero x = false
      simpa [Model.IEEE.isZero] using hzeroFields
    cases hsign : Model.signBit x
    · -- A positive finite nonzero input takes the model square root.
      have hfinitePolicy : Model.isFinite x = true := by
        change Model.IEEE.isFinite x = true
        exact (bne_iff_ne).2 hexponentNotAllOnes
      rw [Model.Spec.sqrt_eq_model (fmt := FloatFormat.binary32) (by decide) x
        hfinitePolicy hsign]
      simpa [hexponentAllOnes, hzeroFields, hsign] using
        NativeBinary32.sqrt_eq_generic_of_positive_finite x hexponentNotAllOnes hnonzero hsign
    · simp [hexponentAllOnes, hzeroFields, hsign, Model.Spec.sqrt,
        Model.chooseNaN1, hnan, hinf, hnonzero, hcanonical]

end NativeBinary32

/-! ## Direct binary64 kernel -/

namespace NativeBinary64

/--
Native binary64 square root equals `Model.Spec.sqrt` on every input, including NaNs, infinities,
signed zeros and negative operands.
-/
theorem sqrt_eq_spec (x : Value) :
    sqrt x = Model.Spec.sqrt x := by
  unfold sqrt Model.Spec.sqrt
  cases hnan : Model.chooseNaN1 x with
  | some nan =>
      simp
  | none =>
      have hnanFalse : Model.isNaN x = false := by
        unfold Model.chooseNaN1 at hnan
        cases h : Model.isNaN x <;> simp [h] at hnan ⊢
      cases hinf : Model.isInf x with
      | true =>
          simp
      | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases hzero : Model.isZero x with
          | true =>
              simp
          | false =>
              simp only [Bool.false_eq_true, ite_false]
              cases hsign : Model.signBit x with
              | true =>
                  simp
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  have hfinitePolicy : Model.isFinite x = true :=
                    Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnanFalse hinf
                  have hfinite :
                      Model.expField x ≠
                        FloatFormat.expAllOnesNat FloatFormat.binary64 :=
                    (bne_iff_ne).1 hfinitePolicy
                  have hnative :=
                    sqrt_eq_generic_of_positive_finite
                      x hfinite hzero hsign
                  have hpublic :=
                    Model.Spec.sqrt_eq_model
                      (fmt := FloatFormat.binary64) (by decide) x
                      hfinitePolicy hsign
                  simp only [Model.Spec.sqrt, Model.chooseNaN1, hnanFalse,
                    Bool.false_eq_true, ite_false, hinf, hzero, hsign] at hpublic
                  rw [hnative, ← hpublic]

end NativeBinary64

/-! ## Descriptor-driven backend dispatch -/

namespace SqrtBackend

/-- Generic square root agrees with `Spec.sqrt` on every input. -/
theorem generic_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    generic x = Spec.sqrt x := by
  unfold generic
  by_cases hnan : chooseNaN1 x = none
  · rw [withNaNSelection_of_none _ _ hnan]
    unfold Spec.sqrt
    rw [hnan]
    simp only
    by_cases hinf : isInf x = true
    · simp [hinf]
    · have hinfFalse : isInf x = false :=
        Bool.eq_false_of_not_eq_true hinf
      rw [dite_eq_right hinf, ite_eq_right hinf]
      by_cases hzero : isZero x = true
      · simp [hzero]
      · have hzeroFalse : isZero x = false :=
          Bool.eq_false_of_not_eq_true hzero
        rw [dite_eq_right hzero, ite_eq_right hzero]
        by_cases hsignBit : signBit x = true
        · simp [hsignBit]
        · have hsignFalse : signBit x = false :=
            Bool.eq_false_of_not_eq_true hsignBit
          rw [dite_eq_right hsignBit, ite_eq_right hsignBit]
          have hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
          have hfinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false
              x hnotNaN hinfFalse
          obtain ⟨value, hdecode⟩ :=
            exists_toDyadic?_of_isFinite hfinite
          have hvalue : finiteDyadic x hfinite = value :=
            finiteDyadic_eq_of_toDyadic hfinite hdecode
          rw [hdecode,
            FiniteSqrt.sqrtPositiveRuntime_eq_finiteDyadic]
          simp [hvalue]
  · have hselected : ∃ nan, chooseNaN1 x = some nan := by
      cases hchoose : chooseNaN1 x with
      | none => exact (hnan hchoose).elim
      | some nan => exact ⟨nan, rfl⟩
    obtain ⟨nan, hchoose⟩ := hselected
    rw [withNaNSelection_of_some _ _ nan hchoose]
    simp [Spec.sqrt, hchoose]

/-- One-word square root with native decoding agrees with `generic`. -/
theorem smallWord_eq_generic {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x : Model fmt) :
    smallWord heligible x = generic x := by
  unfold smallWord generic
  apply congrArg (withNaNSelection (chooseNaN1 x))
  funext hnan
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [NativeSmallWordSqrt.sqrtPositive_eq, NativeSmallWordFinite.sqrtPositive_eq_runtime]

/-- The width-specialized dispatcher agrees with `Spec.sqrt` on every input. -/
theorem word_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    word x = Spec.sqrt x := by
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    unfold word
    split
    · rename_i h
      have heq :
          FloatFormat.eq_binary32_of_isBinary32 h =
            (rfl : FloatFormat.binary32 = FloatFormat.binary32) :=
        Subsingleton.elim _ _
      rw [heq]
      exact NativeBinary32.sqrt_eq_spec x
    · rename_i h
      exact (h FloatFormat.isBinary32_binary32).elim
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      rw [show word x = NativeBinary64.sqrt x by
        simp [word, h32]]
      exact NativeBinary64.sqrt_eq_spec x
    · by_cases heligible : NativeSmallWord.StorageEligible fmt
      · rw [show word x = smallWord heligible x by
          simp [word, h32, h64, heligible]]
        exact (smallWord_eq_generic heligible x).trans (generic_eq_spec x)
      · simp [word, h32, h64, heligible, generic_eq_spec]

end SqrtBackend
end Model

end FloatLib.Floats.Formats.BinaryInterchange
