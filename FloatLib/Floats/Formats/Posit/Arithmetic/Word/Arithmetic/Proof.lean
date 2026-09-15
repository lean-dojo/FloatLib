/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Decode.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Proof

public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Proof

/-!
# Correctness of native-word posit arithmetic

Every direct stored-word result is a valid posit encoding, and each stored-word kernel
re-encodes to the width-generic direct kernel in `DirectDyadicArithmetic` applied to the decoded
operands. Refinement to the rational specification then follows from
`DirectDyadicArithmetic.add_eq_spec` and its siblings.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic

open FloatLib.Numerics

variable {format : Format}

/-! ## Encoding bounds -/

/-- Every direct addition result is a valid complete encoding. -/
theorem addWordsCode_lt_modulus
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    addWordsCode heligible left right < format.modulus := by
  unfold addWordsCode
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
    first
    | exact format.signMaskNat_lt_modulus
    | exact DirectDyadicPacking.roundCode_lt_modulus format _

/-- Every direct subtraction result is a valid complete encoding. -/
theorem subWordsCode_lt_modulus
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    subWordsCode heligible left right < format.modulus := by
  unfold subWordsCode
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
    first
    | exact format.signMaskNat_lt_modulus
    | exact DirectDyadicPacking.roundCode_lt_modulus format _

/-- Every direct multiplication result is a valid complete encoding. -/
theorem mulWordsCode_lt_modulus
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    mulWordsCode heligible left right < format.modulus := by
  unfold mulWordsCode
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
    first
    | exact format.signMaskNat_lt_modulus
    | exact DirectDyadicPacking.roundCode_lt_modulus format _

/-- Every direct division result is a valid complete encoding. -/
theorem divWordsCode_lt_modulus
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    divWordsCode heligible left right < format.modulus := by
  unfold divWordsCode
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
    first
    | exact format.signMaskNat_lt_modulus
    | exact DirectDyadicQuotient.roundCode_lt_modulus format _ _

/-- Every direct square-root result is a valid complete encoding. -/
theorem sqrtWordCode_lt_modulus
    (heligible : NativeWord.Eligible format)
    (value : UInt64) :
    sqrtWordCode heligible value < format.modulus := by
  unfold sqrtWordCode
  cases NativeWord.toDyadic? format value with
  | none =>
      exact format.signMaskNat_lt_modulus
  | some radicand =>
      change
        (if radicand.isLess FloatLib.Numerics.Dyadic.zero = true then
          format.signMaskNat
        else
          DirectDyadicSquareRoot.roundCode format radicand) <
          format.modulus
      by_cases hnegative :
          radicand.isLess FloatLib.Numerics.Dyadic.zero = true
      · rw [ite_eq_left hnegative]
        exact format.signMaskNat_lt_modulus
      · rw [ite_eq_right hnegative]
        exact DirectDyadicSquareRoot.roundCode_lt_modulus
          format radicand

/-- Every direct fused result is a valid complete encoding. -/
theorem fmaWordsCode_lt_modulus
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64) :
    fmaWordsCode heligible left right addend < format.modulus := by
  unfold fmaWordsCode
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
      cases NativeWord.toDyadic? format addend <;>
    first
    | exact format.signMaskNat_lt_modulus
    | exact DirectDyadicPacking.roundCode_lt_modulus format _

/-! ## Stored-word representation -/

/-- The direct addition code re-encodes to the model-valued word kernel. -/
theorem ofNatBits_addWordsCode
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    Model.ofNatBits (addWordsCode heligible left right) =
      addWords heligible left right :=
  rfl

/-- The direct subtraction code re-encodes to the model-valued word kernel. -/
theorem ofNatBits_subWordsCode
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    Model.ofNatBits (subWordsCode heligible left right) =
      subWords heligible left right :=
  rfl

/-- The direct multiplication code re-encodes to the model-valued word kernel. -/
theorem ofNatBits_mulWordsCode
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    Model.ofNatBits (mulWordsCode heligible left right) =
      mulWords heligible left right :=
  rfl

/-- The direct division code re-encodes to the model-valued word kernel. -/
theorem ofNatBits_divWordsCode
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    Model.ofNatBits (divWordsCode heligible left right) =
      divWords heligible left right :=
  rfl

/-- The direct square-root code re-encodes to the model-valued word kernel. -/
theorem ofNatBits_sqrtWordCode
    (heligible : NativeWord.Eligible format)
    (value : UInt64) :
    Model.ofNatBits (sqrtWordCode heligible value) =
      sqrtWord heligible value :=
  rfl

/-- The direct fused code re-encodes to the model-valued word kernel. -/
theorem ofNatBits_fmaWordsCode
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64) :
    Model.ofNatBits (fmaWordsCode heligible left right addend) =
      fmaWords heligible left right addend :=
  rfl

/-- Direct stored-word addition is the direct kernel applied to the decoded operands. -/
theorem addWords_eq_add
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    addWords heligible left right =
      DirectDyadicArithmetic.add
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold addWords addWordsCode DirectDyadicArithmetic.add
  rw [NativeWord.toDyadic?_eq_model format left
      heligible hleft,
    NativeWord.toDyadic?_eq_model format right
      heligible hright]
  split <;>
    simp_all only [DirectDyadicPacking.ofNatBits_roundCode, Model.nar]

/-- Direct stored-word subtraction is the direct kernel applied to the decoded operands. -/
theorem subWords_eq_sub
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    subWords heligible left right =
      DirectDyadicArithmetic.sub
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold subWords subWordsCode DirectDyadicArithmetic.sub
  rw [NativeWord.toDyadic?_eq_model format left
      heligible hleft,
    NativeWord.toDyadic?_eq_model format right
      heligible hright]
  split <;>
    simp_all only [DirectDyadicPacking.ofNatBits_roundCode, Model.nar]

/-- Direct stored-word multiplication is the direct kernel applied to the decoded operands. -/
theorem mulWords_eq_mul
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    mulWords heligible left right =
      DirectDyadicArithmetic.mul
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold mulWords mulWordsCode DirectDyadicArithmetic.mul
  rw [NativeWord.toDyadic?_eq_model format left
      heligible hleft,
    NativeWord.toDyadic?_eq_model format right
      heligible hright]
  split <;>
    simp_all only [DirectDyadicPacking.ofNatBits_roundCode, Model.nar]

/-- Direct stored-word division is the direct kernel applied to the decoded operands. -/
theorem divWords_eq_div
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    divWords heligible left right =
      DirectDyadicArithmetic.div
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold divWords divWordsCode DirectDyadicArithmetic.div
    DirectDyadicArithmetic.divDecoded
  rw [NativeWord.toDyadic?_eq_model format left
      heligible hleft,
    NativeWord.toDyadic?_eq_model format right
      heligible hright]
  split <;>
    simp_all only [DirectDyadicQuotient.ofNatBits_roundCode, Model.nar]

/-- Direct stored-word square root is the direct kernel applied to the decoded operands. -/
theorem sqrtWord_eq_sqrt
    (heligible : NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) :
    sqrtWord heligible value =
      DirectDyadicArithmetic.sqrt
        (Model.ofNatBits (format := format) value.toNat) := by
  unfold sqrtWord sqrtWordCode DirectDyadicArithmetic.sqrt
  rw [NativeWord.toDyadic?_eq_model format value
    heligible hvalue]
  split
  · simp_all only [Model.nar]
  · rename_i radicand hdecode
    by_cases hnegative :
        radicand.isLess FloatLib.Numerics.Dyadic.zero = true <;>
      simp_all [DirectDyadicSquareRoot.ofNatBits_roundCode,
        Model.nar]

/-- Direct stored-word FMA is the direct kernel applied to the decoded operands. -/
theorem fmaWords_eq_fma
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    fmaWords heligible left right addend =
      DirectDyadicArithmetic.fma
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat)
        (Model.ofNatBits (format := format) addend.toNat) := by
  unfold fmaWords fmaWordsCode DirectDyadicArithmetic.fma
  rw [NativeWord.toDyadic?_eq_model format left
      heligible hleft,
    NativeWord.toDyadic?_eq_model format right
      heligible hright,
    NativeWord.toDyadic?_eq_model format addend
      heligible haddend]
  split <;>
    simp_all only [DirectDyadicPacking.ofNatBits_roundCode, Model.nar]

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic
