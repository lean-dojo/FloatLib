/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.DyadicTarget.Proof
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Correctness of flattened packed-word exact-dyadic posit arithmetic

The flattened packed-word kernels agree with the shared exact-dyadic operations, preserve the
complete posit encoding range, and admit verified compiler substitutions. Executable definitions
live in `FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Runtime`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic

/-! ## Addition -/

/-- Flattened scalar-field addition is the exact packed-word addition. -/
theorem addWordsCodeFlat_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    addWordsCodeFlat heligible left right =
      addWordsCode heligible left right := by
  unfold addWordsCodeFlat addWordsCode
  rw [NativeWord.withTwoDyadicFields_eq]
  cases hleft : NativeWord.toDyadic? format left with
  | none =>
      rfl
  | some leftValue =>
      cases hright : NativeWord.toDyadic? format right with
      | none =>
          rfl
      | some rightValue =>
          cases leftValue
          cases rightValue
          simp only [
            NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
            FloatLib.Numerics.Dyadic.addFields_eq]

/-- Valid-word addition is exactly flattened packed-word addition. -/
theorem addWordsCodeFlatValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    addWordsCodeFlatValid heligible left right hleft hright =
      addWordsCodeFlat heligible left right := by
  unfold addWordsCodeFlatValid addWordsCodeFlat
  simp only [NativeWord.withTwoDyadicFieldsValid_eq]

/-- Every valid-word addition result is a complete in-range posit encoding. -/
theorem addWordsCodeFlatValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    addWordsCodeFlatValid heligible left right hleft hright <
      format.modulus := by
  rw [addWordsCodeFlatValid_eq heligible left right hleft hright,
    addWordsCodeFlat_eq]
  exact addWordsCode_lt_modulus heligible left right

/-- Compile exact packed addition through scalar-field elimination. -/
@[csimp] theorem addWordsCode_eq_addWordsCodeFlat :
    @addWordsCode = @addWordsCodeFlat := by
  funext format heligible left right
  exact (addWordsCodeFlat_eq heligible left right).symm

/-! ## Subtraction -/

/-- Flattened scalar-field subtraction is the exact packed-word subtraction. -/
theorem subWordsCodeFlat_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    subWordsCodeFlat heligible left right =
      subWordsCode heligible left right := by
  unfold subWordsCodeFlat subWordsCode
  rw [NativeWord.withTwoDyadicFields_eq]
  cases hleft : NativeWord.toDyadic? format left with
  | none =>
      rfl
  | some leftValue =>
      cases hright : NativeWord.toDyadic? format right with
      | none =>
          rfl
      | some rightValue =>
          cases leftValue
          cases rightValue
          simp only [
            NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
            FloatLib.Numerics.Dyadic.subFields_eq]

/-- Valid-word subtraction is exactly flattened packed-word subtraction. -/
theorem subWordsCodeFlatValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    subWordsCodeFlatValid heligible left right hleft hright =
      subWordsCodeFlat heligible left right := by
  unfold subWordsCodeFlatValid subWordsCodeFlat
  simp only [NativeWord.withTwoDyadicFieldsValid_eq]

/-- Every valid-word subtraction result is a complete in-range posit encoding. -/
theorem subWordsCodeFlatValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    subWordsCodeFlatValid heligible left right hleft hright <
      format.modulus := by
  rw [subWordsCodeFlatValid_eq heligible left right hleft hright,
    subWordsCodeFlat_eq]
  exact subWordsCode_lt_modulus heligible left right

/-- Compile exact packed subtraction through scalar-field elimination. -/
@[csimp] theorem subWordsCode_eq_subWordsCodeFlat :
    @subWordsCode = @subWordsCodeFlat := by
  funext format heligible left right
  exact (subWordsCodeFlat_eq heligible left right).symm

/-! ## Multiplication -/

/-- Flattened scalar-field multiplication is the exact packed-word multiplier. -/
theorem mulWordsCodeFlat_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) :
    mulWordsCodeFlat heligible left right =
      mulWordsCode heligible left right := by
  unfold mulWordsCodeFlat mulWordsCode
  rw [NativeWord.withTwoDyadicFields_eq]
  cases hleft : NativeWord.toDyadic? format left with
  | none =>
      rfl
  | some leftValue =>
      cases hright : NativeWord.toDyadic? format right with
      | none =>
          rfl
      | some rightValue =>
          cases leftValue
          cases rightValue
          simp only [
            NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
            FloatLib.Numerics.Dyadic.mulFields_eq]

/-- Valid-word multiplication is exactly flattened packed-word multiplication. -/
theorem mulWordsCodeFlatValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    mulWordsCodeFlatValid heligible left right hleft hright =
      mulWordsCodeFlat heligible left right := by
  unfold mulWordsCodeFlatValid mulWordsCodeFlat
  simp only [NativeWord.withTwoDyadicFieldsValid_eq]

/-- Every valid-word multiplication result is a complete in-range posit encoding. -/
theorem mulWordsCodeFlatValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    mulWordsCodeFlatValid heligible left right hleft hright <
      format.modulus := by
  rw [mulWordsCodeFlatValid_eq heligible left right hleft hright,
    mulWordsCodeFlat_eq]
  exact mulWordsCode_lt_modulus heligible left right

/-- Compile exact packed multiplication through scalar-field elimination. -/
@[csimp] theorem mulWordsCode_eq_mulWordsCodeFlat :
    @mulWordsCode = @mulWordsCodeFlat := by
  funext format heligible left right
  exact (mulWordsCodeFlat_eq heligible left right).symm

/-! ## Fused multiply-add -/

/-- Flattened scalar-field FMA is the exact packed-word FMA. -/
theorem fmaWordsCodeFlat_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64) :
    fmaWordsCodeFlat heligible left right addend =
      fmaWordsCode heligible left right addend := by
  unfold fmaWordsCodeFlat fmaWordsCode
  rw [NativeWord.withThreeDyadicFields_eq]
  cases hleft : NativeWord.toDyadic? format left with
  | none =>
      rfl
  | some leftValue =>
      cases hright : NativeWord.toDyadic? format right with
      | none =>
          rfl
      | some rightValue =>
          cases haddend : NativeWord.toDyadic? format addend with
          | none =>
              rfl
          | some addendValue =>
              cases leftValue
              cases rightValue
              cases addendValue
              simp only [
                NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
                FloatLib.Numerics.Dyadic.fmaFields_eq]

/-- Valid-word FMA is exactly flattened packed-word FMA. -/
theorem fmaWordsCodeFlatValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    fmaWordsCodeFlatValid heligible
        left right addend hleft hright haddend =
      fmaWordsCodeFlat heligible left right addend := by
  unfold fmaWordsCodeFlatValid fmaWordsCodeFlat
  simp only [NativeWord.withThreeDyadicFieldsValid_eq]

/-- Every valid-word FMA result is a complete in-range posit encoding. -/
theorem fmaWordsCodeFlatValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    fmaWordsCodeFlatValid heligible
        left right addend hleft hright haddend <
      format.modulus := by
  rw [fmaWordsCodeFlatValid_eq heligible
      left right addend hleft hright haddend,
    fmaWordsCodeFlat_eq]
  exact fmaWordsCode_lt_modulus heligible left right addend

/-- Compile exact packed FMA through scalar-field elimination. -/
@[csimp] theorem fmaWordsCode_eq_fmaWordsCodeFlat :
    @fmaWordsCode = @fmaWordsCodeFlat := by
  funext format heligible left right addend
  exact (fmaWordsCodeFlat_eq heligible left right addend).symm

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic
