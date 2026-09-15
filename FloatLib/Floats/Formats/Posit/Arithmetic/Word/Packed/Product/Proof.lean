/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Product.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Proof

/-!
# Correctness of packed native-word Posit multiplication

The product's high limb is an exact capacity certificate. One-limb products use scalar rounding;
two-limb products use the common wide rounder. Both branches refine direct exact-dyadic packing.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedProduct

open FloatLib.Numerics

/-- Capacity-directed product rounding has the shared direct semantics. -/
theorem roundFieldsWord_toNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    (roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent).toNat =
      DirectDyadicPacking.roundCode format
        (Dyadic.mulFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent) := by
  unfold roundFieldsWord
  by_cases hhigh :
      (FixedWord.mul64 leftSignificand rightSignificand).hi = 0
  · simp only [beq_iff_eq, hhigh, ite_true]
    rw [NativeWordRounding.GuardSticky.roundCodeWord_toNat_eq_direct
      format heligible
      (Bool.xor leftNegative rightNegative)
      (FixedWord.mul64 leftSignificand rightSignificand).lo
      (leftExponent + rightExponent)]
    apply congrArg (DirectDyadicPacking.roundCode format)
    apply Dyadic.ext
    · rfl
    · exact FixedWord.mul64_lo_toNat_of_hi_eq_zero
        leftSignificand rightSignificand hhigh
    · rfl
  · simp only [beq_iff_eq, hhigh, ite_false]
    rw [NativeWordLimb.roundCodeWordLow_toNat_eq_direct
      format heligible
      (Bool.xor leftNegative rightNegative)
      (FixedWord.mul64 leftSignificand rightSignificand)
      (leftExponent + rightExponent)]
    apply congrArg (DirectDyadicPacking.roundCode format)
    apply Dyadic.ext
    · rfl
    · exact FixedWord.mul64_toNat leftSignificand rightSignificand
    · rfl

/-- Fixed-carrier product rounding is direct exact-dyadic product rounding. -/
theorem roundFields_eq
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    roundFields format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (Dyadic.mulFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent) := by
  unfold roundFields
  rw [roundFieldsWord_toNat_eq_direct,
    NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct
      format heligible]

/-- Word-valued product rounding returns the same complete code as the shared `Nat` boundary. -/
theorem roundFieldsWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    (roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent).toNat =
      roundFields format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent := by
  rfl

/-- The packed product kernel is the existing exact flattened multiplication. -/
theorem mulWordsCodeValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    mulWordsCodeValid heligible left right hleft hright =
      NativeWordArithmetic.mulWordsCodeFlatValid
        heligible left right hleft hright := by
  unfold mulWordsCodeValid NativeWordArithmetic.mulWordsCodeFlatValid
    NativeWord.withTwoDyadicFieldsValid
  simp only [roundFields_eq]

/-- The carrier-facing product word is the exact code returned by the shared packed multiplier. -/
theorem mulWordsCodeWordValid_toNat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (mulWordsCodeWordValid heligible left right hleft hright).toNat =
      mulWordsCodeValid heligible left right hleft hright := by
  unfold mulWordsCodeWordValid mulWordsCodeValid
  rw [NativeWord.withTwoDyadicWordFieldsValid_toNat,
    NativeWord.signMaskWord_toNat format
      heligible]
  simp only [roundFieldsWord_toNat]

/-- Every packed native product is a complete in-range posit encoding. -/
theorem mulWordsCodeValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    mulWordsCodeValid heligible left right hleft hright <
      format.modulus := by
  rw [mulWordsCodeValid_eq]
  exact NativeWordArithmetic.mulWordsCodeFlatValid_lt_modulus
    heligible left right hleft hright

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedProduct
