/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Runtime

/-!
# Packed native-word Posit multiplication

Decoding produces two `UInt64` significands and `FixedWord.mul64` computes their exact product.
Products whose high limb is zero use the scalar guard-and-sticky rounder; genuinely two-limb
products use the common two-limb rounder. The branch is an exact capacity test shared by every
one-word Posit format, not a format-width special case.

`Product.Proof` identifies the fixed-carrier result with direct exact-dyadic packing.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedProduct

open FloatLib.Numerics

/--
Round the exact product while retaining the complete result in a machine word.

The high-limb test proves whether the low limb contains the complete mathematical product.
Eligible one-word formats guarantee that either rounding path returns the complete code.
-/
@[inline] def roundFieldsWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    UInt64 :=
  let product := FixedWord.mul64 leftSignificand rightSignificand
  if product.hi == 0 then
    NativeWordRounding.GuardSticky.roundCodeWord format heligible
      (Bool.xor leftNegative rightNegative) product.lo
      (leftExponent + rightExponent)
  else
    (NativeLimbRounding.GuardSticky.roundCodeWord
        format
        (Bool.xor leftNegative rightNegative) product
        (leftExponent + rightExponent)).lo

/-- Natural-number view of `roundFieldsWord`. -/
@[inline] def roundFields
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    Nat :=
  (roundFieldsWord format heligible
    leftNegative leftSignificand leftExponent
    rightNegative rightSignificand rightExponent).toNat

/--
Multiply two proved-valid packed posit words.

Range proofs and native-word eligibility are propositions and erase after compilation. The only
live inputs are the format fields and two packed words.
-/
@[inline] def mulWordsCodeValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : Nat :=
  NativeWord.withTwoDyadicWordFieldsValid format
      heligible
      left hleft right hright format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFields format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

/--
Multiply two proved-valid packed words and retain the result in `UInt64`.

This is the carrier-facing sibling of `mulWordsCodeValid`. The decoder and arithmetic are shared;
only the final result representation differs.
-/
@[inline] def mulWordsCodeWordValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt64 :=
  NativeWord.withTwoDyadicWordFieldsValid format
      heligible
      left hleft right hright (NativeWord.signMaskWord format)
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedProduct
