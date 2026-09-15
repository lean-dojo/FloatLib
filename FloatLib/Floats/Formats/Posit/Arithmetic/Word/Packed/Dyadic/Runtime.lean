/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.DyadicTarget.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Flattened packed-word exact-dyadic posit arithmetic

Addition, subtraction, multiplication, and fused multiply-add decode finite posits to exact
dyadic fields before one direct rounding step. The logical definitions use `Option Dyadic`;
these kernels pass the decoded fields through continuations instead.

The kernels in this module pass signs, significands, and exponents directly to the
format-independent exact field operations, avoiding intermediate input options and dyadic
records. Their semantic and compiler-refinement proofs live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic

/-! ## Addition -/

/-- Add packed posit words after eliminating decoded input records. -/
@[inline] def addWordsCodeFlat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  NativeWord.withTwoDyadicFields format left right format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.addFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent)

/-- Add two words whose packed carrier has already proved both encodings valid. -/
@[inline] def addWordsCodeFlatValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : Nat :=
  NativeWord.withTwoDyadicFieldsValid format
      heligible
      left hleft right hright format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.addFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent)

/-! ## Subtraction -/

/-- Subtract packed posit words after eliminating decoded input records. -/
@[inline] def subWordsCodeFlat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  NativeWord.withTwoDyadicFields format left right format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.subFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent)

/-- Subtract two words whose packed carrier has already proved both encodings valid. -/
@[inline] def subWordsCodeFlatValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : Nat :=
  NativeWord.withTwoDyadicFieldsValid format
      heligible
      left hleft right hright format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.subFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent)

/-! ## Multiplication -/

/--
Multiply packed posit words after scalar-field elimination.

The product is computed with natural-number significands. The fixed-carrier multiplier in
`Packed.Product` is proved equal to this definition.
-/
@[inline] def mulWordsCodeFlat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  NativeWord.withTwoDyadicFields format left right format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.mulFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent)

/-- Multiply two words whose packed carrier has already proved both encodings valid. -/
@[inline] def mulWordsCodeFlatValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : Nat :=
  NativeWord.withTwoDyadicFieldsValid format
      heligible
      left hleft right hright format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.mulFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent)

/-! ## Fused multiply-add -/

/--
Fuse a packed-word product and addend through scalar exact fields.

`Dyadic.fmaFields` forms the exact product and sum before the sole call to the posit rounder.
-/
@[inline] def fmaWordsCodeFlat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64) : Nat :=
  NativeWord.withThreeDyadicFields format left right addend format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.fmaFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent
          addendNegative addendSignificand addendExponent)

/-- FMA for three words whose packed carrier has proved every encoding valid. -/
@[inline] def fmaWordsCodeFlatValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) : Nat :=
  NativeWord.withThreeDyadicFieldsValid format
      heligible
      left hleft right hright addend haddend format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent =>
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.fmaFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent
          addendNegative addendSignificand addendExponent)

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic
