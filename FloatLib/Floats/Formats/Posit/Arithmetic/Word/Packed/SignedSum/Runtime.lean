/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Product.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Runtime

/-!
# Packed one-word Posit signed sums

The two-limb signed-sum engine is the common fixed-carrier implementation. One-word decoded
significands first use scalar alignment and signed-magnitude arithmetic whenever the exact
intermediate fits one word. Exact capacity failures continue in the same common two-limb engine,
which uses exact dyadic arithmetic if two limbs are insufficient. Eligible one-word formats
retain the complete result in its low output limb.

Fused multiply-add uses the same rule: `FixedWord.mul64` computes the exact product, a one-limb
product reuses scalar signed addition, and a genuine two-limb product enters the common engine.
Every branch is selected by exact carrier capacity rather than a named format or tuned width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSignedSum

open FloatLib.Numerics

/-- Continue an exact one-word signed sum in the common two-limb carrier. -/
@[noinline] def roundWideFieldsWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    UInt64 :=
  let hlimb : NativeLimb.Eligible format :=
    NativeWordLimb.limbEligible format heligible
  (NativeLimbPacked.SignedSum.roundFieldsWord format hlimb
      leftNegative (NativeWordLimb.widen leftSignificand) leftExponent
      rightNegative (NativeWordLimb.widen rightSignificand) rightExponent).lo

/-- Round two nonzero signed magnitudes already aligned at one exponent. -/
@[noinline] def roundAlignedFieldsWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64)
    (rightNegative : Bool) (rightSignificand : UInt64)
    (exponent : Int) : UInt64 :=
  if leftNegative == rightNegative then
    let sum := FixedWord.add64 leftSignificand rightSignificand
    if sum.carry == 0 then
      NativeWordRounding.GuardSticky.roundCodeWord format heligible
        leftNegative sum.value exponent
    else
      roundWideFieldsWord format heligible
        leftNegative leftSignificand exponent
        rightNegative rightSignificand exponent
  else
    let result :=
      FixedWord.addSignedMagnitudes
        leftNegative rightNegative leftSignificand rightSignificand
    NativeWordRounding.GuardSticky.roundCodeWord format heligible
      result.1 result.2 exponent

/--
Round the exact sum of two decoded one-word Posit dyadics.

Zero operands bypass alignment. Otherwise the larger-exponent significand is shifted exactly
when it remains in one word. A failed scalar capacity check continues in `roundWideFieldsWord`.
-/
@[inline] def roundFieldsWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    UInt64 :=
  if leftSignificand == 0 then
    NativeWordRounding.GuardSticky.roundCodeWord format heligible
      rightNegative rightSignificand rightExponent
  else if rightSignificand == 0 then
    NativeWordRounding.GuardSticky.roundCodeWord format heligible
      leftNegative leftSignificand leftExponent
  else if leftExponent ≤ rightExponent then
    let shift := Int.toNat (rightExponent - leftExponent)
    if _hshift : shift < 64 then
      if _hfit : FixedWord.DyadicCompare.shiftFits rightSignificand shift then
        roundAlignedFieldsWord format heligible
          leftNegative leftSignificand
          rightNegative (rightSignificand <<< UInt64.ofNat shift)
          leftExponent
      else
        roundWideFieldsWord format heligible
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent
    else
      roundWideFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
  else
    let shift := Int.toNat (leftExponent - rightExponent)
    if _hshift : shift < 64 then
      if _hfit : FixedWord.DyadicCompare.shiftFits leftSignificand shift then
        roundAlignedFieldsWord format heligible
          leftNegative (leftSignificand <<< UInt64.ofNat shift)
          rightNegative rightSignificand
          rightExponent
      else
        roundWideFieldsWord format heligible
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent
    else
      roundWideFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

/-- Add two proved-valid packed Posit words and retain the complete result in `UInt64`. -/
@[inline] def addWordsCodeWordValid
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

/-- Subtract two proved-valid packed words by reversing the right decoded sign. -/
@[inline] def subWordsCodeWordValid
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
        (!rightNegative) rightSignificand rightExponent

/-- Continue a genuine two-limb fused product in the common signed-sum engine. -/
@[noinline] def roundWideFmaFieldsWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int)
    (addendNegative : Bool) (addendSignificand : UInt64) (addendExponent : Int) :
    UInt64 :=
  let hlimb : NativeLimb.Eligible format :=
    NativeWordLimb.limbEligible format heligible
  let product := FixedWord.mul64 leftSignificand rightSignificand
  (NativeLimbPacked.SignedSum.roundFieldsWord format hlimb
      (Bool.xor leftNegative rightNegative) product
      (leftExponent + rightExponent)
      addendNegative (NativeWordLimb.widen addendSignificand)
      addendExponent).lo

/--
Round an exact fused product and addend.

A product fitting one word reuses the scalar signed-sum kernel. Otherwise the exact `UInt128`
product enters the common two-limb engine, including its exact-arithmetic capacity fallback.
-/
@[inline] def roundFmaFieldsWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int)
    (addendNegative : Bool) (addendSignificand : UInt64) (addendExponent : Int) :
    UInt64 :=
  let product := FixedWord.mul64 leftSignificand rightSignificand
  if product.hi == 0 then
    roundFieldsWord format heligible
      (Bool.xor leftNegative rightNegative) product.lo
      (leftExponent + rightExponent)
      addendNegative addendSignificand addendExponent
  else
    roundWideFmaFieldsWord format heligible
      leftNegative leftSignificand leftExponent
      rightNegative rightSignificand rightExponent
      addendNegative addendSignificand addendExponent

/-- Fused multiply-add for three proved-valid packed words, with a word-valued result. -/
@[inline] def fmaWordsCodeWordValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) : UInt64 :=
  NativeWord.withThreeDyadicWordFieldsValid format
      heligible
      left hleft right hright addend haddend (NativeWord.signMaskWord format)
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent =>
      roundFmaFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSignedSum
