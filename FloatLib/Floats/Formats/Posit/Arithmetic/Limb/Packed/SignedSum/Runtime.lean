/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.DyadicCompare.Runtime
public import FloatLib.Kernels.FixedWord.SignedMagnitude.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Packed two-limb Posit signed sums

Packed two-limb signed sums align decoded dyadic fields, combine their signed magnitudes, and
round within `UInt128` whenever the exact intermediate fits that carrier. The sole exact
capacity branch is selected by native shift and carry checks; it preserves the same general
dyadic semantics for intermediates that genuinely require more than 128 bits.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.SignedSum

open FloatLib.Numerics

/-- Exact capacity branch for a signed sum whose aligned magnitude does not fit in two limbs. -/
@[noinline] def roundCapacityFieldsWord
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (rightExponent : Int) : FixedWord.UInt128 :=
  FixedWord.UInt128.ofNat <|
    NativeLimbRounding.roundCodeNat format heligible <|
      Dyadic.addFields
        leftNegative leftSignificand.toNat leftExponent
        rightNegative rightSignificand.toNat rightExponent

/-- Round two nonzero signed magnitudes already aligned at one exponent. -/
@[noinline] def roundAlignedFieldsWord
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (exponent : Int) : FixedWord.UInt128 :=
  if leftNegative == rightNegative then
    let sum := FixedWord.add128 leftSignificand rightSignificand
    if sum.carry == 0 then
      NativeLimbRounding.GuardSticky.roundCodeWord format
        leftNegative sum.value exponent
    else
      roundCapacityFieldsWord format heligible
        leftNegative leftSignificand exponent
        rightNegative rightSignificand exponent
  else
    let result :=
      FixedWord.addSignedMagnitudes128
        leftNegative rightNegative leftSignificand rightSignificand
    NativeLimbRounding.GuardSticky.roundCodeWord format
      result.1 result.2 exponent

/--
Round the exact sum of two decoded native dyadics.

Zero operands bypass alignment. A nonzero operand with the larger exponent is shifted to the
smaller exponent when its exact value remains in two limbs. Failed capacity checks enter the one
exact wider-intermediate branch.
-/
@[inline] def roundFieldsWord
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (rightExponent : Int) : FixedWord.UInt128 :=
  if NativeLimb.isZero leftSignificand then
    NativeLimbRounding.GuardSticky.roundCodeWord format
      rightNegative rightSignificand rightExponent
  else if NativeLimb.isZero rightSignificand then
    NativeLimbRounding.GuardSticky.roundCodeWord format
      leftNegative leftSignificand leftExponent
  else if leftExponent ≤ rightExponent then
    let shift := Int.toNat (rightExponent - leftExponent)
    if _hshift : shift < 128 then
      if _hfit : FixedWord.DyadicCompare.shiftFits128 rightSignificand shift then
        roundAlignedFieldsWord format heligible
          leftNegative leftSignificand
          rightNegative (FixedWord.UInt128.shiftLeft rightSignificand shift)
          leftExponent
      else
        roundCapacityFieldsWord format heligible
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent
    else
      roundCapacityFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
  else
    let shift := Int.toNat (leftExponent - rightExponent)
    if _hshift : shift < 128 then
      if _hfit : FixedWord.DyadicCompare.shiftFits128 leftSignificand shift then
        roundAlignedFieldsWord format heligible
          leftNegative (FixedWord.UInt128.shiftLeft leftSignificand shift)
          rightNegative rightSignificand
          rightExponent
      else
        roundCapacityFieldsWord format heligible
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent
    else
      roundCapacityFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

/-- Add two packed Posit words and retain the complete result in two native limbs. -/
@[inline] def addWordsCodeWord
    {format : Format} (heligible : NativeLimb.Eligible format)
    (left right : FixedWord.UInt128) : FixedWord.UInt128 :=
  NativeLimb.withTwoDyadicFields format left right
    (NativeLimb.signMaskWord format)
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

/-- Subtract two packed Posit words by reversing the right decoded sign. -/
@[inline] def subWordsCodeWord
    {format : Format} (heligible : NativeLimb.Eligible format)
    (left right : FixedWord.UInt128) : FixedWord.UInt128 :=
  NativeLimb.withTwoDyadicFields format left right
    (NativeLimb.signMaskWord format)
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        (!rightNegative) rightSignificand rightExponent

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.SignedSum
