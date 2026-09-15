/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.RestoringSqrt.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime

/-!
# Packed native-word Posit square root

The packed square-root adapter connects native posit storage to the width-generic direct kernel.
A proved-valid `UInt64` encoding is decoded once into native dyadic fields. A fixed-word
restoring root computes the complete destination-width prefix and the common two-limb
guard/sticky packer selects the Posit code. The significand, root, and remainder stay in
fixed-width carriers.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSquareRoot

open FloatLib.Numerics
open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.RestoringSquareRoot

/--
Scale one native significand for destination-width square-root prefix generation.

For an eligible one-word Posit, `payloadBits ≤ 63`; exponent parity therefore makes `shift < 128`.
The exact product fits below bit 192 and is consumed by the 96-digit restoring kernel.
-/
@[inline] def scaledRadicandWord
    (significand : UInt64) (shift : Nat) : UInt256 :=
  mul128
    { hi := 0, lo := significand }
    (UInt128.shiftLeft { hi := 0, lo := 1 } shift)

/-- Round decoded native fields through the exact fixed-word root prefix. -/
@[inline] def roundFieldsWord
    (format : Format) (_heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) : UInt64 :=
  if significand == 0 then
    0
  else if negative then
    NativeWord.signMaskWord format
  else
    let precision := format.payloadBits
    let parity := (exponent.emod 2).toNat
    let scaled :=
      scaledRadicandWord significand (parity + 2 * precision)
    let state := rootAndRemainder scaled 96
    let rootPrefix :=
      if NativeLimb.isZero state.remainder then
        state.root
      else
        state.root.setLowBit
    (NativeLimbRounding.GuardSticky.roundCodeWord
      format false rootPrefix
      (exponent.ediv 2 - Int.ofNat precision)).lo

/-- Complete square-root code retained in the native storage carrier. -/
@[inline] def sqrtWordCodeWordValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) : UInt64 :=
  NativeWord.withDyadicWordFieldsValid format
    heligible value hvalue (NativeWord.signMaskWord format)
    fun negative significand exponent =>
      roundFieldsWord format heligible negative significand exponent

/-- Natural-number view of the complete native square-root code. -/
@[inline] def sqrtWordCodeValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) : Nat :=
  (sqrtWordCodeWordValid heligible value hvalue).toNat

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSquareRoot
