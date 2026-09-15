/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.LimbRound.Runtime
public import FloatLib.Kernels.FixedWord.Product.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Runtime

/-!
# Direct packed-pair posit multiplication runtime

The packed-pair multiplication kernel returns posit codes for configured values stored in two
native limbs. Range and semantic refinement proofs live in `Mul.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/--
Decode two packed operands, multiply their significands in four native limbs, and return the
complete result encoding in two native limbs.

The exact product is normalized with a sticky low bit before rounding. Significands, the product,
and the result code stay in fixed-width carriers; exponents and bit counts use `Int` and `Nat`.
-/
@[noinline] def mulCode
    (_heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  NativeLimb.withTwoDyadicFields format left right
    (NativeLimb.signMaskWord format)
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      let product :=
        FloatLib.Numerics.FixedWord.mul128
          leftSignificand rightSignificand
      NativeLimbRounding.GuardSticky.roundCodeWord format
        (Bool.xor leftNegative rightNegative)
        product.normalizeJam128
        (leftExponent + rightExponent +
          Int.ofNat product.normalizationShift128)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
