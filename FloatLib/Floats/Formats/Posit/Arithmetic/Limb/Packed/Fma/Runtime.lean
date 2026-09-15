/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Runtime
public import FloatLib.Kernels.FixedWord.Product.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Direct packed-pair posit fused multiply-add runtime

The packed-pair fused multiply-add kernel returns posit codes for configured values stored in
two native limbs. Range and semantic refinement proofs live in `Fma.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/--
Decode three operands, form the exact product in four native limbs, add without intermediate
rounding, and return the result code.

The product crosses to the shared arbitrary-precision sum only once. This avoids allocating two
input dyadics and avoids generic big-integer multiplication.
-/
@[noinline] def fmaCode
    (heligible : NativeLimb.Eligible format)
    (left right addend : FloatLib.Numerics.FixedWord.UInt128) : Nat :=
  NativeLimb.withThreeDyadicFields format left right addend format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent =>
      NativeLimbRounding.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.addFields
          (Bool.xor leftNegative rightNegative)
          (FloatLib.Numerics.FixedWord.mul128
            leftSignificand rightSignificand).toNat
          (leftExponent + rightExponent)
          addendNegative addendSignificand.toNat addendExponent)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
