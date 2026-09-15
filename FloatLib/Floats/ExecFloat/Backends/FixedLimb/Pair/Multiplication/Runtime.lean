/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Optimized
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime

/-!
# Two-word multiplication runtime

The partial four-limb product kernel multiplies normal operands in every eligible two-word
layout. The operation dispatcher owns the exact baseline for declined cases. Refinement proofs
are isolated in `Multiplication.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Round and pack a four-limb normal product whose leading set bit is at position `leading`.

The product of two normal significands, or the aligned sum used by fused multiply-add, is
rounded to `fracWidth + 1` bits by shifting out `leading - fracWidth` bits with ties to even. A
magnitude below the normal range, or a rounded result above the largest finite exponent, is
declined.
-/
@[inline] def roundNormalProduct? {fmt : FloatFormat} (sign : Bool) (xExponent yExponent : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt256) (leading : UInt64) : Option (Model fmt) :=
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  if position < UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1) then
    none
  else
    let rounded :=
      product.roundShiftRightEven128 (leading - UInt64.ofNat fmt.fracWidth).toNat
    let carry := isCarry fmt rounded
    let normalizedPosition := if carry then position + 1 else position
    if UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) < normalizedPosition then
      none
    else
      some <| packNormal fmt sign
        (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2))
        (normalizeCarry fmt carry rounded)

/-- Multiply two decoded normal significands in fixed limbs. -/
@[inline] def roundNormalLimb? {fmt : FloatFormat} (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa : FloatLib.Numerics.FixedWord.UInt128) : Option (Model fmt) :=
  let product := FloatLib.Numerics.FixedWord.mul128 xMantissa yMantissa
  roundNormalProduct? sign xExponent yExponent product (UInt64.ofNat product.log2)

/--
Decode two values and try the fixed-limb normal product.

Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def mulNormalLimb? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt then
    none
  else
    roundNormalLimb?
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      xExponent yExponent
      (normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo)
      (normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
