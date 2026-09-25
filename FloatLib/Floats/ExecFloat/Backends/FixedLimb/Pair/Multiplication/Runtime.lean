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

open FloatLib.Numerics.FixedWord

/--
Multiply two two-word values into four limbs.

Keeping each column sum and carry as a native word avoids boxing the polymorphic `AddResult`
values used by `mul128`. The four output words are identical.
-/
@[inline] def multiplyLimbs (x y : UInt128) : UInt256 :=
  let p00 := mul64 x.lo y.lo
  let p01 := mul64 x.lo y.hi
  let p10 := mul64 x.hi y.lo
  let p11 := mul64 x.hi y.hi
  let first1 := p00.hi + p01.lo
  let second1 := first1 + p10.lo
  let carry1 :=
    (if first1 < p00.hi then (1 : UInt64) else 0) +
      (if second1 < first1 then 1 else 0)
  let first2 := p01.hi + p10.hi
  let second2 := first2 + p11.lo
  let third2 := second2 + carry1
  let carry2 :=
    (if first2 < p01.hi then (1 : UInt64) else 0) +
      (if second2 < first2 then 1 else 0) +
      (if third2 < second2 then 1 else 0)
  ⟨p11.hi + carry2, third2, second1, p00.lo⟩

/--
Round with the convention of `UInt256.roundShiftRightEven128`, keeping the increment and its
carry as scalar words. Its mathematical rounding contract requires `64 < shift < 128`; the
total function also agrees with that kernel outside this range.
-/
@[inline] def roundProduct (value : UInt256) (shift : Nat) : UInt128 :=
  let quotient := value.shiftRight128 shift
  let inner := shift - 64
  let highRemainder := value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1)
  let halfHigh := (1 : UInt64) <<< UInt64.ofNat (inner - 1)
  let increment : UInt64 :=
    if highRemainder < halfHigh then 0
    else if highRemainder > halfHigh || value.limb0 != 0 then 1
    else if (quotient.lo &&& 1) == 0 then 0 else 1
  let roundedLo := quotient.lo + increment
  ⟨quotient.hi + (if roundedLo < quotient.lo then 1 else 0), roundedLo⟩

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
      roundProduct product (leading - UInt64.ofNat fmt.fracWidth).toNat
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
  let product := multiplyLimbs xMantissa yMantissa
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
