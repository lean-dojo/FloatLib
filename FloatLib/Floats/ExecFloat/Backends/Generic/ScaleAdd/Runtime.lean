/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Runtime

/-!
# Executable unsigned-scale exact addition

These kernels align and combine signed magnitudes in an unsigned scale coordinate before entering
the product rounder. `ScaleAdd.Proof` proves agreement with exact dyadic addition and rounding for
conventional IEEE descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd

/--
Numerics.Dyadic exponent represented by an unsigned scale accepted by `FiniteProductRound.round`.

The rounder interprets its scale relative to twice the IEEE subnormal alignment offset. The
additional `roundOffset` lets ordinary addition use one-offset coordinates while FMA uses
two-offset product coordinates.
-/
@[inline] def exponent
    (fmt : FloatFormat) (scale roundOffset : Nat) : Int :=
  Int.ofNat (scale + roundOffset) -
    Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)

/-- Round one signed magnitude from an unsigned scale. -/
@[inline] def roundMagnitude
    (fmt : FloatFormat) (roundOffset : Nat)
    (sign : Bool) (mantissa scale : Nat) : Model fmt :=
  FiniteProductRound.round fmt sign mantissa (scale + roundOffset)

/-- Combine nonzero signed magnitudes at one shared unsigned scale and round once. -/
@[inline] def roundMagnitudes
    (fmt : FloatFormat) (roundOffset : Nat)
    (leftSign rightSign : Bool) (left right scale : Nat) : Model fmt :=
  if leftSign == rightSign then
    roundMagnitude fmt roundOffset leftSign (left + right) scale
  else if left == right then
    zero fmt (leftSign && rightSign)
  else if left < right then
    roundMagnitude fmt roundOffset rightSign (right - left) scale
  else
    roundMagnitude fmt roundOffset leftSign (left - right) scale

/--
Align the higher-scale operand while retaining only the low bits needed for rounding.

When the exponents are well separated, the higher operand determines the sign even after
subtraction. Keeping `fracWidth + 3` positions below it leaves a guard bit above the sticky bit,
including after a borrow. The discarded suffix is tested by shifting back the quotient, so a
large exponent gap does not allocate a correspondingly large power of two.
-/
@[inline] def roundAligned
    (fmt : FloatFormat) (roundOffset : Nat)
    (highSign lowSign : Bool) (high low gap scale : Nat) : Model fmt :=
  let keep := fmt.fracWidth + 3
  -- Keep moderate gaps on exact alignment to avoid jamming a small intermediate.
  if 2 * keep < gap ∧ low.log2 + 1 < gap ∧ high ≠ 0 then
    let discard := gap - keep
    let upper := high <<< keep
    let lower := low >>> discard
    let exact := low == lower <<< discard
    let magnitude :=
      if highSign == lowSign then
        let sum := upper + lower
        if exact then sum else sum ||| 1
      else
        let difference := upper - lower
        if exact then difference else (difference - 1) ||| 1
    roundMagnitude fmt roundOffset highSign magnitude (scale + discard)
  else
    roundMagnitudes fmt roundOffset highSign lowSign (high <<< gap) low scale

/--
Align two signed magnitudes and round their exact sum once, using bounded alignment for large gaps.
-/
@[inline] def roundSum
    (fmt : FloatFormat) (roundOffset : Nat)
    (leftSign rightSign : Bool)
    (leftMantissa leftScale rightMantissa rightScale : Nat) : Model fmt :=
  if leftMantissa == 0 then
    if rightMantissa == 0 then
      zero fmt (leftSign && rightSign)
    else
      roundMagnitude fmt roundOffset rightSign rightMantissa rightScale
  else if rightMantissa == 0 then
    roundMagnitude fmt roundOffset leftSign leftMantissa leftScale
  else if leftScale ≤ rightScale then
    roundAligned fmt roundOffset rightSign leftSign rightMantissa leftMantissa
      (rightScale - leftScale) leftScale
  else
    roundAligned fmt roundOffset leftSign rightSign leftMantissa rightMantissa
      (leftScale - rightScale) rightScale

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd
