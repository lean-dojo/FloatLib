/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Core

/-!
# Executable unsigned-scale rounding for finite products

This arbitrary-precision kernel rounds a finite product directly from its unsigned field scale.
For conventional IEEE descriptors, `ProductRound.Proof` proves agreement with the public dyadic
rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteProductRound

/--
Round the magnitude `product * 2^(scale - 2 * ieeeSubnormalAlignExp fmt)` with sign `sign`.

The exponent subtraction is interpreted in `Int`. The numerical refinement assumes a conventional
IEEE descriptor.

The thresholds are written in the same unsigned coordinate:

* `bias + 2 * fracWidth - 1` is the first normal leading-bit position;
* `3 * bias + 2 * fracWidth - 2` is the largest finite normal leading-bit position.
-/
@[inline] def round (fmt : FloatFormat)
    (sign : Bool) (product scale : Nat) : Model fmt :=
  if product == 0 then
    if sign then negZero fmt else posZero fmt
  else
    let leading := product.log2
    let position := leading + scale
    let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
    if position < normalThreshold then
      let align := FloatFormat.ieeeSubnormalAlignExp fmt
      let fraction :=
        if scale < align then
          Numerics.roundShiftRightEven product (align - scale)
        else
          product <<< (scale - align)
      if fraction == 0 then
        if sign then negZero fmt else posZero fmt
      else if fraction == pow2 fmt.fracWidth then
        ofFields fmt sign 1 0
      else
        ofFields fmt sign 0 fraction
    else
      let roundedMantissa :=
        if fmt.fracWidth ≤ leading then
          Numerics.roundShiftRightEven product (leading - fmt.fracWidth)
        else
          product <<< (fmt.fracWidth - leading)
      let carry := roundedMantissa == pow2 (fmt.fracWidth + 1)
      let normalizedPosition := if carry then position + 1 else position
      let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
      if overflowThreshold < normalizedPosition then
        if sign then negInf fmt else posInf fmt
      else
        let normalizedMantissa :=
          if carry then pow2 fmt.fracWidth else roundedMantissa
        let exponentOffset := fmt.bias + 2 * fmt.fracWidth - 2
        ofFields fmt sign
          (normalizedPosition - exponentOffset)
          (normalizedMantissa - pow2 fmt.fracWidth)

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteProductRound
