/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime
public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Native binary32 product rounding

The machine-word product rounder serves multiplication, aligned addition, and fused
multiply-add. Its correctness theorem lives in `Rounding.Proof`, keeping execution-only imports
independent of the proof development.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
Round the signed magnitude `product * 2^(scale - 298)` to binary32, with sign `sign` and
subtraction in `Int`.

Correctness holds for every `UInt64` magnitude when `scale ≤ 506`; callers establish this bound.
In particular, finite multiplication supplies a product below `2^48`.
-/
@[inline] def roundProduct (sign : Bool) (product scale : UInt64) : UInt32 :=
  if product == 0 then
    if sign then 0x80000000 else 0
  else
    let leading := product.log2
    let position := leading + scale
    if position < 172 then
      let fraction :=
        if scale < 149 then
          FloatLib.Numerics.FixedWord.roundShiftRightEven product (149 - scale).toNat
        else
          product <<< (scale - 149)
      if fraction == 0 then
        if sign then 0x80000000 else 0
      else if fraction == 0x800000 then
        mkBits sign 1 0
      else
        mkBits sign 0 fraction.toNat
    else
      let roundedMantissa :=
        if leading < 23 then
          product <<< (23 - leading)
        else
          FloatLib.Numerics.FixedWord.roundShiftRightEven product (leading - 23).toNat
      let carry := roundedMantissa == 0x1000000
      let normalizedPosition := if carry then position + 1 else position
      if normalizedPosition > 425 then
        if sign then 0xff800000 else 0x7f800000
      else
        let normalizedMantissa := if carry then 0x800000 else roundedMantissa
        let encodedExponent := normalizedPosition - 171
        let fraction := normalizedMantissa.toNat - 0x800000
        mkBits sign encodedExponent.toNat fraction

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
