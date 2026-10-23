/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Kernels.FixedWord.Core.Runtime
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# Native-storage binary64 runtime

Binary64 uses the same generic `Model` as every binary-interchange format, but its 64-bit
encoding fits in one `UInt64`. These adapters hand that native storage to the finite kernels
without a second user-visible value type.

Field extraction, packing and exact intermediate arithmetic live here. Exceptional IEEE behavior
stays in the shared dispatcher, and `Core.Proof` proves that the native-word routines agree with
the generic model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

/-- The generic binary64 carrier. -/
abbrev Value := Model FloatFormat.binary64

/-- View generic binary64 storage as a native word. -/
@[inline] def toUInt64 (x : Value) : UInt64 :=
  UInt64.ofBitVec x.bits

/-- Rewrap a native binary64 word in the generic carrier. -/
@[inline] def ofUInt64 (bits : UInt64) : Value :=
  Model.ofBits bits.toBitVec

/-- Toggle the binary64 sign bit without generic `BitVec` arithmetic. -/
@[inline] def negate (x : Value) : Value :=
  ofUInt64 (toUInt64 x ^^^ 0x8000000000000000)

/-- Extract the binary64 sign from a native word. -/
@[inline] def signBit (bits : UInt64) : Bool :=
  (bits &&& 0x8000000000000000) != 0

/-- Extract the binary64 biased exponent from a native word. -/
@[inline] def expField (bits : UInt64) : UInt64 :=
  (bits >>> 52) &&& 0x7ff

/-- Extract the binary64 fraction from a native word. -/
@[inline] def fracField (bits : UInt64) : UInt64 :=
  bits &&& 0x000fffffffffffff

/-- Pack binary64 sign, exponent and fraction fields into a native storage word. -/
@[inline] def packFieldsWord
    (sign : Bool) (exponent fraction : UInt64) : UInt64 :=
  (if sign then (1 : UInt64) <<< 63 else 0) |||
    ((exponent &&& 0x7ff) <<< 52) |||
    (fraction &&& 0x000fffffffffffff)

/-- Decode the finite binary64 significand, including the implicit bit for normal values. -/
@[inline] def finiteMantissa (exponent fraction : UInt64) : UInt64 :=
  if exponent == 0 then fraction else fraction ||| 0x0010000000000000

/--
Round the normalized two-limb magnitude `product * 2 ^ (scale - 2 * 1074)`, with sign `sign` and
given its leading-bit position, to a packed storage word. The magnitude uses the coordinates of
`FiniteProductRound.round`.
-/
@[inline] def roundScaledWord? (sign : Bool) (scale : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt128) (leading : UInt64) : Option UInt64 :=
  let position := leading + scale
  if position < 1126 then
    none
  else
    let rounded :=
      product.roundShiftRightEven (leading - 52).toNat
    let carry := rounded == 0x0020000000000000
    let normalizedPosition := if carry then position + 1 else position
    if 3171 < normalizedPosition then
      none
    else
      let normalizedMantissa :=
        if carry then (0x0010000000000000 : UInt64) else rounded
      let exponent := normalizedPosition.toNat - 1125
      let fraction := normalizedMantissa.toNat - 0x0010000000000000
      some <| packFieldsWord sign (UInt64.ofNat exponent) (UInt64.ofNat fraction)

/-- `roundScaledWord?` as a model value. -/
@[inline] def roundScaled? (sign : Bool) (scale : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt128) (leading : UInt64) : Option Value :=
  (roundScaledWord? sign scale product leading).map ofUInt64

/--
Round a normalized two-limb product of significands with biased exponents `xExponent` and
`yExponent`, given its leading-bit position, to a packed storage word.
-/
@[inline] def roundNormalProductWord? (sign : Bool) (xExponent yExponent : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt128) (leading : UInt64) : Option UInt64 :=
  roundScaledWord? sign ((xExponent - 1) + (yExponent - 1)) product leading

/-- `roundNormalProductWord?` as a model value. -/
@[inline] def roundNormalProduct? (sign : Bool) (xExponent yExponent : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt128) (leading : UInt64) : Option Value :=
  (roundNormalProductWord? sign xExponent yExponent product leading).map ofUInt64

/--
Multiply decoded normal binary64 significands exactly in native limbs, then round the product.

It declines when the leading exponent is below the normal range before rounding, or when rounding
would overflow, and the caller then uses the generic exact rounder.
-/
@[inline] def roundNormalLimb? (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa : UInt64) : Option Value :=
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let leading : UInt64 :=
    if product.hi < ((1 : UInt64) <<< 41) then 104 else 105
  roundNormalProduct? sign xExponent yExponent product leading

/-- Decode two binary64 values and try the fixed-limb normal product pipeline. -/
@[inline] def mulNormalLimb? (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff then
    none
  else
    roundNormalLimb?
      (Bool.xor (signBit xBits) (signBit yBits))
      xExponent yExponent
      (fracField xBits ||| 0x0010000000000000)
      (fracField yBits ||| 0x0010000000000000)

/-- Decode binary64 fields with native storage into compact finite components. -/
@[inline] def decode? (x : Value) : Option FiniteKernel.Components :=
  let bits := toUInt64 x
  let exponent := expField bits
  if exponent == 0x7ff then
    none
  else
    let fraction := fracField bits
    some {
      sign := signBit bits
      exponent := exponent.toNat
      mantissa := (finiteMantissa exponent fraction).toNat }

/--
Native-storage finite addition through the compiled unsigned-scale component kernel.

Its body calls `FiniteKernel.Internal.addComponents`, the compiled twin of the exact-dyadic
`addComponents`. Their equality is proved in `Kernel.Proof`, which a runtime module cannot import,
so calling the compiled kernel by name keeps the exact-dyadic body out of the binary64 hot path.
-/
@[inline] def addFiniteComponents? (x y : Value) : Option Value :=
  match decode? x, decode? y with
  | some dx, some dy =>
      some <| FiniteKernel.Internal.addComponents FloatFormat.binary64 dx dy
  | _, _ => none

/-- Finite binary64 multiplication with flat native field decoding. -/
@[inline] def mulFinite? (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0x7ff || yExponent == 0x7ff then
    none
  else
    let xFraction := fracField xBits
    let yFraction := fracField yBits
    some <| FiniteProductRound.round FloatFormat.binary64
      (Bool.xor (signBit xBits) (signBit yBits))
      ((finiteMantissa xExponent xFraction).toNat *
        (finiteMantissa yExponent yFraction).toNat)
      ((FloatLib.Numerics.FixedWord.finiteScale xExponent).toNat +
        (FloatLib.Numerics.FixedWord.finiteScale yExponent).toNat)

/-- Native-storage finite division using the shared exact component kernel. -/
@[inline] def divFiniteComponents? (x y : Value) : Option Value :=
  match decode? x, decode? y with
  | some dx, some dy =>
      some <| FiniteKernel.divComponents FloatFormat.binary64 dx dy
  | _, _ => none

/--
Native-storage finite fused multiply-add through the compiled unsigned-scale component kernel.

As in `addFiniteComponents?`, the body calls `FiniteKernel.Internal.fmaComponents` to keep the
exact-dyadic `fmaComponents` body off the compiled binary64 path.
-/
@[inline] def fmaFiniteComponents? (x y z : Value) : Option Value :=
  match decode? x, decode? y, decode? z with
  | some dx, some dy, some dz =>
      some <| FiniteKernel.Internal.fmaComponents FloatFormat.binary64 dx dy dz
  | _, _, _ => none

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
