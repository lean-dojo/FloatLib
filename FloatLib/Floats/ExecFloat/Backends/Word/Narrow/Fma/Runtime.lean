/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Finite.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Rounding.Runtime
public import FloatLib.Kernels.FixedWord.SignedMagnitude.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding

/-!
# Native-word fused multiply-add for generic binary32

The fast path combines a product of at most 48 bits with the addend in one `UInt64` when the
alignment allows it. A same-sign addend dominating the product by more than 48 scale bits is
returned unchanged, and other large gaps with a large enough dominant operand shift the smaller
one right with a sticky bit. Remaining gaps use exact dyadic alignment, which preserves
tie-breaking. NaN and infinity handling stays outside this module, and `Fma.Proof` has the proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

open FloatLib.Numerics.FixedWord (shiftRightWord jamCombine)

/-- Finite binary32 fused multiply-add through exact dyadic coordinates. -/
@[inline] def fmaFinite? (x y z : Value) : Option Value :=
  match toDyadic? (toUInt32 x), toDyadic? (toUInt32 y), toDyadic? (toUInt32 z) with
  | some dx, some dy, some dz =>
      let product : Numerics.Dyadic := {
        negative := Bool.xor dx.negative dy.negative,
        significand := dx.significand * dy.significand,
        exponent := dx.exponent + dy.exponent }
      some (ofUInt32 (roundDyadic (Model.addDyadic product dz)))
  | _, _, _ => none

/--
Exact finite binary32 FMA on components the native kernel has already decoded.

It handles any alignment gap without a second decode or significand product.
-/
@[inline] def fmaExactFinite?
    (productSign zSign : Bool)
    (product productScale zMantissa zProductScale : UInt64) : Option Value :=
  some <| ofUInt32 <| roundDyadic <|
    Model.addDyadic
      { negative := productSign
        significand := product.toNat
        exponent := Int.ofNat productScale.toNat - 298 }
      { negative := zSign
        significand := zMantissa.toNat
        exponent := Int.ofNat zProductScale.toNat - 298 }

/--
Whether `shift < 64` and `value >>> shift` discards no set bit. A native shift reduces its count
modulo 64, so a count of 64 or more is never an exact shift.
-/
@[inline] def isExactShift (value shift : UInt64) : Bool :=
  shift < 64 && (value >>> shift) <<< shift == value

/--
Machine-word implementation of finite binary32 fused multiply-add.

The exact product has at most 48 bits. When the aligned operands also fit in one `UInt64`, the
product and addend are combined without building dyadics. An addend dominating a same-sign product
by more than 48 scale bits is returned unchanged. Larger gaps keep three guard bits of a normal
addend, or the whole product when it is at least `2^46`, and shift the other operand right with a
sticky bit, which rounds like the exact sum. Remaining gaps use the exact path
`fmaExactFinite?`.
-/
@[inline] def fmaFiniteWord? (x y z : Value) : Option Value :=
  let xBits := toUInt32 x
  let yBits := toUInt32 y
  let zBits := toUInt32 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0xff || yExponent == 0xff || zExponent == 0xff then
    fmaFinite? x y z
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let xScale := finiteScale xExponent
    let yScale := finiteScale yExponent
    let zScale := finiteScale zExponent
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    let product := xMantissa * yMantissa
    let productScale := xScale + yScale
    let zProductScale := zScale + 149
    if product == 0 || zMantissa == 0 then
      fmaFinite? x y z
    else if productScale ≤ zProductScale then
      let shift := zProductScale - productScale
      if shift ≤ 39 then
        let sum := FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign product (zMantissa <<< shift)
        some (ofUInt32 (roundProduct sum.1 sum.2 productScale))
      else if 48 < shift && productSign == zSign then
        some z
      else if 0x800000 ≤ zMantissa then
        let discard := shift - 3
        let magnitude := jamCombine (productSign == zSign) (isExactShift product discard)
          (zMantissa <<< 3) (shiftRightWord product discard)
        some (ofUInt32 (roundProduct zSign magnitude (productScale + discard)))
      else
        fmaExactFinite?
          productSign zSign product productScale zMantissa zProductScale
    else
      let shift := productScale - zProductScale
      if shift ≤ 15 then
        let sum := FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign (product <<< shift) zMantissa
        some (ofUInt32 (roundProduct sum.1 sum.2 zProductScale))
      else if 0x400000000000 ≤ product then
        let magnitude := jamCombine (productSign == zSign) (isExactShift zMantissa shift)
          product (shiftRightWord zMantissa shift)
        some (ofUInt32 (roundProduct productSign magnitude productScale))
      else
        fmaExactFinite?
          productSign zSign product productScale zMantissa zProductScale

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
