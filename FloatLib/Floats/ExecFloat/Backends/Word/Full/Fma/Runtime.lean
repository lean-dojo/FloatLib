/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import FloatLib.Kernels.FixedWord.Difference.Runtime

/-!
# Native binary64 fused multiply-add runtime

The accepted paths align finite normal operands in two native limbs and round the sum or
difference once. An addend whose scale is at most 62 bits above the product's is aligned exactly,
and every other scale difference goes through a sticky bit. Declined cases use the generic exact
finite kernel. `Fma.Proof` has the proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/--
Shift a normal binary64 significand left by `shift` bits into the product's two-word coordinate,
where `shift` is the addend's scale above the product's.
-/
@[inline] def alignFmaAddend (mantissa : UInt64) (shift : Nat) : FloatLib.Numerics.FixedWord.UInt128 :=
  FloatLib.Numerics.FixedWord.UInt128.shiftLeft { hi := 0, lo := mantissa } shift

/-- Leading-bit position of a binary64 FMA magnitude, which needs at most 116 bits. -/
@[inline] def fmaLeading (magnitude : FloatLib.Numerics.FixedWord.UInt128) : UInt64 :=
  UInt64.ofNat (FloatLib.Numerics.FixedWord.UInt128.log2 magnitude)

/--
Try the normal binary64 FMA path when the product and addend have the same sign and the addend's
scale is at most 62 bits above the product's, on storage words.

The accepted magnitude `xMantissa * yMantissa + zMantissa * 2^shift` is exact and below
`2^116`, so the result is rounded once.
-/
@[inline] def fmaNormalSameSignWord? (xBits yBits zBits : UInt64) : Option UInt64 :=
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff ||
      zExponent == 0 || zExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let productScale := finiteScale xExponent + finiteScale yExponent
    let zProductScale := finiteScale zExponent + 1074
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    if productSign != zSign || zProductScale < productScale ||
        productScale + 62 < zProductScale then
      none
    else
      let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
      let sum := FloatLib.Numerics.FixedWord.add128 product
        (alignFmaAddend zMantissa (zProductScale - productScale).toNat)
      if sum.carry != 0 then
        none
      else
        roundNormalProductWord? productSign xExponent yExponent sum.value
          (fmaLeading sum.value)

/-- `fmaNormalSameSignWord?` as a model value. -/
@[inline] def fmaNormalSameSign? (x y z : Value) : Option Value :=
  (fmaNormalSameSignWord? (toUInt64 x) (toUInt64 y) (toUInt64 z)).map ofUInt64

/--
Try the normal binary64 FMA path when the product and addend have opposite signs and the addend's
scale is at most 62 bits above the product's, on storage words.

It declines exact cancellation and differences whose leading bit is below position 53. The
product rounder checks the result exponent, and declined cases use the generic finite kernel.
-/
@[inline] def fmaNormalOppositeSignWord? (xBits yBits zBits : UInt64) : Option UInt64 :=
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff ||
      zExponent == 0 || zExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let productScale := finiteScale xExponent + finiteScale yExponent
    let zProductScale := finiteScale zExponent + 1074
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    if productSign == zSign || zProductScale < productScale ||
        productScale + 62 < zProductScale then
      none
    else
      let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
      let aligned := alignFmaAddend zMantissa (zProductScale - productScale).toNat
      if product == aligned then
        none
      else
        let productLess := FloatLib.Numerics.FixedWord.UInt128.less product aligned
        let magnitude :=
          if productLess then
            FloatLib.Numerics.FixedWord.UInt128.sub aligned product
          else
            FloatLib.Numerics.FixedWord.UInt128.sub product aligned
        let leading := fmaLeading magnitude
        if leading < 53 then
          none
        else
          roundNormalProductWord? (if productLess then zSign else productSign)
            xExponent yExponent magnitude leading

/-- `fmaNormalOppositeSignWord?` as a model value. -/
@[inline] def fmaNormalOppositeSign? (x y z : Value) : Option Value :=
  (fmaNormalOppositeSignWord? (toUInt64 x) (toUInt64 y) (toUInt64 z)).map ofUInt64

/--
Normal binary64 FMA for addends outside the exact window, on storage words.

An addend whose scale is `gap` positions below the product's is shifted right with a sticky bit
into the product's coordinate. An addend more than 62 positions above keeps three guard positions,
and the product is shifted right with a sticky bit below them. Either way the sticky magnitude
rounds like the exact sum, because the dominant operand leaves more than `fracWidth + 2` bits above
the discarded positions.
-/
@[inline] def fmaJammedWord? (xBits yBits zBits : UInt64) : Option UInt64 :=
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff ||
      zExponent == 0 || zExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let productScale := finiteScale xExponent + finiteScale yExponent
    let zProductScale := finiteScale zExponent + 1074
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
    if zProductScale < productScale then
      let gap := productScale - zProductScale
      let lower := if gap < 64 then zMantissa >>> gap else 0
      let exact := gap < 64 && lower <<< gap == zMantissa
      let magnitude := UInt128.jamCombine (productSign == zSign) exact product ⟨0, lower⟩
      roundNormalProductWord? productSign xExponent yExponent magnitude (fmaLeading magnitude)
    else if productScale + 62 < zProductScale then
      let discard := zProductScale - productScale - 3
      let lower := FloatLib.Numerics.FixedWord.UInt128.shiftRight product discard.toNat
      let shifted := FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower discard.toNat
      let exact := discard < 128 && shifted.hi == product.hi && shifted.lo == product.lo
      let magnitude := UInt128.jamCombine (productSign == zSign) exact ⟨0, zMantissa <<< 3⟩ lower
      roundScaledWord? zSign (productScale + discard) magnitude (fmaLeading magnitude)
    else
      none

/-- `fmaJammedWord?` as a model value. -/
@[inline] def fmaJammed? (x y z : Value) : Option Value :=
  (fmaJammedWord? (toUInt64 x) (toUInt64 y) (toUInt64 z)).map ofUInt64

/--
Native normal binary64 FMA on storage words, trying the same-sign, opposite-sign and sticky paths
in turn. Carriers that store binary64 as a `UInt64` call this word form.
-/
@[inline] def fmaNormalWord? (xBits yBits zBits : UInt64) : Option UInt64 :=
  match fmaNormalSameSignWord? xBits yBits zBits with
  | some result => some result
  | none =>
      match fmaNormalOppositeSignWord? xBits yBits zBits with
      | some result => some result
      | none => fmaJammedWord? xBits yBits zBits

/-- `fmaNormalWord?` as a model value. -/
@[inline] def fmaNormal? (x y z : Value) : Option Value :=
  (fmaNormalWord? (toUInt64 x) (toUInt64 y) (toUInt64 z)).map ofUInt64

/-- Finite binary64 FMA through the native normal paths, falling back to `fmaFiniteComponents?`. -/
@[inline] def fmaFinite? (x y z : Value) : Option Value :=
  match fmaNormal? x y z with
  | some result => some result
  | none => fmaFiniteComponents? x y z

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
