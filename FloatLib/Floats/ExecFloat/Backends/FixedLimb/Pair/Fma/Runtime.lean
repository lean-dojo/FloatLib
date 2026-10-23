/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime

/-!
# Two-word fused multiply-add runtime

The two-word counterpart of `NativeSmallWordFma`. The exact product of the two significands is a
four-word value in the product rounder's coordinate; the addend significand joins it either by an
exact left shift or, when the scales are far apart, through three guard positions and a sticky bit
below the operand at the larger scale. The combined four-word magnitude is reduced to two words
with a sticky bit (`normalizeJam128`) and rounded once by the two-word rounder of
`Addition.Runtime` at scale offset `0`. Correctness proofs live in `Fma.Proof`.

The kernel serves eligible layouts with at most 120 fraction bits and 32 exponent bits, which
keep every intermediate in four words and every scale in one. It returns `none` for exceptional
operands, a zero product, a sticky alignment whose higher operand is subnormal, results below the
normal threshold, and overflow. `fmaFinite?` then falls back to the exact generic kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

/--
Round a nonzero four-word magnitude at product scale `scale` to normal storage words, or decline.

First the magnitude is reduced to its leading 128-bit window with a sticky bit. At least
`fracWidth + 2` bits remain above the jammed positions, so nearest-even rounding is unchanged.
-/
@[inline] def roundProductWords? (fmt : FloatFormat) (sign : Bool) (magnitude : UInt256)
    (scale : UInt64) : Option UInt128 :=
  roundMagnitudeWords? fmt 0 sign magnitude.normalizeJam128
    (scale + UInt64.ofNat magnitude.normalizationShift128)

/--
Combine two nonzero signed four-word magnitudes aligned at one scale and round once.

Its branches are those of `FiniteScaleAdd.roundMagnitudes`, and exact cancellation is positive
zero. Same-sign callers keep `left + right` below `2 ^ 256`.
-/
@[inline] def roundAlignedProductWords? (fmt : FloatFormat) (leftSign rightSign : Bool)
    (left right : UInt256) (scale : UInt64) : Option UInt128 :=
  if leftSign == rightSign then
    roundProductWords? fmt leftSign (add256 left right).value scale
  else if left == right then
    some ⟨0, 0⟩
  else if left.less right then
    roundProductWords? fmt rightSign (right.sub left) scale
  else
    roundProductWords? fmt leftSign (left.sub right) scale

/--
The sticky magnitude of a product `high` above an addend `low` that lie `gap ≥ 3` scale positions
apart: `high` doubled three times, combined with `low` shifted right by `gap - 3`, with the lowest
bit set when that shift discards a nonzero bit.
-/
@[inline] def jammedProductWords (sameSign : Bool) (high : UInt256) (low : UInt128)
    (gap : UInt64) : UInt256 :=
  let discard := (gap - 3).toNat
  let lower := low.shiftRight discard
  let exact := lower.shiftLeft discard == low
  let upper := high.double.double.double
  if sameSign then
    let sum := (add256 upper (UInt256.ofUInt128 lower)).value
    if exact then sum else sum.setLowBit
  else
    let difference := upper.sub (UInt256.ofUInt128 lower)
    if exact then difference else (difference.sub ⟨0, 0, 0, 1⟩).setLowBit

/--
The sticky magnitude of an addend `high` above a product `low` that lie `gap ≥ 3` scale positions
apart: `high` shifted left by three guard positions, combined with `low` shifted right by
`gap - 3`, with the lowest bit set when that shift discards a nonzero bit.
-/
@[inline] def jammedAddendWords (sameSign : Bool) (high : UInt128) (low : UInt256)
    (gap : UInt64) : UInt128 :=
  let discard := (gap - 3).toNat
  let lower := low.shiftRight128 discard
  let exact := !low.hasNonzeroBelow discard
  UInt128.jamCombine sameSign exact (high.shiftLeft 3) lower

/-- Whether a four-word product is at least `2 ^ fracWidth`, the smallest normal significand. -/
@[inline] def productAtLeastImplicit (fmt : FloatFormat) (product : UInt256) : Bool :=
  product.limb3 != 0 || product.limb2 != 0 || implicitBit fmt ≤ product.limb1

/--
Round `product * 2 ^ productScale + addend * 2 ^ addendScale` once, in product coordinates.

A zero addend rounds the product alone. An addend at a scale at most `fracWidth + 2` above the
product is shifted onto the product exactly, and a larger gap leaves the product as a sticky tail
of the addend. A product at a scale above the addend is aligned exactly for gaps below three and
otherwise keeps the addend as its sticky tail. A zero product and a sticky alignment whose higher
operand is below `2 ^ fracWidth` return `none`.
-/
@[inline] def fmaFieldsWords? (fmt : FloatFormat)
    (productSign : Bool) (product : UInt256) (productScale : UInt64)
    (addendSign : Bool) (addend : UInt128) (addendScale : UInt64) : Option UInt128 :=
  if product == ⟨0, 0, 0, 0⟩ then
    none
  else if addend == ⟨0, 0⟩ then
    roundProductWords? fmt productSign product productScale
  else if productScale ≤ addendScale then
    let shift := addendScale - productScale
    if shift ≤ UInt64.ofNat (fmt.fracWidth + 2) then
      roundAlignedProductWords? fmt productSign addendSign product
        (addend.shiftLeft256 shift.toNat) productScale
    else if implicitBit fmt ≤ addend.hi then
      roundMagnitudeWords? fmt 0 addendSign
        (jammedAddendWords (addendSign == productSign) addend product shift)
        (productScale + (shift - 3))
    else
      none
  else
    let shift := productScale - addendScale
    if shift < 3 then
      let shifted := if shift == 0 then product else if shift == 1 then product.double
        else product.double.double
      roundAlignedProductWords? fmt productSign addendSign shifted (UInt256.ofUInt128 addend)
        addendScale
    else if productAtLeastImplicit fmt product then
      roundProductWords? fmt productSign
        (jammedProductWords (productSign == addendSign) product addend shift)
        (addendScale + (shift - 3))
    else
      none

/--
Two-word finite fused multiply-add on storage words, or decline.

The product scale is the sum of the operands' compact finite scales, and the addend's compact
scale is moved into product coordinates by `alignOffset fmt`. Layouts with more than 120 fraction
or 32 exponent bits decline. `Fma.Proof.fmaFiniteWords_refines` relates every accepted result to
`FiniteKernel.fma?`.
-/
@[inline] def fmaFiniteWords? (fmt : FloatFormat) (x y z : UInt128) : Option UInt128 :=
  if 120 < fmt.fracWidth || 32 < fmt.expWidth then
    none
  else
    let xExponent := expField fmt x.hi
    let yExponent := expField fmt y.hi
    let zExponent := expField fmt z.hi
    if xExponent == expAllOnes fmt || yExponent == expAllOnes fmt ||
        zExponent == expAllOnes fmt then
      none
    else
      fmaFieldsWords? fmt
        (Bool.xor (signBit fmt x.hi) (signBit fmt y.hi))
        (mul128 (finiteMantissaWords fmt xExponent x.hi x.lo)
          (finiteMantissaWords fmt yExponent y.hi y.lo))
        (finiteScale xExponent + finiteScale yExponent)
        (signBit fmt z.hi) (finiteMantissaWords fmt zExponent z.hi z.lo)
        (finiteScale zExponent + alignOffset fmt)

/--
Evaluate finite two-word fused multiply-add on model values.

The storage-word kernel runs first. Every remaining finite case uses the generic one-rounding
exact kernel, and exceptional inputs return `none` to the dispatcher.
-/
@[specialize fmt] def fmaFinite? {fmt : FloatFormat} (x y z : Model fmt) : Option (Model fmt) :=
  match fmaFiniteWords? fmt (toWords x) (toWords y) (toWords z) with
  | some words => some (ofWords fmt words)
  | none => FiniteKernel.fmaRuntimeFlat? x y z

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
