/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime

/-!
# Two-word finite addition and subtraction

The two-word counterpart of `NativeSmallWordAdd`: both operands are decoded from their storage words
into a sign, a compact finite scale, and a two-word significand. Scales at most `shiftLimit` apart
are aligned exactly by a left shift, while larger gaps keep three guard positions and a sticky bit
below the higher operand. The signed magnitudes are combined and rounded once to nearest even, and
the normal result is packed into storage words. Every intermediate fits two words because an
eligible significand has at most 126 bits. Refinement proofs live in `Addition.Proof`.

The kernel returns `none` for exceptional or zero operands, a sticky alignment whose higher
operand is subnormal, a magnitude below the normal threshold before rounding, and overflow after
rounding. Exact cancellation returns positive zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

/--
Offset from a compact finite scale to the product rounder's coordinate:
`fmt.exponentBias + fmt.fracWidth - 1`, the value of `FiniteKernel.finiteScaleOffset fmt`.
-/
@[inline] def alignOffset (fmt : FloatFormat) : UInt64 :=
  UInt64.ofNat (fmt.exponentBias + fmt.fracWidth - 1)

/--
Largest alignment shift that is done exactly, by a left shift. A significand has at most
`fracWidth + 1` bits, so shifting it left by `126 - fracWidth` keeps it below `2 ^ 127` and the
same-sign sum of two significands below `2 ^ 128`.
-/
@[inline] def shiftLimit (fmt : FloatFormat) : UInt64 :=
  126 - UInt64.ofNat fmt.fracWidth

/--
Finish a rounded two-word significand already in the normal range: normalize a rounding carry,
decline overflow, and pack the storage words.
-/
@[inline] def finishWords? (fmt : FloatFormat) (sign : Bool) (position : UInt64)
    (rounded : UInt128) : Option UInt128 :=
  let carry := isCarry fmt rounded
  let normalizedPosition := if carry then position + 1 else position
  if UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) < normalizedPosition then
    none
  else
    some <| packNormalWords fmt sign
      (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2))
      (normalizeCarry fmt carry rounded)

/--
Round a nonzero two-word magnitude at an unsigned scale to the storage words of a normal result,
or decline.

An accepted result decodes to `FiniteScaleAdd.roundMagnitude fmt offset sign magnitude scale`.
Addition passes `alignOffset fmt`, so its scales are compact finite scales, and fused multiply-add
passes `0`. The magnitude is rounded to `fracWidth + 1` bits with ties to even, and carry, overflow,
and packing follow `FiniteProductRound.round`. Magnitudes below the normal threshold and results
that overflow return `none`.
-/
@[inline] def roundMagnitudeWords? (fmt : FloatFormat) (offset : UInt64) (sign : Bool)
    (magnitude : UInt128) (scale : UInt64) : Option UInt128 :=
  let leading := UInt64.ofNat magnitude.log2
  let position := leading + scale + offset
  if position < UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1) then
    none
  else
    let fracWidth := UInt64.ofNat fmt.fracWidth
    let rounded :=
      if fracWidth < leading then
        magnitude.roundShiftRightEven128 (leading - fracWidth).toNat
      else
        magnitude.shiftLeft (fracWidth - leading).toNat
    finishWords? fmt sign position rounded

/--
Combine two nonzero signed magnitudes aligned at one scale and round once.

Its branches are those of `FiniteScaleAdd.roundMagnitudes`. Same-sign callers keep
`left + right` below `2 ^ 128`. Exact cancellation of opposite signs is positive zero.
-/
@[inline] def roundAlignedWords? (fmt : FloatFormat) (offset : UInt64) (leftSign rightSign : Bool)
    (left right : UInt128) (scale : UInt64) : Option UInt128 :=
  if leftSign == rightSign then
    roundMagnitudeWords? fmt offset leftSign (add128 left right).value scale
  else if left == right then
    some ⟨0, 0⟩
  else if left.less right then
    roundMagnitudeWords? fmt offset rightSign (right.sub left) scale
  else
    roundMagnitudeWords? fmt offset leftSign (left.sub right) scale

/--
The sticky magnitude for a higher-scale significand `high` and a lower `low` that lie `gap ≥ 3`
scale positions apart: `high` shifted left by three guard positions, combined with `low` shifted
right by `gap - 3`, with the lowest bit set when that shift discards a nonzero bit.
-/
@[inline] def jammedMagnitudeWords (sameSign : Bool) (high low : UInt128) (gap : UInt64) :
    UInt128 :=
  let discard := (gap - 3).toNat
  let lower := low.shiftRight discard
  let exact := lower.shiftLeft discard == low
  UInt128.jamCombine sameSign exact (high.shiftLeft 3) lower

/--
Round the signed sum of a significand `high` with at least `fracWidth + 1` bits and a lower `low`
that lie `gap` scale positions apart, through `jammedMagnitudeWords` at scale `scale + (gap - 3)`.
Callers keep `low` at most `2 ^ (fracWidth + gap - 1)`. A `high` below the implicit bit or at
least `2 ^ 124`, and gaps below three, decline. The `2 ^ 124` bound keeps the same-sign sticky
sum below `2 ^ 128`.
-/
@[inline] def roundJammedWords? (fmt : FloatFormat) (offset : UInt64) (highSign lowSign : Bool)
    (high low : UInt128) (gap scale : UInt64) : Option UInt128 :=
  if implicitBit fmt ≤ high.hi && high.hi < 0x1000000000000000 && 3 ≤ gap then
    roundMagnitudeWords? fmt offset highSign
      (jammedMagnitudeWords (highSign == lowSign) high low gap) (scale + (gap - 3))
  else
    none

/--
Add two decoded finite operands in two-word arithmetic, or decline.

Each operand is a sign, its stored biased exponent, and its two-word significand including the
implicit bit of a normal value. Zero operands return `none`.
-/
@[inline] def addFieldsWords? (fmt : FloatFormat)
    (xSign : Bool) (xExponent : UInt64) (xMantissa : UInt128)
    (ySign : Bool) (yExponent : UInt64) (yMantissa : UInt128) : Option UInt128 :=
  if xMantissa == ⟨0, 0⟩ || yMantissa == ⟨0, 0⟩ then
    none
  else
    let xScale := finiteScale xExponent
    let yScale := finiteScale yExponent
    if xScale ≤ yScale then
      let shift := yScale - xScale
      if shift ≤ shiftLimit fmt then
        roundAlignedWords? fmt (alignOffset fmt) xSign ySign xMantissa
          (yMantissa.shiftLeft shift.toNat) xScale
      else
        roundJammedWords? fmt (alignOffset fmt) ySign xSign yMantissa xMantissa shift xScale
    else
      let shift := xScale - yScale
      if shift ≤ shiftLimit fmt then
        roundAlignedWords? fmt (alignOffset fmt) xSign ySign (xMantissa.shiftLeft shift.toNat)
          yMantissa yScale
      else
        roundJammedWords? fmt (alignOffset fmt) xSign ySign xMantissa yMantissa shift yScale

/-- The two-word significand of a finite value: its fraction, with the implicit bit when normal. -/
@[inline] def finiteMantissaWords (fmt : FloatFormat) (exponent high low : UInt64) : UInt128 :=
  if exponent == 0 then ⟨fracHigh fmt high, low⟩ else normalMantissa fmt (fracHigh fmt high) low

/--
Two-word finite addition, or subtraction when `negateRight` is set, on storage words.

An exceptional operand (an all-ones exponent field) returns `none`. The right operand's sign is
toggled by `negateRight`. `Addition.Proof.addFiniteWords_refines` relates every accepted result to
`FiniteKernel.add?`.
-/
@[inline] def addFiniteWords? (fmt : FloatFormat) (x y : UInt128) (negateRight : Bool) :
    Option UInt128 :=
  let xExponent := expField fmt x.hi
  let yExponent := expField fmt y.hi
  if xExponent == expAllOnes fmt || yExponent == expAllOnes fmt then
    none
  else
    addFieldsWords? fmt
      (signBit fmt x.hi) xExponent (finiteMantissaWords fmt xExponent x.hi x.lo)
      (Bool.xor (signBit fmt y.hi) negateRight) yExponent
      (finiteMantissaWords fmt yExponent y.hi y.lo)

/-! ## Model entry points -/

/--
Evaluate finite two-word addition on model values.

The storage-word kernel runs first. Every remaining finite case uses the width-generic exact
kernel, and exceptional inputs return `none` to the operation dispatcher. `@[specialize fmt]` lets
descriptor-dependent constants simplify at closed-format call sites without asking callers to
inline this candidate chain.
-/
@[specialize fmt] def addFinite? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  match addFiniteWords? fmt (toWords x) (toWords y) false with
  | some words => some (ofWords fmt words)
  | none => FiniteKernel.addRuntime? x y

/--
Evaluate finite two-word subtraction on model values.

The storage-word kernel toggles the right sign. Every remaining finite case uses generic exact
addition with a negated right operand, and exceptional inputs return `none` to the dispatcher.
-/
@[specialize fmt] def subFinite? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  match addFiniteWords? fmt (toWords x) (toWords y) true with
  | some words => some (ofWords fmt words)
  | none => FiniteKernel.addRuntime? x (neg y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
