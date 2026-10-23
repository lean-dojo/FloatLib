/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.ProductRound.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Runtime
public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Native one-word finite addition

The native addition path serves conventional IEEE formats whose storage word, exponent range,
and aligned significand sum fit in `UInt64` (`Eligible`). It is the word-tier counterpart of the
arbitrary-precision kernel `FiniteScaleAdd.roundSum`. Both operands are decoded from the storage
word into a sign, a nonnegative scale and an integer significand. Significands are aligned by a
left shift, or with a sticky bit when the gap is too wide for one word, then the signed
magnitudes are combined and the result is rounded to nearest even and packed. Significand
arithmetic uses `UInt64`, while format coordinates and shift counts also use `Nat`.
Refinement proofs are in `Add.Proof`.

It returns `none` for exceptional or zero operands, wide alignment shifts that the sticky path
declines, a magnitude below the normal threshold before rounding, or overflow after rounding.
The dispatcher then uses the exact generic implementation. Exact cancellation is accepted and
returns positive zero.

The refinement proofs transfer natural-number values through `UInt64.toNat` and compare both
implementations with exact magnitude alignment. The generic kernel's sticky-bit alignment, the
native equal-scale branch and the native sticky path are each proved equal to that common
specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordAdd

open NativeSmallWord

/--
Capacity contract of the one-word addition kernel.

Besides the IEEE condition, the width bounds keep every storage word, scale, and aligned
significand in `UInt64`: a significand has at most `fracWidth + 1 ≤ 62` bits, so the same-sign
sum of two aligned significands fits after any alignment shift accepted by `shiftLimit`. These
bounds include binary64 and exclude formats with more than 30 exponent bits.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    fmt.expWidth ≤ 30 ∧
    fmt.fracWidth ≤ 61

/--
Addition eligibility is decided from the descriptor fields. As for
`NativeSmallWord.StorageEligible`, the conditional form is inlined and simplifies for a closed
format.
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 ∧ fmt.expWidth ≤ 30 ∧ fmt.fracWidth ≤ 61 then
    isTrue h
  else
    isFalse h

/--
Nonnegative scale offset separating the compact finite scale from the product rounder's
coordinate: `fmt.exponentBias + fmt.fracWidth - 1`, the value of
`FiniteKernel.finiteScaleOffset fmt` as one machine word.

For every format that fits one machine word this constant is exact because the bias is below
`2 ^ expWidth`.
-/
@[inline] def alignOffset (fmt : FloatFormat) : UInt64 :=
  UInt64.ofNat (fmt.exponentBias + fmt.fracWidth - 1)

/--
Largest exponent-alignment shift the one-word kernel accepts.

A significand has at most `fracWidth + 1` bits. Shifting the larger-scale operand left by at most
`62 - fracWidth` bits keeps it below `2 ^ 63`, so the same-sign sum of both significands is still
below `2 ^ 64` and no machine-word addition can wrap. Larger shifts take the sticky-bit path
`roundJammed?`.
-/
@[inline] def shiftLimit (fmt : FloatFormat) : UInt64 :=
  62 - UInt64.ofNat fmt.fracWidth

/--
Round a nonzero magnitude at an unsigned scale to a normal result, or decline.

Its specification is `FiniteScaleAdd.roundMagnitude fmt offset sign magnitude scale`, the product
rounder at scale `scale + offset`. Addition passes `alignOffset fmt`, so its scales are the compact
finite scales, and fused multiply-add passes `0` and works in product coordinates.
It reproduces the normal branch of `FiniteProductRound.round` in machine words: it finds the
leading bit, rounds the significand to `fracWidth + 1` bits with ties to even, and hands carry,
overflow and packing to the shared `NativeWordProduct.finish?`. Magnitudes below the normal
threshold before rounding and values that overflow after rounding return `none`.
-/
@[inline] def roundMagnitude? (fmt : FloatFormat) (offset : UInt64) (sign : Bool)
    (magnitude scale : UInt64) : Option (Model fmt) :=
  let leading := FloatLib.Numerics.FixedWord.log2Word magnitude
  let position := leading + scale + offset
  let normalThreshold := biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1
  if position < normalThreshold then
    none
  else
    let fracWidth := UInt64.ofNat fmt.fracWidth
    let rounded :=
      -- A significand that already fits needs no right-rounding step.
      if fracWidth < leading then
        FloatLib.Numerics.FixedWord.roundShiftRightEven magnitude
          (leading - fracWidth).toNat
      else
        magnitude <<< (fracWidth - leading)
    NativeWordProduct.finish? fmt sign position rounded

/--
Combine two nonzero signed magnitudes already aligned at one unsigned scale and round once.

The four branches are those of `FiniteScaleAdd.roundMagnitudes`: same signs add the magnitudes,
equal opposite magnitudes cancel to positive zero, and otherwise the larger magnitude determines the
sign of the difference. Same-sign callers must keep `left + right` below `2 ^ 64`, and
opposite-sign subtraction cannot wrap.
-/
@[inline] def roundAligned? (fmt : FloatFormat) (offset : UInt64) (leftSign rightSign : Bool)
    (left right scale : UInt64) : Option (Model fmt) :=
  if leftSign == rightSign then
    roundMagnitude? fmt offset leftSign (left + right) scale
  else if left == right then
    some (zero fmt (leftSign && rightSign))
  else if left < right then
    roundMagnitude? fmt offset rightSign (right - left) scale
  else
    roundMagnitude? fmt offset leftSign (left - right) scale

/--
The sticky magnitude for a normal larger-scale significand `high` and a smaller-scale `low` that
lie `gap ≥ 3` scale positions apart. `high` is shifted left by three guard positions and `low` right
by `gap - 3`. When that discards a nonzero bit, the borrow is taken and the lowest bit is set, so
the magnitude has the exact sum's rounding (`Add.Proof.roundJammed_refines`).
-/
@[inline] def jammedMagnitude (sameSign : Bool) (high low gap : UInt64) : UInt64 :=
  let discard := gap - 3
  let lower := if discard < 64 then low >>> discard else 0
  let exact := discard < 64 && lower <<< discard == low
  FloatLib.Numerics.FixedWord.jamCombine sameSign exact (high <<< 3) lower

/--
Round the signed sum of a significand `high` with at least `fracWidth + 1` bits and a smaller-scale
`low` that lie `gap` scale positions apart, through `jammedMagnitude` at scale `scale + (gap - 3)`.
Callers keep `low` at most `2 ^ (fracWidth + gap - 1)`, so `high` fixes the sign and the leading
bit of the sum. A `high` below the hidden bit or at least `2 ^ 60`, and gaps below three, decline.
-/
@[inline] def roundJammed? (fmt : FloatFormat) (offset : UInt64) (highSign lowSign : Bool)
    (high low gap scale : UInt64) : Option (Model fmt) :=
  if hiddenBit fmt ≤ high && high < 0x1000000000000000 && 3 ≤ gap then
    roundMagnitude? fmt offset highSign (jammedMagnitude (highSign == lowSign) high low gap)
      (scale + (gap - 3))
  else
    none

/--
Add two decoded finite operands in machine words, or decline.

Each operand is a sign, its stored biased exponent, and its integer significand including the
implicit bit of a normal value, and scales are the compact finite scales of `FiniteKernel.scale`.
Equal scales combine as they are. Otherwise the operand with the larger scale is shifted left
before the signed magnitudes are combined, and alignment shifts above `shiftLimit fmt` go through
`roundJammed?`. Zero operands return `none` and are left to the exact kernel.
-/
@[inline] def addFields? (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : UInt64)
    (ySign : Bool) (yExponent yMantissa : UInt64) : Option (Model fmt) :=
  if xMantissa == 0 || yMantissa == 0 then
    none
  else
    let xScale := FloatLib.Numerics.FixedWord.finiteScale xExponent
    let yScale := FloatLib.Numerics.FixedWord.finiteScale yExponent
    if xScale == yScale then
      roundAligned? fmt (alignOffset fmt) xSign ySign xMantissa yMantissa xScale
    else if xScale ≤ yScale then
      let shift := yScale - xScale
      if shift ≤ shiftLimit fmt then
        roundAligned? fmt (alignOffset fmt) xSign ySign xMantissa (yMantissa <<< shift) xScale
      else
        roundJammed? fmt (alignOffset fmt) ySign xSign yMantissa xMantissa shift xScale
    else
      let shift := xScale - yScale
      if shift ≤ shiftLimit fmt then
        roundAligned? fmt (alignOffset fmt) xSign ySign (xMantissa <<< shift) yMantissa yScale
      else
        roundJammed? fmt (alignOffset fmt) xSign ySign xMantissa yMantissa shift yScale

/--
One-word finite addition, or subtraction when `negateRight` is set.

Both operands are decoded from their storage words with the shared one-word field extractors, and
an exceptional operand (an all-ones exponent field) returns `none`. Toggling the right operand's
sign with `negateRight` means subtraction never materializes a negated model value. `Add.Proof`
proves every accepted result equal to `FiniteKernel.add? x y`, or `FiniteKernel.add? x (neg y)`
for subtraction.
-/
@[inline] def addFinite? {fmt : FloatFormat} (x y : Model fmt) (negateRight : Bool) :
    Option (Model fmt) :=
  let xBits := toWord x
  let yBits := toWord y
  let xExponent := exponentField fmt xBits
  let yExponent := exponentField fmt yBits
  let allOnes := exponentMask fmt
  if xExponent == allOnes || yExponent == allOnes then
    none
  else
    addFields? fmt
      (signField fmt xBits) xExponent
      (NativeSmallWordFinite.finiteMantissa fmt xExponent (fractionField fmt xBits))
      (Bool.xor (signField fmt yBits) negateRight) yExponent
      (NativeSmallWordFinite.finiteMantissa fmt yExponent (fractionField fmt yBits))

/-! ## Storage-word entry points

The functions below are `addFinite?` and its helpers with machine words at both ends. A carrier
that stores the encoding as a `UInt64` calls `addFiniteWord?`, so an accepted sum never becomes
an exact-width model value. For binary64 that model value is a natural number of up to 64 bits,
which the runtime allocates once the sign bit is set. `Add.Proof` shows that `addFinite?` is the
`ofWord` image of `addFiniteWord?`.
-/

/-- The storage word of `zero fmt sign`. -/
@[inline] def zeroWord (fmt : FloatFormat) (sign : Bool) : UInt64 :=
  if sign && fmt.supportsSignedZero then packFields fmt true 0 0 else 0

/-- `roundMagnitude?` returning the packed storage word. -/
@[inline] def roundMagnitudeWord? (fmt : FloatFormat) (offset : UInt64) (sign : Bool)
    (magnitude scale : UInt64) : Option UInt64 :=
  let leading := FloatLib.Numerics.FixedWord.log2Word magnitude
  let position := leading + scale + offset
  let normalThreshold := biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1
  if position < normalThreshold then
    none
  else
    let fracWidth := UInt64.ofNat fmt.fracWidth
    let rounded :=
      if fracWidth < leading then
        FloatLib.Numerics.FixedWord.roundShiftRightEven magnitude
          (leading - fracWidth).toNat
      else
        magnitude <<< (fracWidth - leading)
    NativeWordProduct.finishWord? fmt sign position rounded

/-- `roundAligned?` returning the packed storage word. -/
@[inline] def roundAlignedWord? (fmt : FloatFormat) (offset : UInt64) (leftSign rightSign : Bool)
    (left right scale : UInt64) : Option UInt64 :=
  if leftSign == rightSign then
    roundMagnitudeWord? fmt offset leftSign (left + right) scale
  else if left == right then
    some (zeroWord fmt (leftSign && rightSign))
  else if left < right then
    roundMagnitudeWord? fmt offset rightSign (right - left) scale
  else
    roundMagnitudeWord? fmt offset leftSign (left - right) scale

/-- `roundJammed?` returning the packed storage word. -/
@[inline] def roundJammedWord? (fmt : FloatFormat) (offset : UInt64) (highSign lowSign : Bool)
    (high low gap scale : UInt64) : Option UInt64 :=
  if hiddenBit fmt ≤ high && high < 0x1000000000000000 && 3 ≤ gap then
    roundMagnitudeWord? fmt offset highSign (jammedMagnitude (highSign == lowSign) high low gap)
      (scale + (gap - 3))
  else
    none

/-- `addFields?` returning the packed storage word. -/
@[inline] def addFieldsWord? (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : UInt64)
    (ySign : Bool) (yExponent yMantissa : UInt64) : Option UInt64 :=
  if xMantissa == 0 || yMantissa == 0 then
    none
  else
    let xScale := FloatLib.Numerics.FixedWord.finiteScale xExponent
    let yScale := FloatLib.Numerics.FixedWord.finiteScale yExponent
    if xScale == yScale then
      roundAlignedWord? fmt (alignOffset fmt) xSign ySign xMantissa yMantissa xScale
    else if xScale ≤ yScale then
      let shift := yScale - xScale
      if shift ≤ shiftLimit fmt then
        roundAlignedWord? fmt (alignOffset fmt) xSign ySign xMantissa (yMantissa <<< shift) xScale
      else
        roundJammedWord? fmt (alignOffset fmt) ySign xSign yMantissa xMantissa shift xScale
    else
      let shift := xScale - yScale
      if shift ≤ shiftLimit fmt then
        roundAlignedWord? fmt (alignOffset fmt) xSign ySign (xMantissa <<< shift) yMantissa yScale
      else
        roundJammedWord? fmt (alignOffset fmt) xSign ySign xMantissa yMantissa shift yScale

/-- `addFinite?` on storage words, returning the packed storage word of an accepted sum. -/
@[inline] def addFiniteWord? (fmt : FloatFormat) (xBits yBits : UInt64)
    (negateRight : Bool) : Option UInt64 :=
  let xExponent := exponentField fmt xBits
  let yExponent := exponentField fmt yBits
  let allOnes := exponentMask fmt
  if xExponent == allOnes || yExponent == allOnes then
    none
  else
    addFieldsWord? fmt
      (signField fmt xBits) xExponent
      (NativeSmallWordFinite.finiteMantissa fmt xExponent (fractionField fmt xBits))
      (Bool.xor (signField fmt yBits) negateRight) yExponent
      (NativeSmallWordFinite.finiteMantissa fmt yExponent (fractionField fmt yBits))

end Model.NativeSmallWordAdd
end FloatLib.Floats.Formats.BinaryInterchange
