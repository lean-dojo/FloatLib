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
arbitrary-precision kernel `FiniteScaleAdd.roundSum`: both operands are decoded from the storage
word into a sign, a nonnegative scale, and an integer significand; the significands are aligned
by a left shift; the signed magnitudes are combined; and the result is rounded to nearest even
and packed. Significand arithmetic uses `UInt64`; format coordinates and shift counts also use
`Nat`. Refinement proofs live in `Add.Proof`.

The kernel returns `none` for exceptional or zero operands, alignment shifts exceeding the word
budget, a magnitude below the normal threshold before rounding, or overflow after rounding. The
dispatcher then uses the exact generic implementation. Exact cancellation is accepted and returns
positive zero.

The refinement proofs transfer natural-number values through `UInt64.toNat` and compare both
implementations with exact magnitude alignment. The generic kernel's sticky-bit alignment and
the native equal-scale exit are separately proved equal to that common specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordAdd

open NativeSmallWord

/--
Capacity contract of the one-word addition kernel.

The IEEE condition selects the exact binary semantics. The width bounds keep every storage word,
scale, and aligned significand in `UInt64`: a significand has at most `fracWidth + 1 ≤ 62` bits,
so the same-sign sum of two aligned significands fits after any alignment shift accepted by
`shiftLimit`. These bounds include binary64; formats with more than 30 exponent bits are excluded.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    fmt.expWidth ≤ 30 ∧
    fmt.fracWidth ≤ 61

/--
Addition eligibility is decided from the descriptor fields; the conditional form is inlined and
can be simplified for a closed format (see `NativeSmallWord.StorageEligible`).
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
below `2 ^ 64` and no machine-word addition can wrap. Larger shifts decline to the exact kernel.
-/
@[inline] def shiftLimit (fmt : FloatFormat) : UInt64 :=
  62 - UInt64.ofNat fmt.fracWidth

/--
Round a nonzero magnitude at an unsigned scale to a normal result, or decline.

The exact magnitude is `magnitude * 2 ^ (scale - offset)`, where
`offset = fmt.exponentBias + fmt.fracWidth - 1` and subtraction is in `Int`; `sign` supplies its
sign. This is the coordinate of `FiniteScaleAdd.roundMagnitude`. The function reproduces the normal
branch of
`FiniteProductRound.round` in machine words: it finds the leading bit, rounds the significand to
`fracWidth + 1` bits with ties to even, and hands carry, overflow, and packing to the shared
`NativeWordProduct.finish?`. Magnitudes below the normal threshold before rounding and values
that overflow after rounding return `none`.
-/
@[inline] def roundMagnitude? (fmt : FloatFormat) (sign : Bool)
    (magnitude scale : UInt64) : Option (Model fmt) :=
  let leading := FloatLib.Numerics.FixedWord.log2Word magnitude
  let position := leading + scale + alignOffset fmt
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
sign of the difference. Same-sign callers must keep `left + right` below `2 ^ 64`; opposite-sign
subtraction cannot wrap.
-/
@[inline] def roundAligned? (fmt : FloatFormat) (leftSign rightSign : Bool)
    (left right scale : UInt64) : Option (Model fmt) :=
  if leftSign == rightSign then
    roundMagnitude? fmt leftSign (left + right) scale
  else if left == right then
    some (zero fmt (leftSign && rightSign))
  else if left < right then
    roundMagnitude? fmt rightSign (right - left) scale
  else
    roundMagnitude? fmt leftSign (left - right) scale

/--
Add two decoded finite operands in machine words, or decline.

Each operand is a sign, its stored biased exponent, and its integer significand including the
implicit bit of a normal value. The scales are the compact finite scales of `FiniteKernel.scale`.
Equal scales combine directly; otherwise the operand with the larger scale is shifted left before
the signed magnitudes are combined. Zero operands and alignment shifts above `shiftLimit fmt`
return `none`; the exact kernel handles them.
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
      roundAligned? fmt xSign ySign xMantissa yMantissa xScale
    else if xScale ≤ yScale then
      let shift := yScale - xScale
      if shift ≤ shiftLimit fmt then
        roundAligned? fmt xSign ySign xMantissa (yMantissa <<< shift) xScale
      else
        none
    else
      let shift := xScale - yScale
      if shift ≤ shiftLimit fmt then
        roundAligned? fmt xSign ySign (xMantissa <<< shift) yMantissa yScale
      else
        none

/--
One-word finite addition, or subtraction when `negateRight` is set, directly on storage words.

Both operands are decoded with the shared one-word field extractors. An exceptional operand (an
all-ones exponent field) returns `none`. The right operand's sign is toggled by `negateRight`, so
subtraction never materializes a negated model value. Every accepted result is proved equal to
`FiniteKernel.add? x y`, respectively `FiniteKernel.add? x (neg y)`, in `Add.Proof`.
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

end Model.NativeSmallWordAdd
end FloatLib.Floats.Formats.BinaryInterchange
