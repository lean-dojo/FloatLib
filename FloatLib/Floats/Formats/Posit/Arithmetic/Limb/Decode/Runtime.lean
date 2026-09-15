/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Core.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime
public import FloatLib.Kernels.FixedWord.Difference.Runtime
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime

/-!
# Direct two-limb posit candidate decoding

The two-limb posit decoder reads encodings stored in native words. Regime scans stay in
fixed-width words, and conversion to `Nat` is delayed until exact dyadic fields are constructed.
Refinement theorems live in `Decode.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimb

open FloatLib.Numerics

/-- Test whether both limbs of a two-word encoding are zero. -/
@[inline] def isZero (value : FloatLib.Numerics.FixedWord.UInt128) : Bool :=
  value.hi == 0 && value.lo == 0

/--
Read one bit from a two-word value using least-significant-bit numbering.

Each branch delegates to the native-word reader, keeping the executable path to a shift, mask,
and comparison instead of constructing a `BitVec` view.
-/
@[inline] def bitAt (value : FloatLib.Numerics.FixedWord.UInt128) (index : Nat) : Bool :=
  if index < 64 then
    NativeWord.bitAt value.lo index
  else
    NativeWord.bitAt value.hi (index - 64)

/--
Retain the low `width` bits of a two-limb value.

The value is zero-extended outside its 128-bit carrier, so requesting at least 128 bits returns
the complete value.
-/
@[inline] def lowBits
    (value : FloatLib.Numerics.FixedWord.UInt128) (width : Nat) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  if width < 64 then
    ⟨0, NativeWord.lowBits value.lo width⟩
  else if width ≤ 128 then
    ⟨NativeWord.lowBits value.hi (width - 64), value.lo⟩
  else
    value

/-- Bitwise complement of both native limbs. -/
@[inline] def complement
    (value : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  ⟨~~~value.hi, ~~~value.lo⟩

/--
Count leading zeroes in the low `width` bits of a two-limb value.

The executable path masks once and uses the native logarithm of the high or low nonzero limb.
-/
@[inline] def countLeadingZeros
    (value : FloatLib.Numerics.FixedWord.UInt128) (width : Nat) : Nat :=
  let truncated := lowBits value width
  if isZero truncated then
    width
  else
    width - (FloatLib.Numerics.FixedWord.UInt128.log2 truncated + 1)

/--
Count a leading run in the low `width` bits of a two-limb value.

Zero runs use one masked native logarithm at every width. One runs use the complemented carrier
through width 128; at wider widths the zero extension makes the leading bit zero immediately.
-/
@[inline] def countLeadingRun
    (value : FloatLib.Numerics.FixedWord.UInt128)
    (width : Nat) (bit : Bool) : Nat :=
  if bit then
    if width ≤ 128 then
      countLeadingZeros (complement value) width
    else
      0
  else
    countLeadingZeros value width

/--
Eliminate a nonnegative candidate into native significand and exact exponent fields.

The full significand remains in two machine limbs. Only the at-most-two-bit stored exponent is
converted to `Nat`, matching the standardized posit descriptor without constructing an
intermediate dyadic record.
-/
@[inline] def withNonnegativeFields {α : Type}
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (continuation :
      FloatLib.Numerics.FixedWord.UInt128 → Int → α) : α :=
  if isZero code then
    continuation ⟨0, 0⟩ 0
  else
    let regimeBit := bitAt code (format.payloadBits - 1)
    let regimeRunLength :=
      countLeadingRun code format.payloadBits regimeBit
    let hasRegimeTerminator : Bool :=
      regimeRunLength < format.payloadBits
    let trailingBits :=
      format.payloadBits - regimeRunLength -
        (if hasRegimeTerminator then 1 else 0)
    let usedExponentBits := min format.exponentBits trailingBits
    let fractionBits := trailingBits - usedExponentBits
    let fractionField := lowBits code fractionBits
    let significand :=
      (FloatLib.Numerics.FixedWord.add128 fractionField
        (FloatLib.Numerics.FixedWord.UInt128.singleBit fractionBits)).value
    let storedExponentWord :=
      lowBits
        (FloatLib.Numerics.FixedWord.UInt128.shiftRight code fractionBits)
        usedExponentBits
    let storedExponent := storedExponentWord.lo.toNat
    let exponentField :=
      storedExponent *
        2 ^ (format.exponentBits - usedExponentBits)
    let regimeValue : Int :=
      if regimeBit then
        Int.ofNat regimeRunLength - 1
      else
        -Int.ofNat regimeRunLength
    continuation significand
      (regimeValue * Int.ofNat format.regimeExponentStep +
        Int.ofNat exponentField - Int.ofNat fractionBits)

/--
Decode a nonnegative candidate into the shared exact-dyadic carrier.

This proof-facing view is defined through `withNonnegativeFields`; optimized arithmetic consumes
the same decoder through its native continuation interface.
-/
@[inline] def nonnegativeDyadicAt
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.Dyadic :=
  withNonnegativeFields format code fun significand exponent =>
    {
      negative := false
      significand := significand.toNat
      exponent
    }

/-! ## Direct decoding of complete stored words -/

/-- Test the stored sign bit without reconstructing the mathematical code. -/
@[inline] def isNegative
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128) : Bool :=
  bitAt code format.signIndex

/--
Unsigned magnitude of one complete two-limb posit encoding.

Negative posit codes use exact-width two's complement. Complementation and increment stay in the
two native limbs; `lowBits` removes the carrier bits above narrower formats. The result crosses to
`Nat` only once, when `nonnegativeDyadicAt` constructs the shared exact significand.
-/
@[inline] def magnitudeWord
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  if isNegative format code then
    lowBits (complement code).increment format.bits
  else
    code

/--
Decode a known finite, nonzero posit code through the two-limb field decoder.

The caller handles exceptional values. Sign extraction, magnitude extraction, and regime
inspection use the two native limbs; the result stores the significand in the shared dyadic carrier.
-/
@[inline] def decodeFinite
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.Dyadic :=
  let negative := isNegative format code
  let magnitude := magnitudeWord format code
  { nonnegativeDyadicAt format magnitude with negative }

/--
Eliminate a complete stored posit word into native dyadic fields.

NaR selects `onNaR`; zero and every finite value call the continuation. Sign extraction,
two's-complement magnitude recovery, regime decoding, and significand construction all remain
inside the two-limb carrier.
-/
@[inline] def withDyadicFields {α : Type}
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int → α) : α :=
  if code == signMaskWord format then
    onNaR
  else if isZero code then
    continuation false ⟨0, 0⟩ 0
  else
    let negative := isNegative format code
    let magnitude :=
      if negative then
        lowBits (complement code).increment format.bits
      else
        code
    withNonnegativeFields format magnitude fun significand exponent =>
      continuation negative significand exponent

/-- Eliminate two stored posit words through one shared native-field interface. -/
@[inline] def withTwoDyadicFields {α : Type}
    (format : Format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int → α) : α :=
  withDyadicFields format left onNaR
    fun leftNegative leftSignificand leftExponent =>
      withDyadicFields format right onNaR
        fun rightNegative rightSignificand rightExponent =>
          continuation leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent

/-- Eliminate three stored posit words through one shared native-field interface. -/
@[inline] def withThreeDyadicFields {α : Type}
    (format : Format)
    (left right addend : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int → α) : α :=
  withDyadicFields format left onNaR
    fun leftNegative leftSignificand leftExponent =>
      withDyadicFields format right onNaR
        fun rightNegative rightSignificand rightExponent =>
          withDyadicFields format addend onNaR
            fun addendNegative addendSignificand addendExponent =>
              continuation leftNegative leftSignificand leftExponent
                rightNegative rightSignificand rightExponent
                addendNegative addendSignificand addendExponent

/--
Total direct decoder for one stored two-limb posit word.

NaR becomes `none`, the unique zero becomes exact dyadic zero, and every ordinary word uses the
fixed-limb decoder.
-/
@[inline] def toDyadic?
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128) :
    Option FloatLib.Numerics.Dyadic :=
  if code == signMaskWord format then
    none
  else if isZero code then
    some FloatLib.Numerics.Dyadic.zero
  else
    some (decodeFinite format code)

end FloatLib.Floats.Formats.Posit.Model.NativeLimb
