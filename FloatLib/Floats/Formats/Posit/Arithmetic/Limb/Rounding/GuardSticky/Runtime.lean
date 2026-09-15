/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Shared.GuardSticky.Runtime
public import FloatLib.Kernels.FixedWord.DyadicCompare.Runtime

/-!
# Direct guard-and-sticky two-limb Posit rounding

The shared field-oriented posit rounder is instantiated with the `UInt128` carrier.
`candidateCarrier` maps every shared operation to a two-limb primitive, and the generic kernel
in `GuardStickyCarrier` keeps significands and codes in `UInt128`. Exponents and bit counts use
`Int` and `Nat`. Only the steps with carrier-specific contracts live here: the exact
minimum-positive comparison, the zero test, and exact-width sign restoration.

The kernel is selected by intermediate capacity, not by a particular named Posit format. Every
format whose storage fits two words may use it whenever the exact significand is below `2^128`.
Wider exact intermediates retain the same field semantics through the arbitrary-width rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding.GuardSticky

open FloatLib.Numerics

/-- Shift left in the two-word bitstream, returning zero at and beyond 128 positions. -/
@[inline] def shiftLeft (value : FixedWord.UInt128) (shift : Nat) : FixedWord.UInt128 :=
  if shift < 128 then
    FixedWord.UInt128.shiftLeft value shift
  else
    ⟨0, 0⟩

-- Named predicates keep their constants out of runtime carrier closures.
/-- Whether the discarded low-bit suffix is nonzero. -/
@[always_inline] def hasLowBits (value : FixedWord.UInt128) (width : Nat) : Bool :=
  !NativeLimb.isZero (NativeLimb.lowBits value width)

/-- Parity of the packed candidate used to break a midpoint tie. -/
@[always_inline] def isOdd (value : FixedWord.UInt128) : Bool :=
  (value.lo &&& 1) != 0

/--
Two-limb implementation of the shared candidate carrier.

The transparent record lets inlined helpers use the two-limb primitives directly. Addition drops
the carry out of the second limb and the successor wraps; the shared rounder applies both only
to values it has bounded.
-/
abbrev candidateCarrier : GuardStickyCarrier.CandidateCarrier FixedWord.UInt128 where
  bitAt := NativeLimb.bitAt
  hasLowBits := hasLowBits
  ofWord := fun word => ⟨0, word⟩
  shiftLeft := shiftLeft
  shiftRight := FixedWord.UInt128.shiftRight
  fractionBelow := NativeLimb.lowBits
  add := fun left right => (FixedWord.add128 left right).value
  lowOnes := fun width =>
    NativeLimb.lowBits ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ width
  increment := FixedWord.UInt128.increment
  isOdd := isOdd
  log2 := FixedWord.UInt128.log2

/-- Test a positive two-limb target against the format's exact minimum-positive value. -/
@[inline] def isLessMinPositive
    (format : Format) (significand : FixedWord.UInt128) (exponent : Int) : Bool :=
  let minExponent := -(4 * Int.ofNat (format.payloadBits - 1))
  FixedWord.DyadicCompare.compareNonnegative128ToWord
      significand exponent 1 minExponent == .lt

/--
Round the nonnegative value `significand * 2 ^ exponent` to its complete unsigned code in two
limbs.

Zero maps to code zero and targets below `minPos` to code one; every other target uses the shared
normalized rounder at the `UInt128` carrier.
-/
@[inline] def roundPositiveCodeWord
    (format : Format) (significand : FixedWord.UInt128) (exponent : Int) :
    FixedWord.UInt128 :=
  if NativeLimb.isZero significand then
    ⟨0, 0⟩
  else if isLessMinPositive format significand exponent then
    ⟨0, 1⟩
  else
    GuardStickyCarrier.roundNormalizedPositive candidateCarrier format significand exponent

/-- Restore a posit sign by exact-width two's complement inside the two-limb carrier. -/
@[inline] def restoreSignWord
    (format : Format) (negative : Bool) (positiveCode : FixedWord.UInt128) :
    FixedWord.UInt128 :=
  if negative then
    if NativeLimb.isZero positiveCode then
      ⟨0, 0⟩
    else
      NativeLimb.lowBits
        (NativeLimb.complement positiveCode).increment format.bits
  else
    positiveCode

/-- Round signed dyadic fields while keeping the significand and result code in two limbs. -/
@[inline] def roundCodeWord
    (format : Format) (negative : Bool)
    (significand : FixedWord.UInt128) (exponent : Int) : FixedWord.UInt128 :=
  restoreSignWord format negative
    (roundPositiveCodeWord format significand exponent)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding.GuardSticky
