/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Shared.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime
public import FloatLib.Kernels.FixedWord.DyadicCompare.Runtime

/-!
# Direct one-word guard-and-sticky Posit rounding

The shared field-oriented posit rounder is instantiated with the `UInt64` carrier.
`candidateCarrier` maps every shared operation to a native-word primitive, and the generic
kernel in `GuardStickyCarrier` keeps the candidate code in `UInt64` during packing and rounding.
Only steps with carrier-specific contracts live here: the exact minimum-positive comparison, the
zero test, and sign restoration.

The kernel is selected by intermediate capacity, not by a named Posit width. Operations that
continue in a two-limb intermediate import the separate `WordLimb` adapter at that boundary; this
scalar rounder does not depend on or re-export a second implementation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky

open FloatLib.Numerics

/-- Shift left in the one-word bitstream, returning zero at and beyond 64 positions. -/
@[inline] def shiftLeft (value : UInt64) (shift : Nat) : UInt64 :=
  if shift < 64 then
    value <<< UInt64.ofNat shift
  else
    0

-- Named predicates keep their constants out of runtime carrier closures.
/-- Whether the discarded low-bit suffix is nonzero. -/
@[always_inline] def hasLowBits (value : UInt64) (width : Nat) : Bool :=
  NativeWord.lowBits value width != 0

/-- Parity of the packed candidate used to break a midpoint tie. -/
@[always_inline] def isOdd (value : UInt64) : Bool :=
  (value &&& 1) != 0

/--
One-word implementation of the shared candidate carrier.

This transparent record is consumed only by always-inlined helpers, leaving the generated hot path
in primitive `UInt64` operations. Shifts return zero at and beyond the word width instead of using
the native modular shift amount; addition and the successor are the wrapping machine operations,
which the shared rounder applies only to values it has bounded.
-/
abbrev candidateCarrier : GuardStickyCarrier.CandidateCarrier UInt64 where
  bitAt := NativeWord.bitAt
  hasLowBits := hasLowBits
  ofWord := fun word => word
  shiftLeft := shiftLeft
  shiftRight := NativeWord.shiftRight
  fractionBelow := fun value leading => value - shiftLeft 1 leading
  add := fun left right => left + right
  lowOnes := NativeWord.lowMask
  increment := fun value => value + 1
  isOdd := isOdd
  log2 := fun value => value.log2.toNat

/-- Test a positive scalar target against the format's exact minimum-positive value. -/
@[inline] def isLessMinPositive
    (format : Format) (significand : UInt64) (exponent : Int) : Bool :=
  let minExponent := -(4 * Int.ofNat (format.payloadBits - 1))
  FixedWord.DyadicCompare.isLessNonnegative
    significand exponent 1 minExponent

/--
Round the nonnegative value `significand * 2 ^ exponent` to its complete unsigned code in one word.

Zero maps to code zero and targets below `minPos` to code one; every other target uses the shared
normalized rounder at the `UInt64` carrier.
-/
@[inline] def roundPositiveCodeWord
    (format : Format) (_heligible : NativeWord.Eligible format)
    (significand : UInt64) (exponent : Int) : UInt64 :=
  if significand == 0 then
    0
  else if isLessMinPositive format significand exponent then
    1
  else
    GuardStickyCarrier.roundNormalizedPositive candidateCarrier format significand exponent

/-- Natural-number view of positive native-field rounding. -/
@[inline] def roundPositiveCode
    (format : Format) (heligible : NativeWord.Eligible format)
    (significand : UInt64) (exponent : Int) : Nat :=
  (roundPositiveCodeWord format heligible significand exponent).toNat

/-- Round signed native dyadic fields and retain the complete code in one word. -/
@[inline] def roundCodeWord
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) : UInt64 :=
  NativeWord.restoreSignWord format negative
    (roundPositiveCodeWord format heligible significand exponent)

/-- Natural-number view of complete signed native-field rounding. -/
@[inline] def roundCodeNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) : Nat :=
  (roundCodeWord format heligible negative significand exponent).toNat

end FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky
