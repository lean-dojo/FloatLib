/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Prefix.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Runtime

/-!
# Executable direct posit quotient packing

A quotient of two dyadics need not be dyadic, and this algorithm copes without building a
rational. It normalizes both significands, generates the leading quotient window that the
destination format needs, and records in the low sticky bit whether any bit it didn't generate is
a one. That finite stream goes to the same direct regime, exponent, and fraction rounder that exact
dyadics use.

Every width takes the same path: one integer division, one exact remainder test, and one
guard/sticky packing pass. `Direct.Proof` proves that this equals exact quotient rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/--
Position of the quotient's leading bit after normalization.

A Posit has `payloadBits` bits below its sign. Keeping the quotient through that leading position
leaves enough exponent and fraction stream for every possible guard bit, and the jammed low bit
records whether any later quotient digit is nonzero.
-/
@[inline] def prefixLeading (format : Format) : Nat :=
  format.payloadBits

/--
Normalize two positive significands to the same leading position.

The operands are shifted by different amounts to reach a common leading position. That changes
their ratio by a power of two fixed by the original leading positions, and the result exponent
makes up for it.
-/
structure NormalizedSignificands where
  /-- Numerator shifted so its leading bit reaches the common position. -/
  numerator : Nat
  /-- Denominator shifted so its leading bit reaches the common position. -/
  denominator : Nat
  /-- Leading-bit position of the original numerator. -/
  numeratorLeading : Nat
  /-- Leading-bit position of the original denominator. -/
  denominatorLeading : Nat

/-- Shift two positive significands to their shared leading-bit position. -/
@[inline] def normalizeSignificands
    (numerator denominator : Nat) : NormalizedSignificands :=
  let numeratorLeading := numerator.log2
  let denominatorLeading := denominator.log2
  let commonLeading := max numeratorLeading denominatorLeading
  { numerator := numerator <<< (commonLeading - numeratorLeading)
    denominator := denominator <<< (commonLeading - denominatorLeading)
    numeratorLeading
    denominatorLeading }

/--
Generate a normalized quotient prefix at a given leading position.

For nonzero input significands, a normalized ratio below one emits one extra digit, and a ratio of
at least one begins with its known leading one. Either way the quotient prefix has leading position
`leading`, and the Euclidean remainder determines its exact sticky bit.
-/
@[inline] def prefixAtLeading
    (leading : Nat)
    (numerator denominator : FloatLib.Numerics.Dyadic) :
    FloatLib.Numerics.Dyadic :=
  let normalized :=
    normalizeSignificands numerator.significand denominator.significand
  let steps :=
    if normalized.numerator < normalized.denominator then leading + 1 else leading
  let scaledNumerator := normalized.numerator <<< steps
  let quotient := scaledNumerator / normalized.denominator
  let remainder := scaledNumerator % normalized.denominator
  { negative := false
    significand := jamRemainder quotient remainder
    exponent :=
      numerator.exponent - denominator.exponent +
        Int.ofNat normalized.numeratorLeading -
        Int.ofNat normalized.denominatorLeading -
        Int.ofNat steps }

/--
Generate the destination-width normalized quotient prefix.

The policy depends on representable precision alone. No named storage backend or special format
width enters into it.
-/
@[inline] def quotientPrefix
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    FloatLib.Numerics.Dyadic :=
  prefixAtLeading (prefixLeading format) numerator denominator

/-! ## Complete direct quotient rounding -/

/-- Round a positive quotient in one pass from its normalized prefix and exact sticky bit. -/
@[inline] def roundPositiveCode
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) : Nat :=
  if numerator.significand == 0 || numerator.negative ||
      denominator.significand == 0 || denominator.negative then
    0
  else
    DirectDyadicPacking.roundPositiveCode format
      (quotientPrefix format numerator denominator)


/-- Pack the positive quotient code that `roundPositiveCode` selects. -/
@[inline] def roundPositive
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    Model format :=
  Model.ofNatBits
    (roundPositiveCode format numerator denominator)


/-- Round a signed quotient using the direct positive packer and shared special-value rules. -/
@[noinline] def round
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    Model format :=
  DyadicQuotient.roundSignedWith format (roundPositive format)
    numerator denominator

/--
Complete signed quotient encoding for storage kernels that keep codes rather than models.

Division by zero emits the NaR code, a zero numerator emits zero, and the sign of a finite
quotient is restored on the positive code. `roundCode_eq_toNatBits` identifies this with `round`.
-/
@[inline] def roundCode
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) : Nat :=
  if denominator.significand == 0 then
    format.signMaskNat
  else if numerator.significand == 0 then
    0
  else
    DyadicRounding.restoreSignCode format
      (Bool.xor numerator.negative denominator.negative)
      (roundPositiveCode format
        (DyadicRounding.magnitude numerator) (DyadicRounding.magnitude denominator))

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient
