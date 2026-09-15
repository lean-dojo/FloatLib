/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Prefix.Runtime

/-!
# Executable direct posit square-root packing

The square root of an exact dyadic need not be dyadic. This module scales the source by an even
power of two, computes its integer square root, and jams the exact square remainder into the low
bit of a prefix with enough bits for the destination format. The ordinary direct Posit packer
then performs the complete guard/sticky rounding step.

The kernel is width-generic. Its equality to exact square-root rounding is proved in `Direct.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicSquareRoot

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/--
Number of generated square-root fraction bits.

A Posit has `payloadBits` bits below its sign. Generating the root to that precision leaves enough
exponent/fraction stream for every possible guard bit; the jammed low bit records whether the
exact root has any later nonzero digit.
-/
@[inline] def prefixPrecision (format : Format) : Nat :=
  format.payloadBits

/-- Parity of the source dyadic exponent, represented as zero or one. -/
@[inline] def exponentParity
    (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  (radicand.exponent.emod 2).toNat

/-- Integer radicand whose square root carries `precision` generated fraction bits. -/
@[inline] def scaledRadicand
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  Nat.shiftLeft radicand.significand
    (exponentParity radicand + 2 * precision)

/-- Truncated integer square root at the requested fractional precision. -/
@[inline] def truncatedRoot
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  Nat.sqrt (scaledRadicand precision radicand)

/-- Exact square remainder left by the truncated integer root. -/
@[inline] def squareRemainder
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  let scaled := scaledRadicand precision radicand
  let root := Nat.sqrt scaled
  scaled - root * root

/--
Generate a normalized square-root prefix at an explicit fractional precision.

Writing the source exponent as `2q + r`, where `r` is zero or one, reduces the operation to an
integer square root of `significand * 2^(r + 2 * precision)`. The Euclidean square remainder
determines whether the exact root continues beyond the generated prefix.
-/
@[inline] def prefixAtPrecision
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) :
    FloatLib.Numerics.Dyadic :=
  { negative := false
    significand :=
      jamRemainder
        (truncatedRoot precision radicand)
        (squareRemainder precision radicand)
    exponent :=
      radicand.exponent.ediv 2 - Int.ofNat precision }

/--
Generate the destination-width normalized square-root prefix.

The policy depends only on representable precision, not on a named storage backend or special
format width.
-/
@[inline] def rootPrefix
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) :
    FloatLib.Numerics.Dyadic :=
  prefixAtPrecision (prefixPrecision format) radicand

/--
Round a nonnegative square root directly from its normalized prefix and exact sticky bit.

Integer square-root and remainder calculations determine the prefix; the shared guard/sticky
packer selects the final code. This helper returns zero for zero or negative inputs.
-/
@[inline] def roundCode
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  if radicand.significand == 0 || radicand.negative then
    0
  else
    DirectDyadicPacking.roundPositiveCode format
      (rootPrefix format radicand)

/-- Pack the code selected by direct prefix square-root rounding. -/
@[inline] def round
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) : Model format :=
  Model.ofNatBits (roundCode format radicand)


end FloatLib.Floats.Formats.Posit.Model.DirectDyadicSquareRoot
