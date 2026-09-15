/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime

/-!
# Two-limb posit rounding runtime

Posit rounding uses the two-limb execution refinement whenever the exact significand fits in
`UInt128`. Wider exact intermediates retain the same field-oriented guard/sticky semantics in
the arbitrary-width direct rounder. Selection is by representation capacity rather than named
format, and neither branch uses a candidate certificate or search path.

Semantic refinement laws are in `Rounding.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding

open FloatLib.Numerics

/--
Round a positive exact dyadic using two limbs when its significand fits.

The outer zero and sign decisions are representation-independent. A significand below `2^128`
then stays in two native words through minimum-positive comparison, field packing, guard/sticky
inspection, and nearest-even increment. Only a genuinely wider intermediate crosses to the
arbitrary-width implementation, which applies the same exact rounding semantics.
-/
@[inline] def roundPositiveCode
    (format : Format) (_heligible : NativeLimb.Eligible format)
    (target : FloatLib.Numerics.Dyadic) : Nat :=
  if target.significand == 0 || target.negative then
    0
  else if _hcapacity : target.significand < 2 ^ 128 then
    let significand :=
      FloatLib.Numerics.FixedWord.UInt128.ofNat target.significand
    if GuardSticky.isLessMinPositive format significand target.exponent then
      1
    else
      (GuardStickyCarrier.roundNormalizedPositive GuardSticky.candidateCarrier format
        significand target.exponent).toNat
  else
    DirectDyadicPacking.roundPositiveCode format target

/-- Pack the code selected by two-limb positive rounding. -/
@[inline] def roundPositive
    (format : Format) (heligible : NativeLimb.Eligible format)
    (target : FloatLib.Numerics.Dyadic) : Model format :=
  Model.ofNatBits (roundPositiveCode format heligible target)

/-- Round any exact dyadic using unique posit zero and whole-word negative symmetry. -/
@[noinline] def round
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) : Model format :=
  if value.significand == 0 then
    Model.zero format
  else
    let magnitude := DyadicRounding.magnitude value
    if value.negative then
      Model.neg (roundPositive format heligible magnitude)
    else
      roundPositive format heligible magnitude

/--
Return the complete encoding selected by proved two-limb rounding.

The result remains a natural number only at the arithmetic boundary. Configured pair storage
immediately splits it into two `UInt64` limbs, avoiding construction of an exact-width `Model`.
-/
@[noinline] def roundCodeNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) : Nat :=
  if value.significand == 0 then
    0
  else
    let magnitude := DyadicRounding.magnitude value
    let positiveCode := roundPositiveCode format heligible magnitude
    DyadicRounding.restoreSignCode format value.negative positiveCode

end FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding
