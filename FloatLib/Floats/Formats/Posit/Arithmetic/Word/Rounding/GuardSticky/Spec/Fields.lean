/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Shared.GuardSticky.Spec
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Runtime

/-!
# Field-oriented guard-and-sticky Posit rounding

Field-oriented rounding reads the finite exponent/fraction tail directly from its normalized
fields. It is the representation-independent executable kernel: arbitrary-width backends use
these `Nat` operations directly, while fixed-word and fixed-limb backends refine the same bit
and suffix queries to native masks and shifts.

Unlike `exactTailRaw`, the field-oriented kernel never first concatenates the exponent and
fraction into a larger temporary natural number.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

/--
Round an interior normalized Posit directly from its fields.

This is the general executable guard/sticky kernel for every width. It retains the same packed
lower candidate as `roundInteriorCode`, but reads the discarded suffix in place instead of
materializing the complete exponent/fraction stream.
-/
@[inline] def roundInteriorCodeFromFields
    (format : Format) (regime : Int)
    (exponentField significand leading regimeFieldBits : Nat) : Nat :=
  let lower :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  let retainedTailBits := format.payloadBits - regimeFieldBits
  let guard :=
    tailBit exponentField significand leading retainedTailBits
  let sticky :=
    tailHasNonzeroAfter exponentField significand leading
      (retainedTailBits + 1)
  if guard && (sticky || lower % 2 != 0) then
    lower + 1
  else
    lower

end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
