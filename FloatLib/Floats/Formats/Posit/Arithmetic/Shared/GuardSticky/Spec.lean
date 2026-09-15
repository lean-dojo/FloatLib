/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Representation-independent Posit guard and sticky bits

These functions inspect the exact exponent-and-fraction tail using natural numbers only. They are
the common specification refined by the one-word and two-limb execution carriers; no fixed-width
storage implementation is imported here.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

/--
Read one bit of a normalized exponent/fraction tail.

The first two positions are the Posit exponent, most-significant bit first. Later positions walk
the significand below its leading one and then return exact zero padding.
-/
@[inline] def tailBit
    (exponentField significand leading index : Nat) : Bool :=
  if index < 2 then
    exponentField.testBit (1 - index)
  else
    let fractionIndex := index - 2
    if fractionIndex < leading then
      significand.testBit (leading - fractionIndex - 1)
    else
      false

/--
Whether any exact exponent/fraction bit remains after `consumed` leading tail positions.

Before both exponent bits have been consumed, the suffix consists of the low exponent bits and
the explicit fraction. Afterwards it is exactly a low-bit test on the significand.
-/
@[inline] def tailHasNonzeroAfter
    (exponentField significand leading consumed : Nat) : Bool :=
  if consumed < 2 then
    let remainingExponentBits := 2 - consumed
    exponentField % 2 ^ remainingExponentBits != 0 ||
      significand % 2 ^ leading != 0
  else
    let consumedFractionBits := consumed - 2
    if consumedFractionBits < leading then
      significand % 2 ^ (leading - consumedFractionBits) != 0
    else
      false

end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
