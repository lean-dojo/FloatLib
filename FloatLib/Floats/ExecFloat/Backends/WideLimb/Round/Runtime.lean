/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Runtime

/-!
# Wide-limb normal rounding runtime

Accepted nonzero wide-limb arithmetic results pass through rounding of an exact or sticky-jammed
significand at an unsigned scale. `roundNormal?` performs that step on limbs: it locates
the leading bit, rounds to `fracWidth + 1` bits with ties to even, detects a carry into the next
binade, checks the exponent range, and packs. It returns `none` if the leading position is below
the normal range before rounding or above the finite range after carry normalization. The
dispatcher handles declined cases with the exact baseline. `Round.Proof` shows that an accepted
result is the arbitrary-precision product rounder
`FiniteProductRound.round` applied to the exact value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/--
Round an exact or sticky-jammed significand in the unsigned product-scale coordinate.

For the numerical contract, the conventional IEEE descriptor has `expWidth ≤ 32` and the limb
value is `shiftRightJam exact jam`, with `exact ≠ 0`. Either `jam = 0` or
`2 ^ (fmt.fracWidth + jam + 2) ≤ exact` is required. An accepted result then agrees with rounding
signed magnitude `exact * 2^(scale - 2 * ieeeSubnormalAlignExp fmt)`, interpreting the exponent
subtraction in `Int`. The bounds are supplied by callers, not checked here.
-/
def roundNormal? (fmt : FloatFormat) (sign : Bool) (significand : LimbArray) (jam scale : Nat) :
    Option (Value fmt) :=
  let leading := significand.log2
  let position := leading + jam + scale
  if position < fmt.bias + 2 * fmt.fracWidth - 1 then
    none
  else
    let rounded :=
      if fmt.fracWidth ≤ leading then
        significand.roundShiftRightEven (leading - fmt.fracWidth)
      else
        significand.shiftLeft (fmt.fracWidth - leading)
    let carry := rounded.log2 == fmt.fracWidth + 1
    let normalizedPosition := if carry then position + 1 else position
    if 3 * fmt.bias + 2 * fmt.fracWidth - 2 < normalizedPosition then
      none
    else
      some <| pack fmt sign
        (UInt32.ofNat (normalizedPosition - (fmt.bias + 2 * fmt.fracWidth - 2)))
        (rounded.lowBits fmt.fracWidth)

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
