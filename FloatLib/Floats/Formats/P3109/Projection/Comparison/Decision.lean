/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Runtime

/-!
# Exact threshold decisions for P3109 rounding

P3109 interim report v4.1 (14 September 2026), §4.7.4, unapproved draft.
Square roots and general exact comparisons share these nine rounding policies.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Format

/--
Select the upper candidate from exact threshold comparisons.

For stochastic A and B the threshold is the first fraction whose scaled floor reaches the
required integer. For C it is the midpoint below that integer, with the integer's tie parity.
The comparison argument lets the executable square comparisons and the real semantics share
these policy rules.
-/
def roundMagnitudeUp (format : Format) (mode : RoundingMode)
    (quantum : Int) (lower : Nat) (exact : Bool)
    (compareThreshold : Nat → Nat → Ordering) : Bool :=
  if exact then
    false
  else
    match mode with
    | .towardZero | .down => false
    | .up => true
    | .nearestAway =>
        compareThreshold 2 (2 * lower + 1) != .lt
    | .nearest =>
        let ordering := compareThreshold 2 (2 * lower + 1)
        ordering == .gt ||
          (ordering == .eq && !format.lowerCodeIsEven quantum lower)
    | .toOdd => format.lowerCodeIsEven quantum lower
    | .stochasticA random =>
        let scale := 2 ^ random.width
        let threshold := lower * scale + (scale - random.toNat)
        compareThreshold scale threshold != .lt
    | .stochasticB random =>
        let scale := 2 ^ (random.width + 1)
        let threshold := lower * scale + (scale - (2 * random.toNat + 1))
        compareThreshold scale threshold != .lt
    | .stochasticC random =>
        let unit := 2 ^ random.width
        let boundary := unit - random.toNat
        let scale := 2 * unit
        let threshold := lower * scale + (2 * boundary - 1)
        let ordering := compareThreshold scale threshold
        ordering == .gt || (ordering == .eq && boundary % 2 == 0)

end FloatLib.Floats.Formats.P3109.Format
