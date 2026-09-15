/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Runtime

/-!
# Rational enclosures at rational multiples of pi

The angle is reduced modulo two exactly, before multiplication by an enclosed value of pi.
Consequently both the Taylor argument and the error multiplier are bounded independently of
large integer parts of the input. The radius includes the uncertainty in pi. These operations
use neither a rounded value of pi nor an approximate rational-angle equality test.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

/-- Integer full turns removed from a pi-scaled angle, with upward half ties. -/
def piTurns (argument : ℚ) : Int :=
  ⌊argument / 2 + 1 / 2⌋

/-- Exact reduction of a pi-scaled angle to `[-1, 1)`. -/
def piReduced (argument : ℚ) : ℚ :=
  argument - 2 * (piTurns argument : ℚ)

/-- A rational Taylor argument obtained from the lower, clamped quarter-period enclosure. -/
def piArgument (argument : ℚ) (degree : Nat) : ℚ :=
  4 * piReduced argument * trigQuarter degree

/-- Error introduced by using the rational approximation to pi. -/
def piArgumentError (argument : ℚ) (degree : Nat) : ℚ :=
  4 * |piReduced argument| * ((piQuarter degree).hi - trigQuarter degree)

/-- Combined Taylor remainder and argument uncertainty. -/
def piRadius (argument : ℚ) (degree : Nat) : ℚ :=
  trigRadius (piArgument argument degree) degree + piArgumentError argument degree

/-- Enclose `sin (argument * π)` after exact rational angle reduction. -/
def sinPi (argument : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (RationalInterval.around (sinTaylor (piArgument argument degree) degree)
    (piRadius argument degree))

/-- Enclose `cos (argument * π)` with the same exact angle reduction. -/
def cosPi (argument : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (RationalInterval.around (cosTaylor (piArgument argument degree) degree)
    (piRadius argument degree))

/-- A division-free enclosure of the residual used to compare pi-scaled tangent. -/
def sinPiSubCos (argument boundary : ℚ) (degree : Nat) : RationalInterval :=
  (sinPi argument degree).sub ((cosPi argument degree).scale boundary)

end FloatLib.Numerics.Enclosure
