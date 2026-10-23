/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Runtime

/-!
# Logarithm bounds for rational powers

For a positive base and target, `base ^ exponent` lies below the target exactly when
`exponent * log base - log target` is negative. Rational enclosures of the two logarithms give an
enclosure of this difference, and raising their degree narrows it. A comparison never needs an
integer power of the base or the target.

The interval can separate a nonzero difference from zero but cannot certify equality, which
`RationalPower.powEq` decides.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- Enclose the logarithm of a power divided by a target, for positive base and target. -/
def logDifference (base exponent target : ℚ) (degree : Nat) : RationalInterval :=
  ((Enclosure.log base degree).scale exponent).sub (Enclosure.log target degree)

end FloatLib.Numerics.RationalPower
