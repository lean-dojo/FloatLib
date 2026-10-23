/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Binary rounding of rational enclosures

Exact rational rounding accepts an enclosure when both endpoints select the same finite IEEE
encoding. The endpoints are compared as encodings, so they must also agree on the sign of zero.
The proofs show that an accepted result is finite and has the real value of the correctly rounded
exact value, but they do not state which sign a zero result carries. An inconclusive enclosure
returns `none` for refinement.

An enclosure may also carry a binary scale: `roundScaled? fmt interval scale` rounds the endpoints
of `interval` times `2 ^ scale` without forming that power, so a result far outside the range of
the interval's rationals costs no more than one near one.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Enclosure

open FloatLib.Numerics

/-- Round a signed rational times `2 ^ scale`, taking its sign from the exact value. -/
def roundEndpoint (fmt : FloatFormat) (value : ℚ) (scale : ℤ) : Model fmt :=
  roundRatScaled fmt (decide (value < 0)) value.num.natAbs value.den scale

/--
Return a finite encoding only when both endpoints of `interval` times `2 ^ scale` select it by
nearest-even rational rounding.

Unsupported descriptors, overflowing endpoints, and differing endpoint results return `none`.
-/
def roundScaled? (fmt : FloatFormat) (interval : RationalInterval) (scale : ℤ) :
    Option (Model fmt) :=
  if fmt.isIEEE then
    let lower := roundEndpoint fmt interval.lo scale
    let upper := roundEndpoint fmt interval.hi scale
    if isFinite lower = true ∧ lower = upper then some lower else none
  else none

/-- Return a finite encoding only when both endpoints select it by nearest-even rounding. -/
def round? (fmt : FloatFormat) (interval : RationalInterval) : Option (Model fmt) :=
  roundScaled? fmt interval 0

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Enclosure
