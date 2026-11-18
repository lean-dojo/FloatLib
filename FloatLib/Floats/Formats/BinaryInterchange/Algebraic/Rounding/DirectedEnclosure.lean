/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedRuntime
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Rounding a real from a rational enclosure, in every rounding direction

A real known only by a rational enclosure can be rounded when the enclosure decides the rounding:
it excludes zero, and its two endpoints round to the same encoding. This is the rounding test of
Ziv's strategy. `roundEnclosure?` performs it in any `IEEERoundingMode`, overflow results
included, and `zivRound?` repeats it on enclosures of doubling precision.

`DirectedEnclosureProof` proves that an accepted encoding is the rounding of every real in the
enclosure. The test cannot accept a real that lies on a rounding boundary, so a caller treats the
values it knows to be exact apart.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

/-- Round a rational in the direction `mode`. A zero is positive. -/
def roundRat (fmt : FloatFormat) (mode : IEEERoundingMode) (q : Rat) : Model fmt :=
  roundSigned fmt mode fun boundary => cmp q boundary

/--
Round a real known by a rational enclosure in the direction `mode`, when the enclosure decides
the rounding: it excludes zero and both endpoints round to the same encoding, compared as storage
words. `none` asks for a narrower enclosure.
-/
def roundEnclosure? (fmt : FloatFormat) (mode : IEEERoundingMode)
    (interval : Numerics.RationalInterval) : Option (Model fmt) :=
  if 0 < interval.lo ∨ interval.hi < 0 then
    let lower := roundRat fmt mode interval.lo
    if toNatBits lower = toNatBits (roundRat fmt mode interval.hi) then some lower else none
  else none

/--
Round a real from enclosures at the precisions `precision`, `2 * precision`, and so on, at most
`levels` of them: the first enclosure that decides the rounding gives the result.
-/
def zivRound? (fmt : FloatFormat) (mode : IEEERoundingMode)
    (enclose : Nat → Option Numerics.RationalInterval) : Nat → Nat → Option (Model fmt)
  | 0, _ => none
  | levels + 1, precision =>
      match (enclose precision).bind (roundEnclosure? fmt mode) with
      | some result => some result
      | none => zivRound? fmt mode enclose levels (2 * precision)

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
