/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Rounding rational enclosures to posits

When both endpoints of a rational enclosure round to the same posit code, everything inside rounds
to that code too, and the enclosure has settled the answer. `roundPositive?` checks this with
rational arithmetic and the format's appended-bit rule. If the endpoints disagree it returns
`none`, and the caller can tighten the enclosure and try again.

It is meant for nonnegative targets. For a strictly positive target, an interval that crosses
zero is accepted once its lower endpoint has become positive and not before. Acceptance rests on
the monotonicity of real posit rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.Enclosure

open FloatLib.Numerics

/--
Accept an enclosure when both endpoints select the same nonnegative posit code.

The caller supplies the proof that its real target belongs to the enclosure in
`eq_roundPositive_of_roundPositive?_eq_some`.
-/
def roundPositive? (format : Format) (interval : RationalInterval) : Option (Model format) :=
  let lower := Model.roundPositiveCode format interval.lo
  let upper := Model.roundPositiveCode format interval.hi
  if lower = upper then some (Model.ofNatBits lower) else none

end FloatLib.Floats.Formats.Posit.Model.Enclosure
