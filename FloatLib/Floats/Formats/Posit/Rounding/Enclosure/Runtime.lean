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

An enclosure determines a unique rounded value when its endpoints select the same posit code.
The check uses only rational arithmetic and the format's existing appended-bit rounding rule.
An inconclusive check returns `none`, allowing a caller to refine the enclosure.

`roundPositive?` is for nonnegative functions. An interval crossing zero cannot be accepted for
a strictly positive target until its lower endpoint has become positive. The corresponding
theorem uses monotonicity of real posit rounding.
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
