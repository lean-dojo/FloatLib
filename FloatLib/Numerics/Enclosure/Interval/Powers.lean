/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic

/-!
# Real powers and logarithms with a specified base

Real powers use `exp (log x * y)` on strictly positive base intervals. Both the base and the
exponent may vary. Logarithms with a specified base divide the argument's logarithm by the
base's logarithm; the latter enclosure must exclude zero. All intermediate bounds are rational.
`PowersProof` proves containment for every real member of the input intervals.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/--
Enclose real powers on a strictly positive base interval, with a possibly variable real exponent.

A nonpositive lower base endpoint is rejected, including zero: logarithmic reduction cannot
enclose it. Negative and zero exponents are allowed when the base interval is positive.
-/
def rpowBounds? (I J : Interval ℚ) (terms : Nat) : Option (Interval ℚ) := do
  let logarithm ← logBounds? I terms
  let product ← mul? Internal.rationalOutwardRounding logarithm J
  return expBounds product terms

/--
Enclose `logb b x` when the base and argument intervals are positive and the base logarithm
enclosure excludes zero. A base range containing one, or an insufficiently accurate logarithm
enclosure, is rejected by the interval division.
-/
def logbBounds? (B I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) := do
  let baseLog ← logBounds? B terms
  let argumentLog ← logBounds? I terms
  div? Internal.rationalOutwardRounding argumentLog baseLog

end FloatLib.Numerics.Interval
