/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.Runtime

/-!
# Rational-power comparison using logarithm bounds

Clearing an exponent's denominator is exact, but can create enormous integers even when the
input rationals are small. Bounds for `exponent * log base - log target` often decide the same
comparison with much less work. An interval that contains zero leaves the comparison undecided;
the exact algebraic comparator then handles it, including equality.

The degree controls only the preliminary bound computation. It is never used to guess a result
or to replace an undecided comparison with a rounded approximation.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- Enclose the logarithm of a power divided by a target, for positive base and target. -/
def logDifference (base exponent target : ℚ) (degree : Nat) : RationalInterval :=
  ((Enclosure.log base degree).scale exponent).sub (Enclosure.log target degree)

/--
Compare a rational real power with a rational target, using bounds before exact arithmetic.

The semantic domain has `base > 0`; the target and exponent may have either sign. Exact
integer-power comparison remains the fallback, so hard cases can still require large integers.
-/
def compareWithEnclosure (base exponent target : ℚ) (degree : Nat) : Ordering :=
  if base = 1 ∨ exponent = 0 then cmp (1 : ℚ) target
  else if target ≤ 0 then .gt
  else
    let difference := logDifference base exponent target degree
    if difference.hi < 0 then .lt
    else if 0 < difference.lo then .gt
    else compare base exponent target

end FloatLib.Numerics.RationalPower
