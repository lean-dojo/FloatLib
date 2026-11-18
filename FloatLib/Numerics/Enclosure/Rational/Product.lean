/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Products and prefixed sequences of rational intervals

`RationalInterval.mul` is the four-corner product of two intervals, and `divPositive` the
quotient by an interval of positive numbers. `RationalInterval.prefixed` replaces the first terms
of a sequence of enclosures by others: a slow sequence whose convergence is proved can start with
fast enclosures that are only proved sound, and it still converges (`Converges.prefixed`).
-/

@[expose] public section

namespace FloatLib.Numerics.RationalInterval

/-- The product interval: the least and the greatest of the four endpoint products. -/
def mul (left right : RationalInterval) : RationalInterval :=
  ⟨min (min (left.lo * right.lo) (left.lo * right.hi))
      (min (left.hi * right.lo) (left.hi * right.hi)),
    max (max (left.lo * right.lo) (left.lo * right.hi))
      (max (left.hi * right.lo) (left.hi * right.hi))⟩

/--
The quotient by an interval of positive numbers: the product with the interval of the inverses.
-/
def divPositive (numerator denominator : RationalInterval) : RationalInterval :=
  numerator.mul ⟨1 / denominator.hi, 1 / denominator.lo⟩

/-- The sequence `first` below `count`, and `rest` from there on. -/
def prefixed (first : Nat → RationalInterval) (count : Nat) (rest : Nat → RationalInterval)
    (n : Nat) : RationalInterval :=
  if n < count then first n else rest n

end FloatLib.Numerics.RationalInterval
