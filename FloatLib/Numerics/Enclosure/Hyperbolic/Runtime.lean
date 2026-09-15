/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Runtime

/-!
# Rational enclosures for hyperbolic sine and cosine

Exact interval addition, subtraction, and scaling combine the existing exponential
enclosures. Callers comparing large inputs first use logarithmic bounds to avoid constructing
an exponential whose size greatly exceeds the rational boundary.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

/-- Enclose `(exp x - exp (-x)) / 2` with exact rational endpoint arithmetic. -/
def sinh (x : ℚ) (degree : Nat) : RationalInterval :=
  ((exp x degree).sub (exp (-x) degree)).scaleNonnegative (1 / 2)

/-- Enclose `(exp x + exp (-x)) / 2` with exact rational endpoint arithmetic. -/
def cosh (x : ℚ) (degree : Nat) : RationalInterval :=
  ((exp x degree).add (exp (-x) degree)).scaleNonnegative (1 / 2)

end FloatLib.Numerics.Enclosure
