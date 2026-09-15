/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime

/-!
# Rational reduction and enclosures for the complex argument

The input order is `(x, y)` for `arg (x + i*y)`. A rational slope and an integer multiple of
π/4 describe the principal branch `(-π, π]`. The negative real axis selects `+π`.
At the origin this numerical helper uses the totalized mathematical value zero; format
wrappers whose contract rejects the origin must do so before rounding.
-/

@[expose] public section

namespace FloatLib.Numerics.TrigonometricComparison

/--
Return a slope and a multiple of π/4 whose shifted arctangent is the principal argument.
The second component is rational to support exact boundary shifts in comparisons of `arg / π`.
-/
def atan2Reduction (x y : ℚ) : ℚ × ℚ :=
  if 0 < x then (y / x, 0)
  else if x < 0 then (y / x, if 0 ≤ y then 4 else -4)
  else (0, if 0 < y then 2 else if y < 0 then -2 else 0)

/--
Enclose the principal argument using exact rational arctangent and Machin π/4 enclosures.
All series arguments are reduced by the existing arctangent kernel.
-/
def atan2Interval (x y : ℚ) (degree : Nat) : RationalInterval :=
  let reduced := atan2Reduction x y
  (Enclosure.atan reduced.1 degree).add ((Enclosure.piQuarter degree).scale reduced.2)

end FloatLib.Numerics.TrigonometricComparison
