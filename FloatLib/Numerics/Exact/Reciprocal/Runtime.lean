/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Compare

/-!
# Exact comparisons with reciprocals

`compareReciprocal compare` compares `t⁻¹` with rational boundaries, given an exact comparator
for a nonzero real `t`. The comparison with zero gives the sign of `t`. A boundary of the other
sign, or zero, is then decided by that sign alone. Otherwise the boundary and `t` have the same
sign, and inversion reverses the order on each half-line: `t⁻¹ < b` exactly when `b⁻¹ < t`. The
result is the reversed comparison of `t` with `b⁻¹`, so no reciprocal enclosure is formed.

Secant, cosecant and cotangent are reciprocals of cosine, sine and tangent, and their hyperbolic
counterparts are reciprocals of the hyperbolic cosine, sine and tangent. Their poles are special
values that a wrapper handles before rounding, so this comparator is used only for `t ≠ 0`.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Compare `t⁻¹` with a rational boundary, given an exact comparator `compare` for a real `t`.

The contract requires `t ≠ 0`, so the result returned when `compare 0 = .eq` is never used.
-/
def compareReciprocal (compare : ℚ → Ordering) (boundary : ℚ) : Ordering :=
  match compare 0 with
  | .gt => if boundary ≤ 0 then .gt else (compare boundary⁻¹).swap
  | .lt => if 0 ≤ boundary then .lt else (compare boundary⁻¹).swap
  | .eq => .eq

end FloatLib.Numerics
