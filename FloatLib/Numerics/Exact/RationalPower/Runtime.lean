/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Compare

/-!
# Exact comparisons with rational powers

For a positive rational base and a nonnegative rational target, comparing `base ^ (p / q)`
with the target is equivalent to comparing `base ^ p` with `target ^ q`. The latter uses only
exact integer powers in the rational field. Equality is decidable too, so this comparison can
resolve a rounding tie without an approximation or a refinement loop.

The integers can grow large. This is a reference algorithm, with no fixed bound on intermediate
storage. The corresponding real-power theorem is in `RationalPower.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/--
Compare a rational power with a rational target by raising both sides to the exponent denominator.

The real interpretation requires `0 < base` and `0 ≤ target`. A format handles exceptional
values and negative targets before using this kernel.
-/
def compare (base exponent target : ℚ) : Ordering :=
  cmp (base ^ exponent.num) (target ^ exponent.den)

end FloatLib.Numerics.RationalPower
