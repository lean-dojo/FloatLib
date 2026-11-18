/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Product.AngleProof

/-!
# Total comparators for the products of the complex exponential functions

`ProductComparison.prepare growth trig a b` compares `growth a * trig b` with any rational: for
example `exp a * cos b`, the real part of `exp (a + i b)`. It never forms the unbounded factor,
so `exp a * cos b` is compared with the overflow threshold of a format as cheaply as with one.
The enclosures of the bounded factor are shared across boundaries, and the erased termination
proof is `Admissible.exists_decide?_isSome`.
-/

@[expose] public section

namespace FloatLib.Numerics.ProductComparison

/--
A total comparator of the admissible product `growth a * trig b` with rational boundaries. The
first `levels` enclosures of the bounded factor are shared, and refinement past them is unbounded.
-/
def prepare (growth : Growth) (trig : Trig) (a b : ℚ) (levels : Nat)
    (h : Admissible growth trig a b) : ℚ → Ordering :=
  let cache := Enclosure.Comparison.cacheIntervals (trig.intervals b) levels
  fun boundary => compare (growth.compare a) cache.get boundary
    (h.exists_decide?_isSome levels boundary)

/-- The prepared comparator orders the real product against every rational boundary. -/
theorem prepare_eq_real (growth : Growth) (trig : Trig) (a b : ℚ) (levels : Nat)
    (h : Admissible growth trig a b) (boundary : ℚ) :
    prepare growth trig a b levels h boundary =
      cmp (growth.eval (a : ℝ) * trig.eval (b : ℝ)) (boundary : ℝ) :=
  compare_eq_real h.growth_pos (growth.compare_eq_real a) _
    (fun n => by
      simpa only [Enclosure.Comparison.cacheIntervals_apply] using
        (trig.converges_intervals b).contains n)
    boundary _

end FloatLib.Numerics.ProductComparison
