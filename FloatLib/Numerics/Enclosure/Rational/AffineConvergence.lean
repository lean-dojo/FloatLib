/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Endpoint convergence through affine interval operations

Each endpoint of a midpoint-radius interval, a negation, a sum, a difference or a scaled interval
is an affine function of input endpoints, so its limit is the same affine function of their
limits. Negation exchanges the endpoints, and subtraction pairs the lower endpoint of one interval
with the upper endpoint of the other. Scaling by a negative rational exchanges the endpoints too:
when both endpoints converge to the same real value, either sign gives the expected scaled limit.
A midpoint-radius interval whose radius vanishes has both endpoints converging to the midpoint
limit.
-/

public section

namespace FloatLib.Numerics.RationalInterval

open Filter
open scoped Topology

variable {α : Type*} {l : Filter α} {intervals left right : α → RationalInterval} {x y : ℝ}

/-- With a vanishing radius, the lower endpoints `midpoint - radius` tend to the midpoint limit. -/
theorem tendsto_around_lo {midpoint radius : α → ℚ}
    (hmidpoint : Tendsto (fun a => (midpoint a : ℝ)) l (𝓝 x))
    (hradius : Tendsto (fun a => (radius a : ℝ)) l (𝓝 0)) :
    Tendsto (fun a => ((around (midpoint a) (radius a)).lo : ℝ)) l (𝓝 x) := by
  simpa [around] using hmidpoint.sub hradius

/-- With a vanishing radius, the upper endpoints `midpoint + radius` tend to the midpoint limit. -/
theorem tendsto_around_hi {midpoint radius : α → ℚ}
    (hmidpoint : Tendsto (fun a => (midpoint a : ℝ)) l (𝓝 x))
    (hradius : Tendsto (fun a => (radius a : ℝ)) l (𝓝 0)) :
    Tendsto (fun a => ((around (midpoint a) (radius a)).hi : ℝ)) l (𝓝 x) := by
  simpa [around] using hmidpoint.add hradius

/-- Lower endpoints of negated intervals converge to the negated upper-endpoint limit. -/
theorem tendsto_neg_lo (hhi : Tendsto (fun a => ((intervals a).hi : ℝ)) l (𝓝 x)) :
    Tendsto (fun a => ((intervals a).neg.lo : ℝ)) l (𝓝 (-x)) := by
  simpa [neg] using hhi.neg

/-- Upper endpoints of negated intervals converge to the negated lower-endpoint limit. -/
theorem tendsto_neg_hi (hlo : Tendsto (fun a => ((intervals a).lo : ℝ)) l (𝓝 x)) :
    Tendsto (fun a => ((intervals a).neg.hi : ℝ)) l (𝓝 (-x)) := by
  simpa [neg] using hlo.neg

/-- Lower endpoints of interval sums converge to the sum of the lower-endpoint limits. -/
theorem tendsto_add_lo
    (hleft : Tendsto (fun a => ((left a).lo : ℝ)) l (𝓝 x))
    (hright : Tendsto (fun a => ((right a).lo : ℝ)) l (𝓝 y)) :
    Tendsto (fun a => (((left a).add (right a)).lo : ℝ)) l (𝓝 (x + y)) := by
  simpa [add] using hleft.add hright

/-- Upper endpoints of interval sums converge to the sum of the upper-endpoint limits. -/
theorem tendsto_add_hi
    (hleft : Tendsto (fun a => ((left a).hi : ℝ)) l (𝓝 x))
    (hright : Tendsto (fun a => ((right a).hi : ℝ)) l (𝓝 y)) :
    Tendsto (fun a => (((left a).add (right a)).hi : ℝ)) l (𝓝 (x + y)) := by
  simpa [add] using hleft.add hright

/-- Lower endpoints scaled by a fixed factor converge to the scaled limit, for any sign. -/
theorem tendsto_scaleNonnegative_lo
    (hlo : Tendsto (fun a => ((intervals a).lo : ℝ)) l (𝓝 x)) (factor : ℚ) :
    Tendsto (fun a => (((intervals a).scaleNonnegative factor).lo : ℝ)) l
      (𝓝 ((factor : ℝ) * x)) := by
  simpa [scaleNonnegative] using hlo.const_mul (factor : ℝ)

/-- Upper endpoints scaled by a fixed factor converge to the scaled limit, for any sign. -/
theorem tendsto_scaleNonnegative_hi
    (hhi : Tendsto (fun a => ((intervals a).hi : ℝ)) l (𝓝 x)) (factor : ℚ) :
    Tendsto (fun a => (((intervals a).scaleNonnegative factor).hi : ℝ)) l
      (𝓝 ((factor : ℝ) * x)) := by
  simpa [scaleNonnegative] using hhi.const_mul (factor : ℝ)

/-- The lower endpoints of scaled intervals converge to the scaled common limit. -/
theorem tendsto_scale_lo
    (hlo : Tendsto (fun a => ((intervals a).lo : ℝ)) l (𝓝 x))
    (hhi : Tendsto (fun a => ((intervals a).hi : ℝ)) l (𝓝 x)) (factor : ℚ) :
    Tendsto (fun a => (((intervals a).scale factor).lo : ℝ)) l
      (𝓝 ((factor : ℝ) * x)) := by
  by_cases h : 0 ≤ factor
  · simpa [scale, scaleNonnegative, h] using hlo.const_mul (factor : ℝ)
  · simpa [scale, scaleNonnegative, neg, h] using hhi.const_mul (factor : ℝ)

/-- The upper endpoints of scaled intervals converge to the scaled common limit. -/
theorem tendsto_scale_hi
    (hlo : Tendsto (fun a => ((intervals a).lo : ℝ)) l (𝓝 x))
    (hhi : Tendsto (fun a => ((intervals a).hi : ℝ)) l (𝓝 x)) (factor : ℚ) :
    Tendsto (fun a => (((intervals a).scale factor).hi : ℝ)) l
      (𝓝 ((factor : ℝ) * x)) := by
  by_cases h : 0 ≤ factor
  · simpa [scale, scaleNonnegative, h] using hhi.const_mul (factor : ℝ)
  · simpa [scale, scaleNonnegative, neg, h] using hlo.const_mul (factor : ℝ)

/-- Lower endpoints of interval differences converge to the difference of endpoint limits. -/
theorem tendsto_sub_lo
    (hleft : Tendsto (fun a => ((left a).lo : ℝ)) l (𝓝 x))
    (hright : Tendsto (fun a => ((right a).hi : ℝ)) l (𝓝 y)) :
    Tendsto (fun a => (((left a).sub (right a)).lo : ℝ)) l (𝓝 (x - y)) := by
  simpa only [sub, sub_eq_add_neg] using tendsto_add_lo hleft (tendsto_neg_lo hright)

/-- Upper endpoints of interval differences converge to the difference of endpoint limits. -/
theorem tendsto_sub_hi
    (hleft : Tendsto (fun a => ((left a).hi : ℝ)) l (𝓝 x))
    (hright : Tendsto (fun a => ((right a).lo : ℝ)) l (𝓝 y)) :
    Tendsto (fun a => (((left a).sub (right a)).hi : ℝ)) l (𝓝 (x - y)) := by
  simpa only [sub, sub_eq_add_neg] using tendsto_add_hi hleft (tendsto_neg_hi hright)

end FloatLib.Numerics.RationalInterval
