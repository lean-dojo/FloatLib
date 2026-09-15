/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Endpoint convergence under scaling and subtraction

Scaling by a negative rational exchanges the lower and upper endpoints. When both endpoints
converge to the same real value, either sign gives the expected scaled limit. Subtraction pairs
the lower endpoint of one interval with the upper endpoint of the other.
-/

public section

namespace FloatLib.Numerics.RationalInterval

open Filter
open scoped Topology

variable {α : Type*} {l : Filter α} {intervals left right : α → RationalInterval} {x y : ℝ}

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
  simpa [sub, add, neg, sub_eq_add_neg] using hleft.sub hright

/-- Upper endpoints of interval differences converge to the difference of endpoint limits. -/
theorem tendsto_sub_hi
    (hleft : Tendsto (fun a => ((left a).hi : ℝ)) l (𝓝 x))
    (hright : Tendsto (fun a => ((right a).lo : ℝ)) l (𝓝 y)) :
    Tendsto (fun a => (((left a).sub (right a)).hi : ℝ)) l (𝓝 (x - y)) := by
  simpa [sub, add, neg, sub_eq_add_neg] using hleft.sub hright

end FloatLib.Numerics.RationalInterval
