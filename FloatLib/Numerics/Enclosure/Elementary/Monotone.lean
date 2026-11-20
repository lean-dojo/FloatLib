/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Slopes
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The value of a function from the sign of its derivative

A function whose derivative is nonnegative between `l` and `x` is at `x` at least what it is at
`l`, and more when the derivative is positive; with a derivative that is nonpositive between `x`
and `u` it is at `x` at least what it is at `u`. An enclosure does not separate two sides of a
comparison that meet at an end of the range of the variable, but the derivative of their
difference may have a sign that an enclosure shows: `Real.exp x - (1 + x)` vanishes at `0`, and
its derivative `Real.exp x - 1` is positive for `0 < x`.

## Main statements

* `le_of_deriv_nonneg`, `lt_of_deriv_pos`: the value at `x` against the value at `l ≤ x`.
* `le_of_deriv_nonpos`, `lt_of_deriv_neg`: the value at `x` against the value at `u ≥ x`.
* `hasDerivAt_tanh_comp`, `hasDerivAt_tan_comp`: the chain rule for the hyperbolic tangent and
  the tangent, in the form of the rules of Mathlib for the other elementary functions.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- A function that has the derivative `f' t` at every `t` of `[l, x]`, with `0 ≤ f' t` for
`l < t < x`, is at `x` at least what it is at `l`. -/
theorem le_of_deriv_nonneg {f f' : ℝ → ℝ} {l x : ℝ} (hx : l ≤ x)
    (hd : ∀ t, l ≤ t → t ≤ x → HasDerivAt f (f' t) t)
    (hs : ∀ t, l < t → t < x → 0 ≤ f' t) : f l ≤ f x := by
  have hmono : MonotoneOn f (Set.Icc l x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc l x)
      (fun t ht => (hd t ht.1 ht.2).continuousAt.continuousWithinAt)
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t ht.1.le ht.2.le).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hd t ht.1.le ht.2.le).deriv]
      exact hs t ht.1 ht.2
  exact hmono (Set.left_mem_Icc.2 hx) (Set.right_mem_Icc.2 hx) hx

/-- A function that has the derivative `f' t` at every `t` of `[l, x]`, with `0 < f' t` for
`l < t < x`, is at `x` more than what it is at `l < x`. -/
theorem lt_of_deriv_pos {f f' : ℝ → ℝ} {l x : ℝ} (hx : l < x)
    (hd : ∀ t, l ≤ t → t ≤ x → HasDerivAt f (f' t) t)
    (hs : ∀ t, l < t → t < x → 0 < f' t) : f l < f x := by
  have hmono : StrictMonoOn f (Set.Icc l x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc l x)
      (fun t ht => (hd t ht.1 ht.2).continuousAt.continuousWithinAt) (fun t ht => ?_)
    rw [interior_Icc] at ht
    rw [(hd t ht.1.le ht.2.le).deriv]
    exact hs t ht.1 ht.2
  exact hmono (Set.left_mem_Icc.2 hx.le) (Set.right_mem_Icc.2 hx.le) hx

/-- A function that has the derivative `f' t` at every `t` of `[x, u]`, with `f' t ≤ 0` for
`x < t < u`, is at `x` at least what it is at `u`. -/
theorem le_of_deriv_nonpos {f f' : ℝ → ℝ} {u x : ℝ} (hx : x ≤ u)
    (hd : ∀ t, t ≤ u → x ≤ t → HasDerivAt f (f' t) t)
    (hs : ∀ t, t < u → x < t → f' t ≤ 0) : f u ≤ f x := by
  have h := le_of_deriv_nonneg (f := fun s => -f s) (f' := fun s => -f' s) hx
    (fun t h1 h2 => (hd t h2 h1).neg) (fun t h1 h2 => neg_nonneg.2 (hs t h2 h1))
  exact neg_le_neg_iff.1 h

/-- A function that has the derivative `f' t` at every `t` of `[x, u]`, with `f' t < 0` for
`x < t < u`, is at `x < u` more than what it is at `u`. -/
theorem lt_of_deriv_neg {f f' : ℝ → ℝ} {u x : ℝ} (hx : x < u)
    (hd : ∀ t, t ≤ u → x ≤ t → HasDerivAt f (f' t) t)
    (hs : ∀ t, t < u → x < t → f' t < 0) : f u < f x := by
  have h := lt_of_deriv_pos (f := fun s => -f s) (f' := fun s => -f' s) hx
    (fun t h1 h2 => (hd t h2 h1).neg) (fun t h1 h2 => neg_pos.2 (hs t h2 h1))
  exact neg_lt_neg_iff.1 h

/-- The chain rule for the hyperbolic tangent. -/
theorem hasDerivAt_tanh_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => Real.tanh (f y)) ((1 - Real.tanh (f x) ^ 2) * f') x :=
  (hasDerivAt_tanh (f x)).comp x hf

/-- The chain rule for the tangent, where the cosine of the argument does not vanish. -/
theorem hasDerivAt_tan_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hx : Real.cos (f x) ≠ 0) :
    HasDerivAt (fun y => Real.tan (f y)) (1 / Real.cos (f x) ^ 2 * f') x :=
  (Real.hasDerivAt_tan hx).comp x hf

end FloatLib.Numerics.Interval
