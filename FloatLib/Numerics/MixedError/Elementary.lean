/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.MixedError.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import FloatLib.Numerics.ErrorBound.Algebra
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Mixed error of exponentials and logarithms

The exponential turns an absolute error of its argument into a relative error of its value:
`|exp x - exp x₀| ≤ (exp |x - x₀| - 1) * exp x₀`. The logarithm does the converse at a positive
exact argument, turning a pure relative error `r < 1` into the absolute error `-log (1 - r)`. When
the computed and the exact argument are both nonnegative, `log (1 + x)` preserves a mixed error with
the same constants, and so does `exp x - 1` when both are nonpositive, where the relative condition
number of both functions is at most one.

Arguments of the other sign need a margin. Where `1 + x` and `1 + x₀` are at least `m > 0`,
`log (1 + x)` divides the propagated error by `m`, so a computed argument may fall below zero as
long as it stays above `-1`. On a neighbourhood `|x₀| ≤ c` of zero, `exp x - 1` multiplies the
relative error by `(1 + c) * exp (r * c + a)` and the absolute error by `exp (c + r * c + a)`. A
real power `x ^ b` of a positive base turns the errors of both arguments into a pure relative error,
through `exp (b * log (x / x₀) + (b - b₀) * log x₀)`. With an exact exponent the base may be
negative.

An implementation of one of these functions is described by a contract `MixedError y (f x) u η`: its
result `y` at the computed argument `x` has mixed error `(u, η)`. A correctly rounded result
satisfies it with the unit roundoff and the underflow allowance of its format.
`MixedError.trans_exp` and its siblings compose such a contract with the error of the argument.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- `exp x - 1 - x` is nonnegative. -/
theorem exp_sub_one_sub_nonneg (x : ℝ) : 0 ≤ Real.exp x - 1 - x :=
  sub_nonneg.mpr (le_sub_iff_add_le.mpr (Real.add_one_le_exp x))

/-- `exp x - 1 - x` is positive away from zero. -/
theorem exp_sub_one_sub_pos {x : ℝ} (hx : x ≠ 0) : 0 < Real.exp x - 1 - x :=
  sub_pos.mpr (lt_sub_iff_add_lt.mpr (Real.add_one_lt_exp hx))

/--
The exponential turns the distance between its arguments into a relative error:
`|exp x - exp x₀| ≤ (exp |x - x₀| - 1) * exp x₀`.
-/
theorem abs_exp_sub_exp_le (x x₀ : ℝ) :
    |Real.exp x - Real.exp x₀| ≤ (Real.exp |x - x₀| - 1) * Real.exp x₀ := by
  have hexp : Real.exp x = Real.exp x₀ * Real.exp (x - x₀) := by
    rw [← Real.exp_add, add_sub_cancel]
  rw [hexp, ← mul_sub_one, abs_mul, abs_of_pos (Real.exp_pos x₀), mul_comm]
  gcongr
  rcases le_total 0 (x - x₀) with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr h))]
  · rw [abs_of_nonpos h, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr h))]
    linarith [Real.add_one_le_exp (x - x₀), Real.add_one_le_exp (-(x - x₀))]

/-- The logarithm is `1 / m`-Lipschitz on `[m, ∞)` for `m > 0`. -/
theorem abs_log_sub_log_le {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m := by
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  rw [abs_sub_le_iff]
  constructor
  · calc Real.log x - Real.log y = Real.log (x / y) := (Real.log_div hx0.ne' hy0.ne').symm
      _ ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      _ = (x - y) / y := div_sub_one hy0.ne'
      _ ≤ |x - y| / m := div_le_div₀ (abs_nonneg _) (le_abs_self _) hm hy
  · calc Real.log y - Real.log x = Real.log (y / x) := (Real.log_div hy0.ne' hx0.ne').symm
      _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
      _ = (y - x) / x := div_sub_one hx0.ne'
      _ ≤ |x - y| / m := div_le_div₀ (abs_nonneg _) (abs_sub_comm x y ▸ le_abs_self _) hm hx

/-- `|exp t - 1| ≤ exp |t| - 1`. -/
theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) : |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  simpa using abs_exp_sub_exp_le t 0

/-- A value within relative distance `ρ < 1` of a nonzero `x₀` has a positive ratio to it, whose
logarithm has magnitude at most `-log (1 - ρ)`. -/
theorem abs_log_div_le {x x₀ ρ : ℝ} (hx₀ : x₀ ≠ 0) (hρ : ρ < 1) (h : |x - x₀| ≤ ρ * |x₀|) :
    0 < x / x₀ ∧ |Real.log (x / x₀)| ≤ -Real.log (1 - ρ) := by
  have hq : |x / x₀ - 1| ≤ ρ := by
    rw [← div_le_iff₀ (abs_pos.mpr hx₀), ← abs_div, sub_div, div_self hx₀] at h
    exact h
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans hq
  obtain ⟨upper, lower⟩ := abs_sub_le_iff.1 hq
  have hlo : 1 - ρ ≤ x / x₀ := sub_le_comm.mp lower
  have hhi : x / x₀ ≤ 1 + ρ := sub_le_iff_le_add'.mp upper
  have hm : 0 < 1 - ρ := sub_pos.mpr hρ
  have hp : 0 < 1 + ρ := add_pos_of_pos_of_nonneg zero_lt_one hρ0
  have hpos : 0 < x / x₀ := hm.trans_le hlo
  refine ⟨hpos, abs_le.2 ⟨?_, ?_⟩⟩
  · rw [neg_neg]
    exact Real.log_le_log hm hlo
  · calc Real.log (x / x₀) ≤ Real.log (1 + ρ) := Real.log_le_log hpos hhi
      _ ≤ -Real.log (1 - ρ) := by
        rw [le_neg_iff_add_nonpos_right, ← Real.log_mul hp.ne' hm.ne']
        apply Real.log_nonpos (mul_pos hp hm).le
        rw [← sq_sub_sq, one_pow]
        exact sub_le_self _ (sq_nonneg _)

namespace MixedError

variable {x x₀ y r a u η c m : ℝ}

/--
The exponential of an argument with error `(r, a)` has the pure relative error
`exp (r * |x₀| + a) - 1`, with absolute part zero.
-/
theorem exp (h : MixedError x x₀ r a) :
    MixedError (Real.exp x) (Real.exp x₀) (Real.exp (r * |x₀| + a) - 1) 0 := by
  refine ⟨sub_nonneg.mpr (Real.one_le_exp_iff.mpr
    (add_nonneg (mul_nonneg h.r_nonneg (abs_nonneg _)) h.a_nonneg)), le_rfl, ?_⟩
  rw [add_zero, abs_of_pos (Real.exp_pos x₀)]
  exact (abs_exp_sub_exp_le x x₀).trans (by gcongr; exact h.bound)

/--
The logarithm turns a pure relative error `r < 1` at a positive exact argument into the absolute
error `-log (1 - r)`.
-/
theorem log (h : MixedError x x₀ r 0) (hx₀ : 0 < x₀) (hr : r < 1) :
    MixedError (Real.log x) (Real.log x₀) 0 (-Real.log (1 - r)) := by
  obtain ⟨_, hlog⟩ := abs_log_div_le hx₀.ne' hr (by simpa using h.bound)
  have hx := h.pos_of_pos hr hx₀
  apply of_abs_sub_le
  rwa [Real.log_div hx.ne' hx₀.ne'] at hlog

/--
A function on `[0, ∞)` that vanishes at zero, is monotone with slope at most one, and satisfies
`c * f t ≤ f (c * t)` for `c ∈ [0, 1]`, as a concave function vanishing at zero does, keeps the
mixed error of a nonnegative argument.
-/
private theorem of_concave {f : ℝ → ℝ} (h0 : f 0 = 0)
    (hscale : ∀ c t, 0 ≤ c → c ≤ 1 → 0 ≤ t → c * f t ≤ f (c * t))
    (hmono : ∀ s t, 0 ≤ s → s ≤ t → f s ≤ f t)
    (hlip : ∀ s t, 0 ≤ s → s ≤ t → f t - f s ≤ t - s)
    (h : MixedError x x₀ r a) (hx₀ : 0 ≤ x₀) (hx : 0 ≤ x) : MixedError (f x) (f x₀) r a := by
  have hr := h.r_nonneg
  have ha := h.a_nonneg
  have hf₀ : 0 ≤ f x₀ := h0 ▸ hmono 0 x₀ le_rfl hx₀
  have hb := abs_le.1 (by simpa [abs_of_nonneg hx₀] using h.bound : |x - x₀| ≤ r * x₀ + a)
  refine ⟨hr, ha, ?_⟩
  rw [abs_of_nonneg hf₀, abs_le]
  constructor
  · -- Below `x₀`, compare with `(1 - r) * x₀`, where `f` has dropped by at most `r * f x₀`.
    rcases le_or_gt 1 r with hr1 | hr1
    · nlinarith [h0 ▸ hmono 0 x le_rfl hx]
    have hy : 0 ≤ (1 - r) * x₀ := mul_nonneg (by linarith) hx₀
    have hfy := hscale (1 - r) x₀ (by linarith) (by linarith) hx₀
    rcases le_total ((1 - r) * x₀) x with hyx | hxy
    · linarith [hmono _ x hy hyx]
    · linarith [hlip x _ hx hxy]
  · -- Above `x₀`, compare with `(1 + r) * x₀`, where `f` has grown by at most `r * f x₀`.
    have hy : 0 ≤ (1 + r) * x₀ := by positivity
    have hfy : f ((1 + r) * x₀) ≤ (1 + r) * f x₀ := by
      have := hscale (1 + r)⁻¹ ((1 + r) * x₀) (by positivity)
        (inv_le_one_of_one_le₀ (by linarith)) hy
      rwa [inv_mul_cancel_left₀ (by positivity), inv_mul_le_iff₀ (by positivity)] at this
    rcases le_total x ((1 + r) * x₀) with hxy | hyx
    · linarith [hmono x _ hx hxy]
    · linarith [hlip _ x hy hyx]

/-- When `x` and `x₀` are both nonnegative, `log (1 + x)` keeps the error `(r, a)` of `x`. -/
theorem log_one_add (h : MixedError x x₀ r a) (hx₀ : 0 ≤ x₀) (hx : 0 ≤ x) :
    MixedError (Real.log (1 + x)) (Real.log (1 + x₀)) r a := by
  refine of_concave (f := fun t => Real.log (1 + t)) (by simp) ?_ ?_ ?_ h hx₀ hx
  · intro c t hc hc1 ht
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 one_pos)
      (Set.mem_Ioi.2 (by linarith : (0 : ℝ) < 1 + t)) (by linarith : 0 ≤ 1 - c) hc
      (sub_add_cancel 1 c)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at this
    calc c * Real.log (1 + t) ≤ Real.log (1 - c + c * (1 + t)) := this
      _ = Real.log (1 + c * t) := by ring_nf
  · intro s t hs hst
    exact Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one hs)
      (add_le_add le_rfl hst)
  · intro s t hs hst
    rw [← Real.log_div (by linarith) (by positivity)]
    calc Real.log ((1 + t) / (1 + s)) ≤ (1 + t) / (1 + s) - 1 :=
          Real.log_le_sub_one_of_pos (div_pos (by linarith) (by positivity))
      _ = (t - s) / (1 + s) := by
        rw [div_sub_one (by positivity), add_sub_add_left_eq_sub]
      _ ≤ t - s := div_le_self (sub_nonneg.mpr hst) (le_add_of_nonneg_right hs)

/--
Where `1 + x` and `1 + x₀` are at least `m > 0`, `log (1 + x)` turns the error of an argument of
either sign into the absolute error `(r * |x₀| + a) / m`.
-/
theorem log_one_add_of_le (h : MixedError x x₀ r a) (hm : 0 < m) (hx : m ≤ 1 + x)
    (hx₀ : m ≤ 1 + x₀) :
    MixedError (Real.log (1 + x)) (Real.log (1 + x₀)) 0 ((r * |x₀| + a) / m) := by
  refine of_abs_sub_le ((abs_log_sub_log_le hm hx hx₀).trans ?_)
  rw [add_sub_add_left_eq_sub]
  gcongr
  exact h.bound

/-- When `x` and `x₀` are both nonpositive, `exp x - 1` keeps the error `(r, a)` of `x`. -/
theorem exp_sub_one (h : MixedError x x₀ r a) (hx₀ : x₀ ≤ 0) (hx : x ≤ 0) :
    MixedError (Real.exp x - 1) (Real.exp x₀ - 1) r a := by
  suffices MixedError (1 - Real.exp (- -x)) (1 - Real.exp (- -x₀)) r a by
    simpa only [neg_neg, neg_sub] using this.neg
  refine of_concave (f := fun t => 1 - Real.exp (-t)) (by simp) ?_ ?_ ?_ h.neg
    (neg_nonneg.2 hx₀) (neg_nonneg.2 hx)
  · intro c t hc hc1 _
    have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-t)) (by linarith : 0 ≤ 1 - c) hc
      (sub_add_cancel 1 c)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_neg] at this
    linarith
  · intro s t _ hst
    exact sub_le_sub_left (Real.exp_le_exp.2 (neg_le_neg hst)) 1
  · intro s t hs hst
    -- `exp (-s) - exp (-t) = exp (-s) * (1 - exp (-(t - s)))`, with both factors in `[0, 1]`.
    have hsplit : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]
      congr 1
      abel
    have hs1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.mpr hs)
    have hd1 : Real.exp (-(t - s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.mpr (sub_nonneg.mpr hst))
    calc
      _ = Real.exp (-s) * (1 - Real.exp (-(t - s))) := by
        rw [sub_sub_sub_cancel_left, hsplit, mul_sub, mul_one]
      _ ≤ 1 - Real.exp (-(t - s)) :=
        mul_le_of_le_one_left (sub_nonneg.mpr hd1) hs1
      _ ≤ t - s := sub_le_comm.mpr (Real.one_sub_le_exp_neg _)

/-- `exp x - 1 - x` moves with its argument by at most `(exp (|x₀| + e) - 1) * e`, where
`e = r * |x₀| + a` is the error of the argument: its derivative `exp t - 1` is at most
`exp |t| - 1` in magnitude. For a small argument this is about `|x₀| * e`, so the relative error
of the value, which is about `x₀ ^ 2 / 2`, is about twice that of the argument. -/
theorem exp_sub_one_sub (h : MixedError x x₀ r a) :
    MixedError (Real.exp x - 1 - x) (Real.exp x₀ - 1 - x₀) 0
      ((Real.exp (|x₀| + (r * |x₀| + a)) - 1) * (r * |x₀| + a)) := by
  have he : 0 ≤ r * |x₀| + a := add_nonneg (mul_nonneg h.r_nonneg (abs_nonneg _)) h.a_nonneg
  have hderiv : ∀ t, HasDerivAt (fun t => Real.exp t - 1 - t) (Real.exp t - 1) t := fun t =>
    ((Real.hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id t)
  have hslope : ∀ t ∈ Set.uIcc x₀ x, ‖deriv (fun t => Real.exp t - 1 - t) t‖ ≤
      Real.exp (|x₀| + (r * |x₀| + a)) - 1 := by
    intro t ht
    rw [(hderiv t).deriv, Real.norm_eq_abs]
    have hnear : |t| ≤ |x₀| + (r * |x₀| + a) :=
      (sub_le_iff_le_add'.mp (abs_sub_abs_le_abs_sub t x₀)).trans
        (add_le_add_right ((Set.abs_sub_left_of_mem_uIcc ht).trans h.bound) _)
    exact (abs_exp_sub_one_le_exp_abs_sub_one t).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hnear) 1)
  have hmean : |Real.exp x - 1 - x - (Real.exp x₀ - 1 - x₀)| ≤
      (Real.exp (|x₀| + (r * |x₀| + a)) - 1) * |x - x₀| :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hderiv t).differentiableAt) hslope (convex_uIcc x₀ x) Set.left_mem_uIcc
      Set.right_mem_uIcc
  exact of_abs_sub_le (hmean.trans (mul_le_mul_of_nonneg_left h.bound
    (sub_nonneg.mpr (Real.one_le_exp (add_nonneg (abs_nonneg _) he)))))

/-- On `|x₀| ≤ c`, the product `|x₀| * exp x₀` is at most `(1 + c) * |exp x₀ - 1|`. -/
private theorem abs_mul_exp_le (hc : |x₀| ≤ c) :
    |x₀| * Real.exp x₀ ≤ (1 + c) * |Real.exp x₀ - 1| := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hc
  have hexp := Real.exp_pos x₀
  rcases le_total 0 x₀ with hx₀ | hx₀
  · have hone := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx₀)
    rw [abs_of_nonneg hx₀] at hc ⊢
    rw [abs_of_nonneg hone]
    nlinarith [Real.add_one_le_exp x₀]
  · have hone := sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx₀)
    have hinv : Real.exp x₀ * Real.exp (-x₀) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [abs_of_nonpos hx₀, abs_of_nonpos hone]
    nlinarith [Real.add_one_le_exp (-x₀)]

/--
On a neighbourhood `|x₀| ≤ c` of zero, of either sign, `exp x - 1` has relative error
`(1 + c) * exp (r * c + a) * r` and absolute error `exp (c + r * c + a) * a`.
-/
theorem exp_sub_one_of_abs_le (h : MixedError x x₀ r a) (hc : |x₀| ≤ c) :
    MixedError (Real.exp x - 1) (Real.exp x₀ - 1) ((1 + c) * Real.exp (r * c + a) * r)
      (Real.exp (c + r * c + a) * a) := by
  have hr := h.r_nonneg
  have ha := h.a_nonneg
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hc
  have hE : r * |x₀| + a ≤ r * c + a := by gcongr
  have hgrowth : Real.exp (r * |x₀| + a) - 1 ≤ (r * |x₀| + a) * Real.exp (r * |x₀| + a) := by
    have h := mul_le_mul_of_nonneg_right
      (Real.one_sub_le_exp_neg (r * |x₀| + a)) (Real.exp_nonneg (r * |x₀| + a))
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    exact sub_le_comm.mp h
  refine ⟨by positivity, by positivity, ?_⟩
  rw [sub_sub_sub_cancel_right]
  calc |Real.exp x - Real.exp x₀|
      ≤ (Real.exp |x - x₀| - 1) * Real.exp x₀ := abs_exp_sub_exp_le x x₀
    _ ≤ (Real.exp (r * |x₀| + a) - 1) * Real.exp x₀ := by gcongr; exact h.bound
    _ ≤ (r * |x₀| + a) * Real.exp (r * c + a) * Real.exp x₀ := by
      gcongr ?_ * _
      exact hgrowth.trans (by gcongr)
    _ = Real.exp (r * c + a) * (r * (|x₀| * Real.exp x₀) + a * Real.exp x₀) := by
      rw [add_mul, add_mul, mul_add]
      ac_rfl
    _ ≤ Real.exp (r * c + a) * (r * ((1 + c) * |Real.exp x₀ - 1|) + a * Real.exp c) := by
      gcongr Real.exp (r * c + a) * (r * ?_ + a * ?_)
      · exact abs_mul_exp_le hc
      · exact Real.exp_le_exp.2 ((le_abs_self x₀).trans hc)
    _ = (1 + c) * Real.exp (r * c + a) * r * |Real.exp x₀ - 1| +
        Real.exp (c + r * c + a) * a := by
      rw [show Real.exp (c + r * c + a) = Real.exp c * Real.exp (r * c + a) by
        rw [← Real.exp_add, add_assoc]]
      rw [mul_add]; ac_rfl

/-! ### Composition with an implementation contract -/

/--
An exponential whose result `y` has mixed error `(u, η)` at the computed argument `x` has
relative error `(1 + u) * exp (r * |x₀| + a) - 1` and absolute error `η` at the exact argument.
-/
theorem trans_exp (hf : MixedError y (Real.exp x) u η) (h : MixedError x x₀ r a) :
    MixedError y (Real.exp x₀) ((1 + u) * Real.exp (r * |x₀| + a) - 1) η :=
  (hf.trans h.exp).mono (le_of_eq (by ring)) (le_of_eq (by simp))

/--
A logarithm whose result `y` has mixed error `(u, η)` at a computed argument with pure relative
error `r < 1` from a positive exact argument has relative error `u` and absolute error
`(1 + u) * -log (1 - r) + η`.
-/
theorem trans_log (hf : MixedError y (Real.log x) u η) (h : MixedError x x₀ r 0)
    (hx₀ : 0 < x₀) (hr : r < 1) :
    MixedError y (Real.log x₀) u ((1 + u) * -Real.log (1 - r) + η) := by
  exact hf.trans_of_abs_sub_le (by simpa only [zero_mul, zero_add] using (h.log hx₀ hr).bound)

/--
A `log (1 + x)` implementation with mixed error `(u, η)` at a computed argument with error
`(r, a)`, where the computed and the exact argument are both nonnegative, has relative error
`(1 + u) * r + u` and absolute error `(1 + u) * a + η` at the exact argument.
-/
theorem trans_log_one_add (hf : MixedError y (Real.log (1 + x)) u η) (h : MixedError x x₀ r a)
    (hx₀ : 0 ≤ x₀) (hx : 0 ≤ x) :
    MixedError y (Real.log (1 + x₀)) ((1 + u) * r + u) ((1 + u) * a + η) :=
  hf.trans (h.log_one_add hx₀ hx)

/--
An `exp x - 1` implementation with mixed error `(u, η)` at a computed argument with error
`(r, a)`, where the computed and the exact argument are both nonpositive, has relative error
`(1 + u) * r + u` and absolute error `(1 + u) * a + η` at the exact argument.
-/
theorem trans_exp_sub_one (hf : MixedError y (Real.exp x - 1) u η) (h : MixedError x x₀ r a)
    (hx₀ : x₀ ≤ 0) (hx : x ≤ 0) :
    MixedError y (Real.exp x₀ - 1) ((1 + u) * r + u) ((1 + u) * a + η) :=
  hf.trans (h.exp_sub_one hx₀ hx)

/--
A `log (1 + x)` implementation with mixed error `(u, η)`, at a computed argument of either sign
with error `(r, a)` where `1 + x` and `1 + x₀` are at least `m > 0`, has relative error `u` and
absolute error `(1 + u) * ((r * |x₀| + a) / m) + η` at the exact argument.
-/
theorem trans_log_one_add_of_le (hf : MixedError y (Real.log (1 + x)) u η)
    (h : MixedError x x₀ r a) (hm : 0 < m) (hx : m ≤ 1 + x) (hx₀ : m ≤ 1 + x₀) :
    MixedError y (Real.log (1 + x₀)) u ((1 + u) * ((r * |x₀| + a) / m) + η) := by
  exact hf.trans_of_abs_sub_le (by
    simpa only [zero_mul, zero_add] using (h.log_one_add_of_le hm hx hx₀).bound)

/--
An `exp x - 1` implementation with mixed error `(u, η)`, at a computed argument with error `(r, a)`
whose exact value satisfies `|x₀| ≤ c`, has relative error
`(1 + u) * ((1 + c) * exp (r * c + a) * r) + u` and absolute error
`(1 + u) * (exp (c + r * c + a) * a) + η` at the exact argument.
-/
theorem trans_exp_sub_one_of_abs_le (hf : MixedError y (Real.exp x - 1) u η)
    (h : MixedError x x₀ r a) (hc : |x₀| ≤ c) :
    MixedError y (Real.exp x₀ - 1) ((1 + u) * ((1 + c) * Real.exp (r * c + a) * r) + u)
      ((1 + u) * (Real.exp (c + r * c + a) * a) + η) :=
  hf.trans (h.exp_sub_one_of_abs_le hc)

/-- A real power whose positive exact base and exponent `b₀` have computed values with mixed
errors `(r, a)` and `(s, e)` has a pure relative error, when the base's relative distance
`ρ = r + a / x₀` is below one. -/
theorem rpow {b b₀ s e : ℝ} (h : MixedError x x₀ r a) (hb : MixedError b b₀ s e) (hx₀ : 0 < x₀)
    (hsmall : r + a / x₀ < 1) :
    MixedError (x ^ b) (x₀ ^ b₀) (Real.exp (((1 + s) * |b₀| + e) * -Real.log (1 - (r + a / x₀)) +
      (s * |b₀| + e) * |Real.log x₀|) - 1) 0 := by
  have hrelative := h.relative_of_le_abs hx₀ (le_abs_self _)
  obtain ⟨_, hlog⟩ := abs_log_div_le hx₀.ne' hsmall
    (by simpa only [add_zero] using hrelative.bound)
  have hx := hrelative.pos_of_pos hsmall hx₀
  have hexponent := hb.abs_le
  have hpower : x ^ b = x₀ ^ b₀ *
      Real.exp (b * Real.log (x / x₀) + (b - b₀) * Real.log x₀) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx₀, ← Real.exp_add,
      Real.log_div hx.ne' hx₀.ne']
    ring_nf
  have hpos := Real.rpow_pos_of_pos hx₀ b₀
  have hexp : |b * Real.log (x / x₀) + (b - b₀) * Real.log x₀| ≤
      ((1 + s) * |b₀| + e) * -Real.log (1 - (r + a / x₀)) + (s * |b₀| + e) * |Real.log x₀| :=
    Backward.abs_add_le_add (Backward.abs_mul_le_mul hexponent hlog)
      (Backward.abs_mul_le_mul hb.bound le_rfl)
  refine ⟨?_, le_rfl, ?_⟩
  · exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr ((abs_nonneg _).trans hexp))
  · rw [add_zero, abs_of_pos hpos, hpower, ← mul_sub_one, abs_mul, abs_of_pos hpos, mul_comm]
    gcongr
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans (by gcongr)

/--
A real power with an exact exponent of a nonzero base whose computed value has mixed error `(r, a)`
has a pure relative error, when the relative distance `ρ = r + a / |x₀|` is below one. The base may
be negative.
-/
theorem rpow_const {b b₀ : ℝ} (h : MixedError x x₀ r a) (hb : MixedError b b₀ 0 0)
    (hx₀ : x₀ ≠ 0) (hsmall : r + a / |x₀| < 1) :
    MixedError (x ^ b) (x₀ ^ b₀) (Real.exp (|b₀| * -Real.log (1 - (r + a / |x₀|))) - 1) 0 := by
  obtain rfl : b = b₀ := mixedError_zero_zero_iff.mp hb
  have hrelative := h.relative_of_le_abs (abs_pos.mpr hx₀) le_rfl
  obtain ⟨_, hlog⟩ := abs_log_div_le hx₀ hsmall
    (by simpa only [add_zero] using hrelative.bound)
  have hpower : x ^ b = x₀ ^ b * Real.exp (b * Real.log (x / x₀)) := by
    rcases lt_or_gt_of_ne hx₀ with hneg | hpos'
    · have hxneg := hrelative.lt_zero_of_lt_zero hsmall hneg
      rw [Real.rpow_def_of_neg hxneg, Real.rpow_def_of_neg hneg, mul_right_comm, ← Real.exp_add,
        Real.log_div hxneg.ne hneg.ne]
      congr 2
      rw [mul_comm b, ← add_mul, add_sub_cancel]
    · have hxpos := hrelative.pos_of_pos hsmall hpos'
      rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hpos', ← Real.exp_add,
        Real.log_div hxpos.ne' hpos'.ne']
      congr 1
      rw [mul_comm b, ← add_mul, add_sub_cancel]
  have hlog₀ : 0 ≤ -Real.log (1 - (r + a / |x₀|)) := (abs_nonneg _).trans hlog
  refine ⟨?_, le_rfl, ?_⟩
  · exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg (abs_nonneg b) hlog₀))
  · rw [add_zero, hpower, ← mul_sub_one, abs_mul, mul_comm]
    gcongr
    refine (abs_exp_sub_one_le_exp_abs_sub_one _).trans ?_
    rw [abs_mul]
    gcongr

end MixedError

/-- `exp x - 1 - x` at a value within `A` of its reference `R` is within
`(exp (|R| + A) - 1) * A` of its value at `R`: it moves by its derivative, and not by the
changes of its three terms. -/
theorem Backward.deviation_exp_sub_one_sub {x R A : ℝ} (hx : |x - R| ≤ A) :
    |Real.exp x - 1 - x - (Real.exp R - 1 - R)| ≤ (Real.exp (|R| + A) - 1) * A := by
  simpa using (MixedError.exp_sub_one_sub (MixedError.of_abs_sub_le hx)).bound

end FloatLib.Numerics
