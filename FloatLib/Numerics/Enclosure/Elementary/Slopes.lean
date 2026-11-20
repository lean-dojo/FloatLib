/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Bounded slopes of elementary functions at zero

An odd function between `u - u ^ 3 / d` and `u` on the nonnegative half-line has the
representation `u - u ^ 3 * r` at every real argument, with `0 ≤ r ≤ 1 / d`.
`exists_eq_sub_cube` proves this once. Sine, hyperbolic tangent and arctangent are
instances; cosine has the analogous quadratic representation.

The witnesses depend on the argument. Replacing a function value by its representation
and retaining the witness bounds gives polynomial constraints, including at the origin
where direct interval evaluation cannot separate an expression from zero.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- The derivative of `x - x ^ 3 / 3`. -/
private theorem hasDerivAt_sub_cube (x : ℝ) :
    HasDerivAt (fun x : ℝ => x - x ^ 3 / 3) (1 - x ^ 2) x := by
  have h : HasDerivAt (fun x : ℝ => x - x ^ 3 / 3) (1 - ((3 : ℕ) : ℝ) * x ^ (3 - 1) / 3) x :=
    (hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 3)
  refine h.congr_deriv ?_
  norm_num

/-- For `0 ≤ u`, the arctangent is at least `u - u ^ 3 / 3`. -/
theorem sub_cube_le_arctan {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 / 3 ≤ Real.arctan u := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.arctan x - (x - x ^ 3 / 3))
      (1 / (1 + x ^ 2) - (1 - x ^ 2)) x :=
    fun x => (Real.hasDerivAt_arctan x).sub (hasDerivAt_sub_cube x)
  have hmono : MonotoneOn (fun x => Real.arctan x - (x - x ^ 3 / 3)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) fun x _ => ?_
    rw [(hderiv x).deriv, sub_nonneg, le_div_iff₀ (by positivity)]
    linarith [sq_nonneg (x ^ 2)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simpa using h

/-- The derivative of the hyperbolic tangent at `x` is `1 - Real.tanh x ^ 2`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  refine (h.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => Real.tanh_eq_sinh_div_cosh y)
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- For `0 ≤ u`, the hyperbolic tangent is at most `u`. -/
theorem tanh_le_self {u : ℝ} (hu : 0 ≤ u) : Real.tanh u ≤ u := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => x - Real.tanh x) (1 - (1 - Real.tanh x ^ 2)) x :=
    fun x => (hasDerivAt_id' x).sub (hasDerivAt_tanh x)
  have hmono : MonotoneOn (fun x => x - Real.tanh x) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) fun x _ => ?_
    rw [(hderiv x).deriv, sub_sub_cancel]
    exact sq_nonneg (Real.tanh x)
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simpa using h

/-- For `0 ≤ u`, the hyperbolic tangent is at least `u - u ^ 3 / 3`. -/
theorem sub_cube_le_tanh {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 / 3 ≤ Real.tanh u := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.tanh x - (x - x ^ 3 / 3))
      (1 - Real.tanh x ^ 2 - (1 - x ^ 2)) x :=
    fun x => (hasDerivAt_tanh x).sub (hasDerivAt_sub_cube x)
  have hmono : MonotoneOn (fun x => Real.tanh x - (x - x ^ 3 / 3)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hderiv x).deriv]
    have hx0 : 0 ≤ x := by
      rw [interior_Ici] at hx
      exact (Set.mem_Ioi.1 hx).le
    have h1 := tanh_le_self hx0
    have h2 : 0 ≤ Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.2 hx0) (Real.cosh_pos x).le
    exact sub_nonneg.2 (sub_le_sub_left ((sq_le_sq₀ h2 hx0).2 h1) 1)
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simpa using h

/-- An odd function that lies between `u - u ^ 3 / d` and `u` for `0 ≤ u`, with `0 < d`, is at
every `u` its argument minus the cube of its argument times a slope between `0` and `1 / d`. -/
theorem exists_eq_sub_cube {f : ℝ → ℝ} {d : ℝ} (hd : 0 < d) (hodd : ∀ u, f (-u) = -f u)
    (hle : ∀ u, 0 ≤ u → f u ≤ u) (hge : ∀ u, 0 ≤ u → u - u ^ 3 / d ≤ f u) (u : ℝ) :
    ∃ r : ℝ, f u = u - u ^ 3 * r ∧ 0 ≤ r ∧ r ≤ 1 / d := by
  have key : ∀ v : ℝ, v ≠ 0 → 0 ≤ v → f v = v - v ^ 3 * ((v - f v) / v ^ 3) ∧
      0 ≤ (v - f v) / v ^ 3 ∧ (v - f v) / v ^ 3 ≤ 1 / d := by
    intro v hne hv
    have hcube : 0 < v ^ 3 := pow_pos (lt_of_le_of_ne hv (Ne.symm hne)) 3
    refine ⟨by rw [mul_div_cancel₀ _ hcube.ne']; ring,
      div_nonneg (sub_nonneg.2 (hle v hv)) hcube.le, ?_⟩
    rw [div_le_iff₀ hcube, one_div, inv_mul_eq_div]
    exact sub_le_comm.1 (hge v hv)
  rcases lt_trichotomy u 0 with hu | hu | hu
  · obtain ⟨_, h0, h1⟩ := key (-u) (neg_ne_zero.2 hu.ne) (neg_nonneg.2 hu.le)
    have hflip : (-u - f (-u)) / (-u) ^ 3 = (u - f u) / u ^ 3 := by
      rw [hodd, Odd.neg_pow (by decide), neg_sub_neg, ← neg_sub u, neg_div_neg_eq]
    rw [hflip] at h0 h1
    refine ⟨(u - f u) / u ^ 3, ?_, h0, h1⟩
    rw [mul_div_cancel₀ _ (pow_ne_zero 3 hu.ne)]
    ring
  · have hzero : f 0 = 0 := by
      have h := hodd 0
      rw [neg_zero] at h
      exact self_eq_neg.1 h
    exact ⟨0, by rw [hu, hzero]; ring, le_refl 0, (one_div_pos.2 hd).le⟩
  · exact ⟨(u - f u) / u ^ 3, key u hu.ne' hu.le⟩

/-- The sine is its argument minus the cube of its argument times a slope between `0` and
`1 / 6`. -/
theorem exists_sin_eq_sub (u : ℝ) :
    ∃ r : ℝ, Real.sin u = u - u ^ 3 * r ∧ 0 ≤ r ∧ r ≤ 1 / 6 :=
  exists_eq_sub_cube (by norm_num) Real.sin_neg (fun _ => Real.sin_le)
    (fun _ => Real.sin_ge_sub_cube) u

/-- The hyperbolic tangent is its argument minus the cube of its argument times a slope between
`0` and `1 / 3`. -/
theorem exists_tanh_eq_sub (u : ℝ) :
    ∃ r : ℝ, Real.tanh u = u - u ^ 3 * r ∧ 0 ≤ r ∧ r ≤ 1 / 3 :=
  exists_eq_sub_cube (by norm_num) Real.tanh_neg (fun _ => tanh_le_self)
    (fun _ => sub_cube_le_tanh) u

/-- The arctangent is its argument minus the cube of its argument times a slope between `0` and
`1 / 3`. -/
theorem exists_arctan_eq_sub (u : ℝ) :
    ∃ r : ℝ, Real.arctan u = u - u ^ 3 * r ∧ 0 ≤ r ∧ r ≤ 1 / 3 :=
  exists_eq_sub_cube (by norm_num) Real.arctan_neg (fun _ => Real.arctan_le_self)
    (fun _ => sub_cube_le_arctan) u

/-- The cosine is one minus the square of its argument times a slope between `0` and `1 / 2`. -/
theorem exists_cos_eq_sub (u : ℝ) :
    ∃ c : ℝ, Real.cos u = 1 - u ^ 2 * c ∧ 0 ≤ c ∧ c ≤ 1 / 2 := by
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu], le_refl 0, by norm_num⟩
  · have hpos : 0 < u ^ 2 := by positivity
    refine ⟨(1 - Real.cos u) / u ^ 2, by field_simp; ring, ?_, ?_⟩
    · exact div_nonneg (sub_nonneg.2 (Real.cos_le_one u)) hpos.le
    · rw [div_le_iff₀ hpos]
      linarith [Real.one_sub_sq_div_two_le_cos (x := u)]

end FloatLib.Numerics.Interval

end
