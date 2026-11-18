/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Tanh.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import FloatLib.Numerics.Enclosure.Comparison.Cache

/-!
# Total comparators for the hyperbolic tangent of a complex rational

For a rational `a ≠ 0` and `b`, `compareRe` and `compareIm` order the real and imaginary parts of
`tanh (a + i b)`,

`sinh 2a / (cosh 2a + cos 2b)` and `sin 2b / (cosh 2a + cos 2b)`,

against any rational, for a positive `a` (`compareRe_eq_real`, `compareIm_eq_real`). They decide
the sign of the numerators of `Tanh.Sequences`, which involve `exp (-2a)` and `exp (-4a)` only,
so a huge `a` costs no more than a moderate one. The comparison of the real part with one, whose
numerator degenerates, is the sign of `exp (-2a) + cos 2b`.
-/

@[expose] public section

namespace FloatLib.Numerics.TanhComparison

open RationalInterval ProductComparison Enclosure.Comparison

/-- The real part of `tanh (a + i b)`. -/
noncomputable def re (a b : ℝ) : ℝ :=
  Real.sinh (2 * a) / (Real.cosh (2 * a) + Real.cos (2 * b))

/-- The imaginary part of `tanh (a + i b)`. -/
noncomputable def im (a b : ℝ) : ℝ :=
  Real.sin (2 * b) / (Real.cosh (2 * a) + Real.cos (2 * b))

/--
Compare the real part of `tanh (a + i b)` with a rational boundary, for a positive `a`. The
first `levels` enclosures of each exponential and of the cosine are shared across boundaries.
-/
def compareRe (a b : ℚ) (levels : Nat) (ha : a ≠ 0) : ℚ → Ordering :=
  let u := cacheIntervals (expLadder (-(2 * a))) levels
  let v := cacheIntervals (expLadder (-(4 * a))) levels
  let cosine := cacheIntervals (Trig.cos.intervals (2 * b)) levels
  fun boundary =>
    if hpositive : boundary ≤ 0 then .gt
    else if boundary = 1 then
      (compare (fun n => unitInterval (u.get n) (cosine.get n)) 0 (by
        simpa only [u, cosine, cacheIntervals_apply] using
          (converges_unitInterval a b).exists_separates
            (by simpa using exp_neg_add_cos_ne_zero (b := b) ha))).swap
    else
      have hne : boundary ≠ -1 := fun h => hpositive (by rw [h]; norm_num)
      compare (fun n => reInterval (u.get n) (v.get n) (cosine.get n) boundary) 0 (by
        simpa only [u, v, cosine, cacheIntervals_apply] using
          (converges_reInterval a b boundary).exists_separates
            (by simpa using reNumerator_ne_zero (b := b) ha hne))

/--
Compare the imaginary part of `tanh (a + i b)` with a rational boundary, for a positive `a`. The
comparison with zero is the sign of `sin 2b`.
-/
def compareIm (a b : ℚ) (levels : Nat) (ha : a ≠ 0) : ℚ → Ordering :=
  let u := cacheIntervals (expLadder (-(2 * a))) levels
  let v := cacheIntervals (expLadder (-(4 * a))) levels
  let sine := cacheIntervals (Trig.sin.intervals (2 * b)) levels
  let cosine := cacheIntervals (Trig.cos.intervals (2 * b)) levels
  fun boundary =>
    if hzero : boundary = 0 then
      if hb : b = 0 then .eq
      else
        compare (fun n => sine.get n) 0 (by
          simpa only [sine, cacheIntervals_apply] using
            (Trig.converges_intervals .sin (2 * b)).exists_separates
              (by simpa [Trig.eval] using
                (Enclosure.irrational_sin_ratCast (2 * b) (mul_ne_zero two_ne_zero hb)).ne_zero))
    else
      compare (fun n => imInterval (u.get n) (v.get n) (sine.get n) (cosine.get n) boundary) 0
        (by
          simpa only [u, v, sine, cosine, cacheIntervals_apply] using
            (converges_imInterval a b boundary).exists_separates
              (by simpa using imNumerator_ne_zero (b := b) ha hzero))

/-- A quotient by a positive denominator is ordered as a positive multiple of the difference. -/
theorem cmp_div_eq_cmp_mul_sub {X D k : ℝ} (hD : 0 < D) (hk : 0 < k) (t : ℝ) :
    cmp (X / D) t = cmp (k * (X - t * D)) 0 := by
  have hlt : X / D < t ↔ k * (X - t * D) < 0 := by
    rw [div_lt_iff₀ hD, show k * (X - t * D) = -(k * (t * D - X)) by ring, neg_lt_zero,
      mul_pos_iff_of_pos_left hk, sub_pos]
  have hgt : t < X / D ↔ 0 < k * (X - t * D) := by
    rw [lt_div_iff₀ hD, mul_pos_iff_of_pos_left hk, sub_pos]
  simp only [cmp, cmpUsing, hlt, hgt]

/-- The denominator `cosh 2a + cos 2b` is positive for a nonzero `a`. -/
theorem denominator_pos {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    0 < Real.cosh (2 * a) + Real.cos (2 * b) := by
  have hcosh : 1 < Real.cosh (2 * a) := Real.one_lt_cosh.mpr (mul_ne_zero two_ne_zero ha)
  linarith [Real.neg_one_le_cos (2 * b)]

private theorem two_exp_neg_mul_sinh (a : ℝ) :
    2 * Real.exp (-(2 * a)) * Real.sinh (2 * a) = 1 - Real.exp (-(4 * a)) := by
  rw [Real.sinh_eq, show -(4 * a) = -(2 * a) + -(2 * a) by ring, Real.exp_add]
  have h : Real.exp (-(2 * a)) * Real.exp (2 * a) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination h

private theorem two_exp_neg_mul_cosh (a : ℝ) :
    2 * Real.exp (-(2 * a)) * Real.cosh (2 * a) = 1 + Real.exp (-(4 * a)) := by
  rw [Real.cosh_eq, show -(4 * a) = -(2 * a) + -(2 * a) by ring, Real.exp_add]
  have h : Real.exp (-(2 * a)) * Real.exp (2 * a) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination h

private theorem exp_neg_two_mul_sq (a : ℝ) :
    Real.exp (-(2 * a)) ^ 2 = Real.exp (-(4 * a)) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/--
The real part of `tanh (a + i b)` in terms of `u = exp (-2a)`:
`(1 - u) (1 + u) / ((1 - u)² + 4 u cos² b)`. For a positive `a` no term of it cancels.
-/
theorem re_eq_decay (a b : ℝ) :
    re a b = (1 - Real.exp (-(2 * a))) * (1 + Real.exp (-(2 * a))) /
      ((1 - Real.exp (-(2 * a))) * (1 - Real.exp (-(2 * a))) +
        4 * Real.exp (-(2 * a)) * (Real.cos b * Real.cos b)) := by
  have hu : 2 * Real.exp (-(2 * a)) ≠ 0 := by positivity
  have hsum : re a b = (1 - Real.exp (-(4 * a))) /
      (1 + Real.exp (-(4 * a)) + 2 * Real.exp (-(2 * a)) * Real.cos (2 * b)) := by
    rw [re, ← mul_div_mul_left _ _ hu, two_exp_neg_mul_sinh, mul_add, two_exp_neg_mul_cosh]
  rw [hsum, ← exp_neg_two_mul_sq, Real.cos_two_mul]
  congr 1 <;> ring

/--
The imaginary part of `tanh (a + i b)` in terms of `u = exp (-2a)`:
`4 u sin b cos b / ((1 - u)² + 4 u cos² b)`. For a positive `a` no term of it cancels.
-/
theorem im_eq_decay (a b : ℝ) :
    im a b = 4 * Real.exp (-(2 * a)) * (Real.sin b * Real.cos b) /
      ((1 - Real.exp (-(2 * a))) * (1 - Real.exp (-(2 * a))) +
        4 * Real.exp (-(2 * a)) * (Real.cos b * Real.cos b)) := by
  have hu : 2 * Real.exp (-(2 * a)) ≠ 0 := by positivity
  have hsum : im a b = 2 * Real.exp (-(2 * a)) * Real.sin (2 * b) /
      (1 + Real.exp (-(4 * a)) + 2 * Real.exp (-(2 * a)) * Real.cos (2 * b)) := by
    rw [im, ← mul_div_mul_left _ _ hu, mul_add, two_exp_neg_mul_cosh]
  rw [hsum, ← exp_neg_two_mul_sq, Real.cos_two_mul, Real.sin_two_mul]
  congr 1 <;> ring

/-- `compareRe` orders the real part of `tanh (a + i b)` against every rational boundary. -/
theorem compareRe_eq_real (a b : ℚ) (levels : Nat) (ha : 0 < a) (boundary : ℚ) :
    compareRe a b levels ha.ne' boundary = cmp (re a b) (boundary : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hD := denominator_pos haR.ne' (b : ℝ)
  have hsinh : 0 < Real.sinh (2 * (a : ℝ)) := Real.sinh_pos_iff.mpr (by linarith)
  unfold compareRe
  split
  · rename_i hnonpos
    have hb : (boundary : ℝ) ≤ 0 := by exact_mod_cast hnonpos
    exact ((cmp_eq_gt_iff _ _).mpr (hb.trans_lt (div_pos hsinh hD))).symm
  · split
    · rename_i hone
      rw [Converges.compare_eq (by
        simpa only [cacheIntervals_apply] using converges_unitInterval a b), hone, cmp_swap]
      have hlt : re a b < 1 ↔ 0 < Real.exp (-(2 * (a : ℝ))) + Real.cos (2 * (b : ℝ)) := by
        rw [re, div_lt_one hD, ← Real.cosh_sub_sinh]
        constructor <;> intro h <;> linarith
      have hgt : 1 < re a b ↔ Real.exp (-(2 * (a : ℝ))) + Real.cos (2 * (b : ℝ)) < 0 := by
        rw [re, one_lt_div hD, ← Real.cosh_sub_sinh]
        constructor <;> intro h <;> linarith
      push_cast
      simp only [cmp, cmpUsing, hlt, hgt]
    · rw [Converges.compare_eq (by
        simpa only [cacheIntervals_apply] using converges_reInterval a b boundary)]
      have hnum : reNumerator a b boundary = 2 * Real.exp (-(2 * (a : ℝ))) *
          (Real.sinh (2 * (a : ℝ)) -
            boundary * (Real.cosh (2 * (a : ℝ)) + Real.cos (2 * (b : ℝ)))) := by
        rw [reNumerator]
        linear_combination -two_exp_neg_mul_sinh (a : ℝ) +
          (boundary : ℝ) * two_exp_neg_mul_cosh (a : ℝ)
      rw [hnum, re,
        cmp_div_eq_cmp_mul_sub (k := 2 * Real.exp (-(2 * (a : ℝ)))) hD (by positivity)]
      simp

/-- `compareIm` orders the imaginary part of `tanh (a + i b)` against every rational boundary. -/
theorem compareIm_eq_real (a b : ℚ) (levels : Nat) (ha : 0 < a) (boundary : ℚ) :
    compareIm a b levels ha.ne' boundary = cmp (im a b) (boundary : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hD := denominator_pos haR.ne' (b : ℝ)
  unfold compareIm
  split
  · rename_i hzero
    have hlt : im a b < 0 ↔ Real.sin (2 * (b : ℝ)) < 0 := by
      rw [im, div_neg_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact absurd h (not_lt.mpr hD.le)
        · exact h
      · exact fun h => Or.inr ⟨h, hD⟩
    have hgt : 0 < im a b ↔ 0 < Real.sin (2 * (b : ℝ)) := by
      rw [im, div_pos_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact h
        · exact absurd h (not_lt.mpr hD.le)
      · exact fun h => Or.inl ⟨h, hD⟩
    rw [hzero]
    split
    · rename_i hb
      have hsin : Real.sin (2 * (b : ℝ)) = 0 := by rw [hb]; simp
      simp [cmp, cmpUsing, hlt, hgt, hsin]
    · rw [Converges.compare_eq (by
        simpa only [cacheIntervals_apply] using Trig.converges_intervals .sin (2 * b))]
      push_cast
      simp only [Trig.eval, cmp, cmpUsing, hlt, hgt]
      rfl
  · rw [Converges.compare_eq (by
      simpa only [cacheIntervals_apply] using converges_imInterval a b boundary)]
    have hnum : imNumerator a b boundary = 2 * Real.exp (-(2 * (a : ℝ))) *
        (Real.sin (2 * (b : ℝ)) -
          boundary * (Real.cosh (2 * (a : ℝ)) + Real.cos (2 * (b : ℝ)))) := by
      rw [imNumerator]
      linear_combination (boundary : ℝ) * two_exp_neg_mul_cosh (a : ℝ)
    rw [hnum, im, cmp_div_eq_cmp_mul_sub (k := 2 * Real.exp (-(2 * (a : ℝ)))) hD (by positivity)]
    simp

end FloatLib.Numerics.TanhComparison
