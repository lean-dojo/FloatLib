/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.ComplexTranscendental
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Basic.Complex.BigOperators

/-!
# Real exponential sums at rational arguments are not nonzero rationals

The real and imaginary parts of the complex exponential, the hyperbolic and the trigonometric
functions at a complex rational are sums of terms `exp a * (c * cos b + d * sin b)` with rational
`a`, `b`, `c` and `d`. Such a sum never equals a nonzero rational when no term has `a = b = 0`:
each term is half of `(c - i d) exp (a + i b)` plus its conjugate, so the equation is a relation
among exponentials at nonzero Gaussian rationals with a nonzero constant, which
`gaussianInt_add_sum_exp_div_ne_zero` excludes.

So a correctly rounded complex function never meets a rounding boundary at these parts, except
where a part is exactly zero, and the exact comparisons behind the rounding terminate.
-/

public section

namespace FloatLib.Numerics.Enclosure

open scoped BigOperators

/--
A sum of terms `exp (P / D) * (c * cos (Q / D) + d * sin (Q / D))` with integer `P`, `Q`, `c`, `d`
and no term with `P = Q = 0` is not a nonzero integer.
-/
theorem sum_exp_mul_trig_ne_intCast {ι : Type*} (s : Finset ι) (D : ℕ) (hD : 0 < D)
    (P Q : ι → ℤ) (hPQ : ∀ k ∈ s, ¬(P k = 0 ∧ Q k = 0)) (c d : ι → ℤ) (r : ℤ) (hr : r ≠ 0) :
    ∑ k ∈ s, Real.exp ((P k : ℝ) / D) *
      ((c k : ℝ) * Real.cos ((Q k : ℝ) / D) + (d k : ℝ) * Real.sin ((Q k : ℝ) / D)) ≠ (r : ℝ) := by
  intro h
  have hterm (k : ι) :
      GaussianInt.toComplex ⟨c k, -d k⟩ *
          Complex.exp (GaussianInt.toComplex ⟨P k, Q k⟩ / D) +
        GaussianInt.toComplex ⟨c k, d k⟩ *
          Complex.exp (GaussianInt.toComplex ⟨P k, -Q k⟩ / D) =
      ((2 * (Real.exp ((P k : ℝ) / D) * ((c k : ℝ) * Real.cos ((Q k : ℝ) / D) +
        (d k : ℝ) * Real.sin ((Q k : ℝ) / D))) : ℝ) : ℂ) := by
    have h1 : GaussianInt.toComplex ⟨P k, Q k⟩ / (D : ℂ) =
        (((P k : ℝ) / D : ℝ) : ℂ) + (((Q k : ℝ) / D : ℝ) : ℂ) * Complex.I := by
      rw [GaussianInt.toComplex_def']
      push_cast
      ring
    have h2 : GaussianInt.toComplex ⟨P k, -Q k⟩ / (D : ℂ) =
        (((P k : ℝ) / D : ℝ) : ℂ) + ((-((Q k : ℝ) / D) : ℝ) : ℂ) * Complex.I := by
      rw [GaussianInt.toComplex_def']
      push_cast
      ring
    rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
      GaussianInt.toComplex_def', GaussianInt.toComplex_def', ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    apply Complex.ext <;> simp <;> ring
  refine gaussianInt_add_sum_exp_div_ne_zero (s.disjSum s) D hD
    (Sum.elim (fun k => ⟨P k, Q k⟩) (fun k => ⟨P k, -Q k⟩)) ?_
    (Sum.elim (fun k => ⟨c k, -d k⟩) (fun k => ⟨c k, d k⟩)) ⟨-2 * r, 0⟩ ?_ ?_
  · intro k hk
    rcases Finset.mem_disjSum.mp hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact fun hzero => hPQ j hj ⟨congrArg Zsqrtd.re hzero, congrArg Zsqrtd.im hzero⟩
    · exact fun hzero => hPQ j hj
        ⟨congrArg Zsqrtd.re hzero, by simpa using congrArg Zsqrtd.im hzero⟩
  · exact fun hzero => hr (by simpa using congrArg Zsqrtd.re hzero)
  · rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun k _ => hterm k, ← Complex.ofReal_sum,
      ← Finset.mul_sum, h, GaussianInt.toComplex_def']
    push_cast
    ring

/--
A sum of terms `exp a * (c * cos b + d * sin b)` with rational `a`, `b`, `c`, `d` and no term with
`a = b = 0` is not a nonzero rational.
-/
theorem sum_exp_mul_trig_ne_ratCast {ι : Type*} (s : Finset ι) (a b : ι → ℚ)
    (hab : ∀ k ∈ s, ¬(a k = 0 ∧ b k = 0)) (c d : ι → ℚ) (r : ℚ) (hr : r ≠ 0) :
    ∑ k ∈ s, Real.exp (a k : ℝ) *
      ((c k : ℝ) * Real.cos (b k : ℝ) + (d k : ℝ) * Real.sin (b k : ℝ)) ≠ (r : ℝ) := by
  classical
  -- A common denominator `D` for the arguments and `N` for the coefficients and the constant.
  let D : ℕ := ∏ k ∈ s, (a k).den * (b k).den
  let N : ℕ := r.den * ∏ k ∈ s, (c k).den * (d k).den
  have hD : 0 < D := Finset.prod_pos fun k _ => Nat.mul_pos (a k).den_pos (b k).den_pos
  have hN : 0 < N :=
    Nat.mul_pos r.den_pos (Finset.prod_pos fun k _ => Nat.mul_pos (c k).den_pos (d k).den_pos)
  have hint (q : ℚ) (m : ℕ) (hm : q.den ∣ m) : ((q.num * (m / q.den : ℕ) : ℤ) : ℝ) = q * m := by
    obtain ⟨t, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left _ q.den_pos]
    push_cast
    rw [← mul_assoc, Rat.cast_def]
    field_simp
  have hDa (k : ι) (hk : k ∈ s) : (a k).den ∣ D :=
    (Dvd.intro _ rfl).trans (Finset.dvd_prod_of_mem (fun k => (a k).den * (b k).den) hk)
  have hDb (k : ι) (hk : k ∈ s) : (b k).den ∣ D :=
    (Dvd.intro_left _ rfl).trans (Finset.dvd_prod_of_mem (fun k => (a k).den * (b k).den) hk)
  have hNc (k : ι) (hk : k ∈ s) : (c k).den ∣ N :=
    ((Dvd.intro _ rfl).trans
      (Finset.dvd_prod_of_mem (fun k => (c k).den * (d k).den) hk)).trans (Dvd.intro_left _ rfl)
  have hNd (k : ι) (hk : k ∈ s) : (d k).den ∣ N :=
    ((Dvd.intro_left _ rfl).trans
      (Finset.dvd_prod_of_mem (fun k => (c k).den * (d k).den) hk)).trans (Dvd.intro_left _ rfl)
  have hNr : r.den ∣ N := Dvd.intro _ rfl
  intro h
  refine sum_exp_mul_trig_ne_intCast s D hD
    (fun k => (a k).num * (D / (a k).den : ℕ)) (fun k => (b k).num * (D / (b k).den : ℕ)) ?_
    (fun k => (c k).num * (N / (c k).den : ℕ)) (fun k => (d k).num * (N / (d k).den : ℕ))
    (r.num * (N / r.den : ℕ)) ?_ ?_
  · intro k hk hzero
    have hpos (q : ℚ) (hq : q.den ∣ D) : (0 : ℤ) < ((D / q.den : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hD hq) q.den_pos
    refine hab k hk ⟨Rat.num_eq_zero.mp ?_, Rat.num_eq_zero.mp ?_⟩
    · exact (mul_eq_zero.mp hzero.1).resolve_right (hpos _ (hDa k hk)).ne'
    · exact (mul_eq_zero.mp hzero.2).resolve_right (hpos _ (hDb k hk)).ne'
  · have hpos : (0 : ℤ) < ((N / r.den : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hN hNr) r.den_pos
    exact mul_ne_zero (Rat.num_ne_zero.mpr hr) hpos.ne'
  · have hDR : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    rw [hint r N hNr, ← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hint (a k) D (hDa k hk), hint (b k) D (hDb k hk), hint (c k) N (hNc k hk),
      hint (d k) N (hNd k hk), mul_div_assoc, mul_div_assoc, div_self hDR, mul_one, mul_one]
    ring

end FloatLib.Numerics.Enclosure
