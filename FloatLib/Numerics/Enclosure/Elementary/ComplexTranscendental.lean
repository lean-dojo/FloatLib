/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Transcendental
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Exponentials at purely imaginary rational arguments

Correctly rounding trigonometric functions requires excluding exact rational boundaries.
The real-exponential argument extends to imaginary integer arguments by using Gaussian
integers. The polynomial `X² + m²` supplies both conjugate roots to mathlib's exponential
approximation theorem, and a nonzero Gaussian integer has complex norm at least one.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter Polynomial
open scoped Topology BigOperators

private def imaginaryInteger (m : ℤ) : GaussianInt := ⟨0, m⟩

private theorem coe_imaginaryInteger (m : ℤ) :
    (imaginaryInteger m : ℂ) = (m : ℂ) * Complex.I := by
  simp [imaginaryInteger, GaussianInt.toComplex_def']

private def evalImaginary (g : ℤ[X]) (m : ℤ) : GaussianInt :=
  g.eval₂ (Int.castRingHom GaussianInt) (imaginaryInteger m)

private theorem coe_evalImaginary (g : ℤ[X]) (m : ℤ) :
    (evalImaginary g m : ℂ) = aeval ((m : ℂ) * Complex.I) g := by
  change GaussianInt.toComplex (g.eval₂ _ _) = _
  simp only [eval₂_eq_sum, sum_def, map_sum, map_mul, map_pow, aeval_def]
  rw [coe_imaginaryInteger]
  apply Finset.sum_congr rfl
  intro k _
  change GaussianInt.toComplex ((g.coeff k : ℤ) : GaussianInt) * _ = _
  rw [map_intCast]
  rfl

private theorem one_le_norm_gaussianInt (z : GaussianInt) (hz : z ≠ 0) :
    (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
  have hnorm : (1 : ℤ) ≤ z.norm := GaussianInt.norm_pos.mpr hz
  have hnormReal : (1 : ℝ) ≤ Complex.normSq (z : ℂ) := by
    have hcast : (1 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hnorm
    simpa only [GaussianInt.intCast_real_norm] using hcast
  rw [Complex.normSq_eq_norm_sq] at hnormReal
  nlinarith [norm_nonneg (z : ℂ)]

/--
An integer linear combination of exponentials at nonzero imaginary integer arguments cannot
cancel a nonzero integer constant.
-/
theorem int_add_sum_exp_intCast_mul_I_ne_zero {ι : Type*} (s : Finset ι)
    (argument : ι → ℤ) (hargument : ∀ k ∈ s, argument k ≠ 0)
    (a : ι → ℤ) (a₀ : ℤ) (ha₀ : a₀ ≠ 0) :
    (a₀ : ℂ) + ∑ k ∈ s, (a k : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I) ≠ 0 := by
  intro hrelation
  let f : ℤ[X] := ∏ k ∈ s, (X ^ 2 + C (argument k ^ 2))
  have hf : f.eval 0 ≠ 0 := by
    simp only [f, eval_prod, eval_add, eval_pow, eval_X, zero_pow (by decide : 2 ≠ 0),
      eval_C, zero_add]
    exact Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hargument k hk)
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf
  let weight : ℝ := ∑ k ∈ s, ‖(a k : ℂ)‖
  have hlimit :
      Tendsto (fun n : ℕ => (weight * c) * (c ^ n / n.factorial))
        atTop (𝓝 0) := by
    simpa using (Real.summable_pow_div_factorial c).tendsto_atTop_zero.const_mul
      (weight * c)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨p, hpbound, hp⟩ :=
    Nat.exists_infinite_primes (max (N + 1) (max (f.eval 0).natAbs a₀.natAbs + 1))
  obtain ⟨n, hn, g, _, hg⟩ := hc p (by omega) hp
  let total : GaussianInt := ∑ k ∈ s, (a k : GaussianInt) * evalImaginary g (argument k)
  let z : GaussianInt := (n : GaussianInt) * a₀ + p * total
  have hz : z ≠ 0 := by
    intro hz
    have hre : n * a₀ + (p : ℤ) * total.re = 0 := by
      simpa [z] using congrArg Zsqrtd.re hz
    have hdiv : (p : ℤ) ∣ n * a₀ := by
      refine ⟨-total.re, ?_⟩
      linear_combination hre
    rcases Int.Prime.dvd_mul' hp hdiv with h | h
    · exact hn h
    · have := Nat.le_of_dvd (Int.natAbs_pos.mpr ha₀) (Int.natCast_dvd.mp h)
      omega
  have hzlower := one_le_norm_gaussianInt z hz
  have herror (k : ι) (hk : k ∈ s) :
      ‖(n : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I) -
        (p : ℂ) * (evalImaginary g (argument k) : ℂ)‖ ≤
          c ^ p / (p - 1).factorial := by
    have hfzero : f ≠ 0 := by
      intro h
      exact hf (by simp [h])
    have hroot : (argument k : ℂ) * Complex.I ∈ f.aroots ℂ := by
      apply mem_aroots.mpr
      refine ⟨hfzero, ?_⟩
      simp only [f, map_prod, map_add, map_pow, aeval_X, aeval_C]
      apply Finset.prod_eq_zero hk
      simp [mul_pow]
    simpa only [coe_evalImaginary, zsmul_eq_mul, nsmul_eq_mul] using hg hroot
  have htotal : (total : ℂ) =
      ∑ k ∈ s, (a k : ℂ) * (evalImaginary g (argument k) : ℂ) := by
    change GaussianInt.toComplex (∑ k ∈ s, _) = _
    simp only [map_sum, map_mul, map_intCast]
  have hzsum :
      (z : ℂ) = -(∑ k ∈ s,
        (a k : ℂ) * ((n : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I) -
          p * (evalImaginary g (argument k) : ℂ))) := by
    change GaussianInt.toComplex ((n : GaussianInt) * a₀ + p * total) = _
    simp only [map_add, map_mul, map_intCast, map_natCast]
    rw [htotal]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hsum : ∑ k ∈ s, (a k : ℂ) *
        ((n : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I)) =
        n * ∑ k ∈ s, (a k : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hsum' : ∑ k ∈ s, (a k : ℂ) *
        ((p : ℂ) * (evalImaginary g (argument k) : ℂ)) =
        p * ∑ k ∈ s, (a k : ℂ) * (evalImaginary g (argument k) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum, hsum']
    linear_combination (n : ℂ) * hrelation
  have hzupper : ‖(z : ℂ)‖ ≤ weight * (c ^ p / (p - 1).factorial) := by
    rw [hzsum, norm_neg]
    calc
      _ ≤ ∑ k ∈ s, ‖(a k : ℂ) *
          ((n : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I) -
            p * (evalImaginary g (argument k) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ s, ‖(a k : ℂ)‖ * (c ^ p / (p - 1).factorial) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (herror k hk) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hsmall := hN (p - 1) (by omega)
  have hpstep : p - 1 + 1 = p := by omega
  have heq : (weight * c) * (c ^ (p - 1) / (p - 1).factorial) =
      weight * (c ^ p / (p - 1).factorial) := by
    have hpow : c ^ p = c ^ (p - 1) * c :=
      (congrArg (c ^ ·) hpstep.symm).trans (pow_succ c (p - 1))
    rw [hpow]
    ring
  rw [heq] at hsmall
  exact (not_lt_of_ge hzlower) (hzupper.trans_lt hsmall)

/-- The exponential at a nonzero imaginary integer argument is transcendental over `ℤ`. -/
theorem transcendental_int_exp_intCast_mul_I (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℤ (Complex.exp ((m : ℂ) * Complex.I)) := by
  intro halgebraic
  obtain ⟨q, hqzero, hq⟩ := halgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_iff_ne_zero.mpr (Complex.exp_ne_zero _))
  have hargument (k : ℕ) (hk : k ∈ q.support.erase 0) : (k : ℤ) * m ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Finset.mem_erase.mp hk).1) hm
  apply int_add_sum_exp_intCast_mul_I_ne_zero (q.support.erase 0)
    (fun k => (k : ℤ) * m) hargument q.coeff (q.coeff 0) hqzero
  have hzero_mem : 0 ∈ q.support := mem_support_iff.mpr hqzero
  rw [aeval_def, eval₂_eq_sum, sum_def] at hq
  rw [← Finset.add_sum_erase _ _ hzero_mem] at hq
  simp only [pow_zero, mul_one, eq_intCast] at hq
  convert hq using 1
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast
  rw [mul_assoc, Complex.exp_nat_mul]

/-- The exponential at a nonzero imaginary integer argument is transcendental over `ℚ`. -/
theorem transcendental_exp_intCast_mul_I (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℚ (Complex.exp ((m : ℂ) * Complex.I)) := by
  intro h
  exact transcendental_int_exp_intCast_mul_I m hm
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr h)

/-- The exponential at a nonzero imaginary rational argument is transcendental over `ℚ`. -/
theorem transcendental_exp_ratCast_mul_I (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Complex.exp ((q : ℂ) * Complex.I)) := by
  intro halgebraic
  have hpower := halgebraic.pow q.den
  have hscale : (q.den : ℂ) * ((q : ℂ) * Complex.I) = (q.num : ℂ) * Complex.I := by
    rw [Rat.cast_def]
    field_simp
  rw [← Complex.exp_nat_mul, hscale] at hpower
  exact transcendental_exp_intCast_mul_I q.num (Rat.num_ne_zero.mpr hq) hpower

end FloatLib.Numerics.Enclosure
