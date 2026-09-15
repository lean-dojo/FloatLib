/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral

/-!
# Exponentials of nonzero rational arguments are transcendental

The elementary rounding kernels also encounter algebraic boundaries, for example when a
hyperbolic function is written in terms of an exponential. Irrationality alone does not rule
out equality with those boundaries.

The proof uses mathlib’s Lindemann–Weierstrass polynomial approximation at finitely many
integer roots at once. An assumed integer linear relation between their
exponentials gives a nonzero integer whose absolute value tends to zero. Applying this to the
powers in a polynomial proves transcendence.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter Polynomial
open scoped Topology BigOperators

/--
An integer linear combination of exponentials at nonzero integer arguments cannot cancel a
nonzero integer constant.
-/
theorem int_add_sum_exp_intCast_ne_zero {ι : Type*} (s : Finset ι)
    (argument : ι → ℤ) (hargument : ∀ k ∈ s, argument k ≠ 0)
    (a : ι → ℤ) (a₀ : ℤ) (ha₀ : a₀ ≠ 0) :
    (a₀ : ℝ) + ∑ k ∈ s, (a k : ℝ) * Real.exp (argument k : ℝ) ≠ 0 := by
  intro hrelation
  let f : ℤ[X] := ∏ k ∈ s, (X - C (argument k))
  have hf : f.eval 0 ≠ 0 := by
    simp only [f, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
    exact Finset.prod_ne_zero_iff.mpr fun k hk => neg_ne_zero.mpr (hargument k hk)
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf
  let weight : ℝ := ∑ k ∈ s, |(a k : ℝ)|
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
  let z : ℤ := n * a₀ + p * ∑ k ∈ s, a k * g.eval (argument k)
  have hz : z ≠ 0 := by
    intro hz
    have hdiv : (p : ℤ) ∣ n * a₀ := by
      refine ⟨-(∑ k ∈ s, a k * g.eval (argument k)), ?_⟩
      dsimp [z] at hz
      linear_combination hz
    rcases Int.Prime.dvd_mul' hp hdiv with h | h
    · exact hn h
    · have := Nat.le_of_dvd (Int.natAbs_pos.mpr ha₀) (Int.natCast_dvd.mp h)
      omega
  have hzlower : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : 1 ≤ z.natAbs := Int.natAbs_pos.mpr hz
    have hcast : (1 : ℤ) ≤ (z.natAbs : ℤ) := by exact_mod_cast this
    rw [Int.natCast_natAbs] at hcast
    exact_mod_cast hcast
  have herror (k : ι) (hk : k ∈ s) :
      |(n : ℝ) * Real.exp (argument k : ℝ) - (p : ℝ) * ((g.eval (argument k) : ℤ) : ℝ)| ≤
        c ^ p / (p - 1).factorial := by
    have hfzero : f ≠ 0 := by
      intro h
      exact hf (by simp [h])
    have hroot : (argument k : ℂ) ∈ f.aroots ℂ := by
      apply mem_aroots.mpr
      refine ⟨hfzero, ?_⟩
      simp only [f, map_prod, map_sub, aeval_X, aeval_C]
      exact Finset.prod_eq_zero hk (by simp)
    have heval : (aeval (argument k : ℂ)) g = ((g.eval (argument k) : ℤ) : ℂ) := by
      simpa using (aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (argument k) g)
    have hbound := hg hroot
    simp only [zsmul_eq_mul, nsmul_eq_mul, heval] at hbound
    have hexp : Complex.exp (argument k : ℂ) = (Real.exp (argument k : ℝ) : ℂ) := by
      rw [← Complex.ofReal_intCast, Complex.ofReal_exp]
    rw [hexp] at hbound
    simpa only [← Complex.ofReal_intCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      using hbound
  have hzsum :
      (z : ℝ) = -(∑ k ∈ s,
        (a k : ℝ) * ((n : ℝ) * Real.exp (argument k : ℝ) -
          p * ((g.eval (argument k) : ℤ) : ℝ))) := by
    dsimp only [z]
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hsum : ∑ k ∈ s, (a k : ℝ) * ((n : ℝ) * Real.exp (argument k : ℝ)) =
        n * ∑ k ∈ s, (a k : ℝ) * Real.exp (argument k : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hsum' : ∑ k ∈ s, (a k : ℝ) * ((p : ℝ) * ((g.eval (argument k) : ℤ) : ℝ)) =
        p * ∑ k ∈ s, (a k : ℝ) * ((g.eval (argument k) : ℤ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum, hsum']
    linear_combination (n : ℝ) * hrelation
  have hzupper : |(z : ℝ)| ≤ weight * (c ^ p / (p - 1).factorial) := by
    rw [hzsum, abs_neg]
    calc
      _ ≤ ∑ k ∈ s, |(a k : ℝ) *
          ((n : ℝ) * Real.exp (argument k : ℝ) - p * ((g.eval (argument k) : ℤ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ s, |(a k : ℝ)| * (c ^ p / (p - 1).factorial) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herror k hk) (abs_nonneg _)
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

/-- A nonzero integer argument has an exponential transcendental over the integers. -/
theorem transcendental_int_exp_intCast (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℤ (Real.exp (m : ℝ)) := by
  intro halgebraic
  obtain ⟨q, hqzero, hq⟩ := halgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_iff_ne_zero.mpr (Real.exp_ne_zero _))
  have hargument (k : ℕ) (hk : k ∈ q.support.erase 0) : (k : ℤ) * m ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Finset.mem_erase.mp hk).1) hm
  apply int_add_sum_exp_intCast_ne_zero (q.support.erase 0)
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
  exact Real.exp_nat_mul (m : ℝ) k

/-- A nonzero integer argument has an exponential transcendental over the rationals. -/
theorem transcendental_exp_intCast (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℚ (Real.exp (m : ℝ)) := by
  intro h
  exact transcendental_int_exp_intCast m hm
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)

/-- Every nonzero rational argument has a transcendental exponential. -/
theorem transcendental_exp_ratCast (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Real.exp (q : ℝ)) := by
  intro halgebraic
  have hpower := halgebraic.pow q.den
  have hscale : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  rw [← Real.exp_nat_mul, hscale] at hpower
  exact transcendental_exp_intCast q.num (Rat.num_ne_zero.mpr hq) hpower

end FloatLib.Numerics.Enclosure
