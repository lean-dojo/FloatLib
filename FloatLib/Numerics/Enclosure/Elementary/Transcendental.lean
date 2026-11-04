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
import Mathlib.Data.Nat.Prime.Int

/-!
# Exponentials of nonzero rational arguments are transcendental

Some of the boundaries that the elementary rounding kernels meet are algebraic numbers, for example
when a hyperbolic function is written in terms of an exponential, and irrationality alone doesn't
rule out equality with those.

The proof uses Mathlib's Lindemann-Weierstrass polynomial approximation at finitely many integer
roots at once. Suppose there is an integer linear relation between their exponentials. It gives a
nonzero integer whose absolute value tends to zero, which is impossible. Applying this to the powers
in a polynomial proves transcendence.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter Polynomial
open scoped Topology BigOperators

/--
Some prime above any bound makes a weighted Lindemann-Weierstrass error `c ^ p / (p - 1)!` smaller
than one.
-/
theorem exists_prime_mul_pow_div_factorial_lt_one (weight c : ℝ) (bound : ℕ) :
    ∃ p : ℕ, bound < p ∧ p.Prime ∧ weight * (c ^ p / (p - 1).factorial) < 1 := by
  have hlimit :
      Tendsto (fun n : ℕ => (weight * c) * (c ^ n / n.factorial))
        atTop (𝓝 0) := by
    simpa using (Real.summable_pow_div_factorial c).tendsto_atTop_zero.const_mul
      (weight * c)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max (N + 1) (bound + 1))
  refine ⟨p, by omega, hp, ?_⟩
  have hsmall := hN (p - 1) (by omega)
  have hpstep : p - 1 + 1 = p := by omega
  have heq : (weight * c) * (c ^ (p - 1) / (p - 1).factorial) =
      weight * (c ^ p / (p - 1).factorial) := by
    have hpow : c ^ p = c ^ (p - 1) * c :=
      (congrArg (c ^ ·) hpstep.symm).trans (pow_succ c (p - 1))
    rw [hpow]
    ring
  rwa [heq] at hsmall

/--
If a prime `p` divides neither `n` nor the nonzero `a₀`, here because `|a₀| < p`, then
`n * a₀ + p * t` is not zero.
-/
theorem int_mul_add_prime_mul_ne_zero {p : ℕ} (hp : p.Prime) {n a₀ : ℤ} (t : ℤ)
    (hn : ¬(p : ℤ) ∣ n) (ha₀ : a₀ ≠ 0) (hlt : a₀.natAbs < p) :
    n * a₀ + p * t ≠ 0 := by
  intro hz
  have hdiv : (p : ℤ) ∣ n * a₀ := ⟨-t, by linear_combination hz⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdiv with h | h
  · exact hn h
  · have := Nat.le_of_dvd (Int.natAbs_pos.mpr ha₀) (Int.natCast_dvd.mp h)
    omega

/--
The cancellation estimate of the Lindemann-Weierstrass argument, in any normed field: if
`a₀ + ∑ a k * x k = 0` and each `n * x k` is within `E` of `p * y k`, then
`n * a₀ + p * ∑ a k * y k` has norm at most `(∑ ‖a k‖) * E`.
-/
theorem norm_mul_add_mul_sum_le {K : Type*} [NormedField K] {ι : Type*} (s : Finset ι)
    (a x y : ι → K) (a₀ n p : K) (E : ℝ)
    (hrelation : a₀ + ∑ k ∈ s, a k * x k = 0)
    (herror : ∀ k ∈ s, ‖n * x k - p * y k‖ ≤ E) :
    ‖n * a₀ + p * ∑ k ∈ s, a k * y k‖ ≤ (∑ k ∈ s, ‖a k‖) * E := by
  have hsplit : ∑ k ∈ s, a k * (n * x k - p * y k) =
      n * ∑ k ∈ s, a k * x k - p * ∑ k ∈ s, a k * y k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsum : n * a₀ + p * ∑ k ∈ s, a k * y k = -∑ k ∈ s, a k * (n * x k - p * y k) := by
    rw [hsplit]
    linear_combination n * hrelation
  rw [hsum, norm_neg, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (herror k hk) (norm_nonneg _)

/--
A nonzero element of a field is transcendental over `ℤ` when no integer relation
`a₀ + ∑ a k * x ^ k` with `a₀ ≠ 0` and positive exponents vanishes.
-/
theorem transcendental_int_of_add_sum_pow_ne_zero {A : Type*} [Field A] (x : A) (hx : x ≠ 0)
    (hrelation : ∀ (s : Finset ℕ) (a : ℕ → ℤ) (a₀ : ℤ), a₀ ≠ 0 → (∀ k ∈ s, k ≠ 0) →
      (a₀ : A) + ∑ k ∈ s, (a k : A) * x ^ k ≠ 0) :
    Transcendental ℤ x := by
  intro halgebraic
  obtain ⟨q, hqzero, hq⟩ := halgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  apply hrelation (q.support.erase 0) q.coeff (q.coeff 0) hqzero
    (fun k hk => (Finset.mem_erase.mp hk).1)
  have hzero_mem : 0 ∈ q.support := mem_support_iff.mpr hqzero
  rw [aeval_def, eval₂_eq_sum, sum_def] at hq
  rw [← Finset.add_sum_erase _ _ hzero_mem] at hq
  simpa only [pow_zero, mul_one, eq_intCast] using hq

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
  obtain ⟨p, hpbound, hp, hsmall⟩ := exists_prime_mul_pow_div_factorial_lt_one weight c
    (max (f.eval 0).natAbs a₀.natAbs)
  obtain ⟨n, hn, g, _, hg⟩ := hc p (by omega) hp
  let z : ℤ := n * a₀ + p * ∑ k ∈ s, a k * g.eval (argument k)
  have hz : z ≠ 0 := int_mul_add_prime_mul_ne_zero hp _ hn ha₀ (by omega)
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
  have hzupper : |(z : ℝ)| ≤ weight * (c ^ p / (p - 1).factorial) := by
    have h := norm_mul_add_mul_sum_le s (fun k => (a k : ℝ)) (fun k => Real.exp (argument k : ℝ))
      (fun k => ((g.eval (argument k) : ℤ) : ℝ)) (a₀ : ℝ) (n : ℝ) (p : ℝ) _ hrelation
      (fun k hk => by simpa only [Real.norm_eq_abs] using herror k hk)
    dsimp only [z]
    push_cast
    simpa only [Real.norm_eq_abs] using h
  exact (not_lt_of_ge hzlower) (hzupper.trans_lt hsmall)

/-- A nonzero integer argument has an exponential transcendental over the integers. -/
theorem transcendental_int_exp_intCast (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℤ (Real.exp (m : ℝ)) := by
  refine transcendental_int_of_add_sum_pow_ne_zero _ (Real.exp_ne_zero _)
    fun s a a₀ ha₀ hs => ?_
  have hpow (k : ℕ) : Real.exp (m : ℝ) ^ k = Real.exp (((k : ℤ) * m : ℤ) : ℝ) := by
    push_cast
    exact (Real.exp_nat_mul (m : ℝ) k).symm
  simp only [hpow]
  exact int_add_sum_exp_intCast_ne_zero s (fun k => (k : ℤ) * m)
    (fun k hk => mul_ne_zero (by exact_mod_cast hs k hk) hm) a a₀ ha₀

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
