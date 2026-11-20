/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Transcendental
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# Exponentials at purely imaginary rational arguments

To round a trigonometric function correctly, we have to rule out exact rational boundaries. Gaussian
integers extend the real-exponential argument to imaginary integer arguments. The polynomial
`X² + m²` supplies both conjugate roots to Mathlib's exponential approximation theorem, and a
nonzero Gaussian integer has complex norm at least one.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter Polynomial
open scoped Topology BigOperators

private theorem one_le_norm_gaussianInt (z : GaussianInt) (hz : z ≠ 0) :
    (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
  rw [← one_le_sq_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm]
  exact_mod_cast GaussianInt.norm_pos.mpr hz

/--
The integer polynomial whose roots are the Gaussian rationals `argument k / D` and their
conjugates.
-/
private noncomputable def conjugatePairs {ι : Type*} (s : Finset ι) (D : ℕ)
    (argument : ι → GaussianInt) : ℤ[X] :=
  ∏ k ∈ s, ((C (D : ℤ) * X - C (argument k).re) ^ 2 + C ((argument k).im ^ 2))

private theorem eval_zero_conjugatePairs_ne_zero {ι : Type*} (s : Finset ι) (D : ℕ)
    (argument : ι → GaussianInt) (hargument : ∀ k ∈ s, argument k ≠ 0) :
    (conjugatePairs s D argument).eval 0 ≠ 0 := by
  simp only [conjugatePairs, eval_prod, eval_add, eval_pow, eval_sub, eval_mul, eval_C, eval_X,
    mul_zero, zero_sub]
  refine Finset.prod_ne_zero_iff.mpr fun k hk hzero => hargument k hk ?_
  have hre : (argument k).re ^ 2 = 0 := by
    linarith [sq_nonneg (argument k).re, sq_nonneg (argument k).im]
  have him : (argument k).im ^ 2 = 0 := by
    linarith [sq_nonneg (argument k).re, sq_nonneg (argument k).im]
  exact Zsqrtd.ext (by simpa using hre) (by simpa using him)

private theorem div_mem_aroots_conjugatePairs {ι : Type*} (s : Finset ι) {D : ℕ} (hD : 0 < D)
    (argument : ι → GaussianInt) (hne : conjugatePairs s D argument ≠ 0) {k : ι} (hk : k ∈ s) :
    (argument k : ℂ) / D ∈ (conjugatePairs s D argument).aroots ℂ := by
  have hDC : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  refine mem_aroots.mpr ⟨hne, ?_⟩
  simp only [conjugatePairs, map_prod, map_add, map_pow, map_sub, map_mul, aeval_X, aeval_C]
  apply Finset.prod_eq_zero hk
  rw [GaussianInt.toComplex_def]
  simp only [eq_intCast, Int.cast_natCast]
  rw [mul_div_cancel₀ _ hDC, add_sub_cancel_left, mul_pow, Complex.I_sq]
  ring

/-- `D ^ M` times an integer polynomial of degree at most `M` at `w / D` is a Gaussian integer. -/
private theorem exists_gaussianInt_eq_pow_mul_aeval {D : ℕ} (hD : 0 < D) (w : GaussianInt)
    (g : ℤ[X]) {M : ℕ} (hM : g.natDegree ≤ M) :
    ∃ E : GaussianInt, (E : ℂ) = (D : ℂ) ^ M * aeval ((w : ℂ) / D) g := by
  have hDC : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  refine ⟨∑ j ∈ Finset.range (M + 1),
    (g.coeff j : GaussianInt) * ((D : GaussianInt) ^ (M - j) * w ^ j), ?_⟩
  rw [aeval_eq_sum_range' (show g.natDegree < M + 1 by omega), Finset.mul_sum]
  simp only [map_sum, map_mul, map_pow, map_intCast, map_natCast]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [zsmul_eq_mul, div_pow]
  have hsplit : (D : ℂ) ^ M = (D : ℂ) ^ (M - j) * (D : ℂ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  rw [hsplit]
  field_simp

/--
The Gaussian integer `m a₀ + p t` is not zero when the prime `p` does not divide `m` and exceeds
the absolute values of both parts of `a₀ ≠ 0`.
-/
private theorem gaussianInt_mul_add_prime_mul_ne_zero {p : ℕ} (hp : p.Prime) {m : ℤ}
    (hm : ¬(p : ℤ) ∣ m) {a₀ : GaussianInt} (ha₀ : a₀ ≠ 0) (hre : a₀.re.natAbs < p)
    (him : a₀.im.natAbs < p) (total : GaussianInt) :
    (m : GaussianInt) * a₀ + (p : GaussianInt) * total ≠ 0 := by
  intro hzero
  by_cases hre0 : a₀.re = 0
  · have him0 : a₀.im ≠ 0 := fun h => ha₀ (Zsqrtd.ext hre0 h)
    have hpart := congrArg Zsqrtd.im hzero
    exact int_mul_add_prime_mul_ne_zero hp total.im hm him0 him (by simpa using hpart)
  · have hpart := congrArg Zsqrtd.re hzero
    exact int_mul_add_prime_mul_ne_zero hp total.re hm hre0 hre (by simpa using hpart)

/--
A linear combination of exponentials at nonzero Gaussian rational arguments `argument k / D`,
with Gaussian integer coefficients, cannot cancel a nonzero Gaussian integer constant.

This is the case of the Lindemann-Weierstrass theorem that the complex elementary functions need:
`ℚ(i)` is closed under conjugation, so the polynomial with the roots `argument k / D` and their
conjugates has integer coefficients, and clearing the denominator `D` from Mathlib's exponential
approximation leaves a nonzero Gaussian integer of norm below one.
-/
theorem gaussianInt_add_sum_exp_div_ne_zero {ι : Type*} (s : Finset ι) (D : ℕ) (hD : 0 < D)
    (argument : ι → GaussianInt) (hargument : ∀ k ∈ s, argument k ≠ 0)
    (a : ι → GaussianInt) (a₀ : GaussianInt) (ha₀ : a₀ ≠ 0) :
    (a₀ : ℂ) + ∑ k ∈ s, (a k : ℂ) * Complex.exp ((argument k : ℂ) / D) ≠ 0 := by
  intro hrelation
  have hf := eval_zero_conjugatePairs_ne_zero s D argument hargument
  have hfzero : conjugatePairs s D argument ≠ 0 := fun h => hf (by simp [h])
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx _ hf
  obtain ⟨p, hpbound, hp, hsmall⟩ := exists_prime_mul_pow_div_factorial_lt_one
    (∑ k ∈ s, ‖(a k : ℂ)‖) ((D : ℝ) ^ (conjugatePairs s D argument).natDegree * c)
    (max (max ((conjugatePairs s D argument).eval 0).natAbs D) (max a₀.re.natAbs a₀.im.natAbs))
  obtain ⟨n, hn, g, hdegree, hg⟩ := hc p (by omega) hp
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = p * (conjugatePairs s D argument).natDegree := ⟨_, rfl⟩
  choose E hE using fun k =>
    exists_gaussianInt_eq_pow_mul_aeval hD (argument k) g (M := M) (by omega)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = n * (D : ℤ) ^ M := ⟨_, rfl⟩
  have hpD : ¬(p : ℤ) ∣ m := by
    rw [hm]
    intro hdiv
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdiv with h | h
    · exact hn h
    · have hdvd := Int.natCast_dvd_natCast.mp ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h)
      have := Nat.le_of_dvd hD hdvd
      omega
  have hzlower := one_le_norm_gaussianInt _
    (gaussianInt_mul_add_prime_mul_ne_zero hp hpD ha₀ (by omega) (by lia) (∑ k ∈ s, a k * E k))
  have herror (k : ι) (hk : k ∈ s) :
      ‖(n : ℂ) * Complex.exp ((argument k : ℂ) / D) -
        (p : ℂ) * aeval ((argument k : ℂ) / D) g‖ ≤ c ^ p / (p - 1).factorial := by
    simpa only [zsmul_eq_mul, nsmul_eq_mul] using
      hg (div_mem_aroots_conjugatePairs s hD argument hfzero hk)
  have hbound := norm_mul_add_mul_sum_le s (fun k => (a k : ℂ))
    (fun k => Complex.exp ((argument k : ℂ) / D))
    (fun k => aeval ((argument k : ℂ) / D) g) (a₀ : ℂ) (n : ℂ) (p : ℂ) _ hrelation herror
  have hcast : (((m : GaussianInt) * a₀ + (p : GaussianInt) * ∑ k ∈ s, a k * E k :
      GaussianInt) : ℂ) = (D : ℂ) ^ M *
        ((n : ℂ) * a₀ + (p : ℂ) * ∑ k ∈ s, (a k : ℂ) * aeval ((argument k : ℂ) / D) g) := by
    simp only [map_add, map_mul, map_sum, map_intCast, map_natCast]
    have hsum : ∑ k ∈ s, GaussianInt.toComplex (a k) * GaussianInt.toComplex (E k) =
        (D : ℂ) ^ M * ∑ k ∈ s, (a k : ℂ) * aeval ((argument k : ℂ) / D) g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hE k]; ring
    rw [hsum, hm]
    push_cast
    ring
  refine (not_lt_of_ge hzlower) (lt_of_le_of_lt ?_ hsmall)
  rw [hcast, norm_mul, norm_pow, Complex.norm_natCast]
  calc (D : ℝ) ^ M * ‖(n : ℂ) * a₀ +
        (p : ℂ) * ∑ k ∈ s, (a k : ℂ) * aeval ((argument k : ℂ) / D) g‖
      ≤ (D : ℝ) ^ M * ((∑ k ∈ s, ‖(a k : ℂ)‖) * (c ^ p / (p - 1).factorial)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (∑ k ∈ s, ‖(a k : ℂ)‖) *
        (((D : ℝ) ^ (conjugatePairs s D argument).natDegree * c) ^ p / (p - 1).factorial) := by
        rw [hM, mul_pow, ← pow_mul, Nat.mul_comm (conjugatePairs s D argument).natDegree p]
        ring

/--
An integer linear combination of exponentials at nonzero imaginary integer arguments cannot
cancel a nonzero integer constant.
-/
theorem int_add_sum_exp_intCast_mul_I_ne_zero {ι : Type*} (s : Finset ι)
    (argument : ι → ℤ) (hargument : ∀ k ∈ s, argument k ≠ 0)
    (a : ι → ℤ) (a₀ : ℤ) (ha₀ : a₀ ≠ 0) :
    (a₀ : ℂ) + ∑ k ∈ s, (a k : ℂ) * Complex.exp ((argument k : ℂ) * Complex.I) ≠ 0 := by
  have h := gaussianInt_add_sum_exp_div_ne_zero s 1 one_pos (fun k => ⟨0, argument k⟩)
    (fun k hk h => hargument k hk (by simpa using congrArg Zsqrtd.im h))
    (fun k => (a k : GaussianInt)) (a₀ : GaussianInt) (by exact_mod_cast ha₀)
  simpa [GaussianInt.toComplex_def'] using h

/-- The exponential at a nonzero imaginary integer argument is transcendental over `ℤ`. -/
theorem transcendental_int_exp_intCast_mul_I (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℤ (Complex.exp ((m : ℂ) * Complex.I)) := by
  refine transcendental_int_of_add_sum_pow_ne_zero _ (Complex.exp_ne_zero _)
    fun s a a₀ ha₀ hs => ?_
  have hpow (k : ℕ) : Complex.exp ((m : ℂ) * Complex.I) ^ k =
      Complex.exp ((((k : ℤ) * m : ℤ) : ℂ) * Complex.I) := by
    push_cast
    rw [mul_assoc, Complex.exp_nat_mul]
  simp only [hpow]
  exact int_add_sum_exp_intCast_mul_I_ne_zero s (fun k => (k : ℤ) * m)
    (fun k hk => mul_ne_zero (by exact_mod_cast hs k hk) hm) a a₀ ha₀

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
