/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.CBall.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Complex-ball enclosures of the imaginary exponential

Integer Horner evaluation encloses the Taylor polynomial, and the exponential remainder bound
certifies the small-input evaluator. Range reduction is sound for every supplied step and table
satisfying their enclosure contracts. The fallback unit square handles every rejected smallness
check. No bound on the computed radius is asserted.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

open scoped Nat

namespace CBall

/-- What `expITerms x k m` encloses for `y = i t`: `(m + k)! * ∑ j ≤ k, y ^ j / (m + j)!`. -/
noncomputable def hornerValue (y : ℂ) (k m : ℕ) : ℂ :=
  ((m + k)! : ℂ) * ∑ j ∈ Finset.range (k + 1), y ^ j / ((m + j)! : ℂ)

/-- With no step the value is one. -/
theorem hornerValue_zero (y : ℂ) (m : ℕ) : hornerValue y 0 m = 1 := by
  have hm : ((m ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  simp [hornerValue, hm]

/-- One step of Horner's rule: the coefficient `c = (m + k + 1)! / m!` plus `y` times the value
one index up. -/
theorem hornerValue_succ (y : ℂ) (k m c : ℕ) (hc : c * m ! = (m + (k + 1))!) :
    hornerValue y (k + 1) m = (c : ℂ) + y * hornerValue y k (m + 1) := by
  have hm : ((m ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hcC : (c : ℂ) = ((m + (k + 1))! : ℂ) / (m ! : ℂ) := by
    rw [eq_div_iff hm]
    exact_mod_cast hc
  have e1 : m + 1 + k = m + (k + 1) := by omega
  unfold hornerValue
  rw [Finset.sum_range_succ', e1, hcC]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      y ^ (j + 1) / ((m + (j + 1))! : ℂ) = y * (y ^ j / ((m + 1 + j)! : ℂ)) := by
    intro j _
    rw [show m + (j + 1) = m + 1 + j by omega, pow_succ', mul_div_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  simp only [pow_zero, Nat.add_zero]
  rw [mul_add, mul_one_div, mul_left_comm, add_comm]

/-- `expITerms x k m` is the coefficient `(m + k)! / m!` and a ball around the Horner value. -/
theorem expITerms_spec {x : Ball} {t : ℝ} (ht : x.Contains t) :
    ∀ k m : ℕ, (expITerms x k m).1 * m ! = (m + k)! ∧
      (expITerms x k m).2.Mem (hornerValue ((t : ℂ) * Complex.I) k m)
  | 0, m => by
    refine ⟨by simp [expITerms], ?_⟩
    rw [hornerValue_zero]
    simpa [expITerms] using mem_ofNat 1
  | k + 1, m => by
    obtain ⟨hc, hmem⟩ := expITerms_spec ht k (m + 1)
    have hc' : (m + 1) * (expITerms x k (m + 1)).1 * m ! = (m + (k + 1))! := by
      have : (m + 1) * (expITerms x k (m + 1)).1 * m ! =
          (expITerms x k (m + 1)).1 * (m + 1)! := by
        rw [Nat.factorial_succ, mul_assoc, mul_left_comm]
      rw [this, hc]
      congr 1
      omega
    refine ⟨hc', ?_⟩
    rw [hornerValue_succ _ k m _ hc']
    set A := hornerValue ((t : ℂ) * Complex.I) k (m + 1)
    have hval : (((m + 1) * (expITerms x k (m + 1)).1 : ℕ) : ℂ) + (t : ℂ) * Complex.I * A =
        ⟨(((m + 1) * (expITerms x k (m + 1)).1 : ℕ) : ℝ) - t * A.im, t * A.re⟩ := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
      · simp [Complex.mul_re, Complex.mul_im]
    rw [hval]
    exact mem_mk ⟨Ball.contains_sub (Ball.contains_ofNat _) (Ball.contains_mul ht hmem.2),
      Ball.contains_mul ht hmem.1⟩

/-- `Ball.ofNat c` is apart from zero for a positive `c`. -/
theorem apart_ofNat {c : Nat} (hc : 0 < c) : (Ball.ofNat c).apart = true := by
  change Nat.ble (Nat.succ 0) (Nat.add (Nat.sub c 0) (Nat.sub 0 c)) = true
  apply Nat.ble_eq_true_of_le
  simp only [Nat.add_eq, Nat.sub_eq, Nat.sub_zero, Nat.zero_sub, Nat.add_zero]
  exact hc

/-- `expIPoly x n p` contains the Taylor polynomial `∑ j < n, (i t) ^ j / j!`, for `n ≥ 1`. -/
theorem mem_expIPoly {x : Ball} {t : ℝ} (ht : x.Contains t) {n : Nat} (hn : 1 ≤ n) (p : Nat) :
    (expIPoly x n p).Mem
      (∑ j ∈ Finset.range n, ((t : ℂ) * Complex.I) ^ j / (j ! : ℂ)) := by
  obtain ⟨hc, hmem⟩ := expITerms_spec ht (n - 1) 0
  set c := (expITerms x (n - 1) 0).1
  have hcval : c = (n - 1)! := by simpa using hc
  have hcpos : 0 < c := hcval ▸ Nat.factorial_pos _
  have hinv := Ball.contains_inv (K := ℝ) (apart_ofNat hcpos) (Nat.add p (size c))
    (Ball.contains_ofNat c)
  have hscaled := mem_smul hinv hmem
  have hsum : (((c : ℝ)⁻¹ : ℝ) : ℂ) * hornerValue ((t : ℂ) * Complex.I) (n - 1) 0 =
      ∑ j ∈ Finset.range n, ((t : ℂ) * Complex.I) ^ j / (j ! : ℂ) := by
    have hcC : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    unfold hornerValue
    rw [show n - 1 + 1 = n by omega]
    simp only [Nat.zero_add]
    rw [← hcval]
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel_left₀ hcC]
  rw [← hsum]
  exact hscaled

/-- The remainder numerator is at least the remainder bound times `2 ^ p`. -/
theorem le_expIRemainder (j n p : Nat) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) / (2 ^ (j * n) * n ! * n) ≤ (expIRemainder j n p : ℝ) / 2 ^ p := by
  have hshl : ∀ a b : Nat, Nat.shiftLeft a b = a * 2 ^ b := fun a b => Nat.shiftLeft_eq a b
  have hdef : expIRemainder j n p = ceilDiv ((n + 1) * 2 ^ p) (n ! * 2 ^ (j * n) * n) := by
    unfold expIRemainder
    rw [factorial_eq, hshl, hshl]
    rfl
  have hden : 0 < n ! * 2 ^ (j * n) * n :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos n) (pow_pos (by decide) _)) hn
  have h := le_mul_ceilDiv (a := (n + 1) * 2 ^ p) hden
  rw [← hdef] at h
  have hcast : (((n : ℝ) + 1) * 2 ^ p) ≤
      ((n ! : ℝ) * 2 ^ (j * n) * n) * (expIRemainder j n p : ℝ) := by
    exact_mod_cast h
  have hpos : (0 : ℝ) < 2 ^ (j * n) * n ! * n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hcast

/-- `expISmall x j n p` contains `exp (i t)` for every `t` in `x`. -/
theorem mem_expISmall {x : Ball} {t : ℝ} (ht : x.Contains t) (j n p : Nat) :
    (expISmall x j n p).Mem (Complex.exp ((t : ℂ) * Complex.I)) := by
  unfold expISmall
  cases hcheck : Bool.and (x.within j) (Nat.ble 1 n)
  · change box.Mem _
    refine ⟨Ball.contains_unit ?_, Ball.contains_unit ?_⟩
    · rw [Complex.exp_ofReal_mul_I_re]; exact Real.abs_cos_le_one t
    · rw [Complex.exp_ofReal_mul_I_im]; exact Real.abs_sin_le_one t
  · have hboth : x.within j = true ∧ Nat.ble 1 n = true := by simpa using hcheck
    have hn : 1 ≤ n := Nat.le_of_ble_eq_true hboth.2
    have hsmall : |t| ≤ 1 / 2 ^ j := Ball.within_sound hboth.1 ht
    have hpoly := mem_expIPoly ht hn p
    set P := ∑ m ∈ Finset.range n, ((t : ℂ) * Complex.I) ^ m / (m ! : ℂ)
    set E := Complex.exp ((t : ℂ) * Complex.I)
    have hnorm : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
    have hle1 : ‖(t : ℂ) * Complex.I‖ ≤ 1 := by
      rw [hnorm]
      exact hsmall.trans (by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ (by norm_num))
    have hbound := Complex.exp_bound hle1 (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    rw [hnorm] at hbound
    have hrem : ‖E - P‖ ≤ (expIRemainder j n p : ℝ) / 2 ^ p := by
      refine le_trans hbound (le_trans ?_ (le_expIRemainder j n p hn))
      have hpow : |t| ^ n ≤ 1 / 2 ^ (j * n) := by
        calc |t| ^ n ≤ (1 / 2 ^ j) ^ n := pow_le_pow_left₀ (abs_nonneg t) hsmall n
          _ = 1 / 2 ^ (j * n) := by rw [div_pow, one_pow, ← pow_mul]
      calc |t| ^ n * ((n.succ : ℝ) * ((n ! : ℝ) * n)⁻¹)
          ≤ 1 / 2 ^ (j * n) * ((n.succ : ℝ) * ((n ! : ℝ) * n)⁻¹) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = ((n : ℝ) + 1) / (2 ^ (j * n) * n ! * n) := by
            simp only [Nat.cast_succ, div_eq_mul_inv, one_mul, mul_inv_rev,
              mul_assoc, mul_comm, mul_left_comm]
    have hre : |E.re - P.re| ≤ (expIRemainder j n p : ℝ) / 2 ^ p := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans hrem
    have him : |E.im - P.im| ≤ (expIRemainder j n p : ℝ) / 2 ^ p := by
      rw [← Complex.sub_im]
      exact (Complex.abs_im_le_norm _).trans hrem
    change (CBall.mk _ _).Mem E
    refine ⟨Ball.contains_round ?_ p, Ball.contains_round ?_ p⟩
    · have := Ball.contains_widen hpoly.1 hre
      rwa [add_sub_cancel] at this
    · have := Ball.contains_widen hpoly.2 him
      rwa [add_sub_cancel] at this

/-- `exp (i k π / 2) = i ^ k`. -/
theorem exp_quarterTurns (k : ℕ) :
    Complex.exp ((((k : ℝ) * (Real.pi / 2) : ℝ) : ℂ) * Complex.I) = Complex.I ^ k := by
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]

/--
Any evaluator and two phase actions satisfying their enclosure contracts give a sound
range reduction, for every real step and every precision.
-/
theorem mem_expIReduce {f : Ball → CBall} {positive negative : Nat → CBall → CBall}
    {s : ℝ}
    (hf : ∀ (r : Ball) (v : ℝ), r.Contains v → (f r).Mem (Complex.exp ((v : ℂ) * Complex.I)))
    (hpositive : ∀ (k : Nat) (z : CBall) (w : ℂ), z.Mem w →
      (positive k z).Mem (Complex.exp ((((k : ℝ) * s : ℝ) : ℂ) * Complex.I) * w))
    (hnegative : ∀ (k : Nat) (z : CBall) (w : ℂ), z.Mem w →
      (negative k z).Mem (Complex.exp (-((((k : ℝ) * s : ℝ) : ℂ) * Complex.I)) * w))
    {x step : Ball} {t : ℝ} (hs : step.Contains s) (ht : x.Contains t) (p : Nat) :
    (expIReduce f positive negative x step p).Mem (Complex.exp ((t : ℂ) * Complex.I)) := by
  unfold expIReduce
  set k := quarterTurns x step
  have hks := Ball.contains_mul (Ball.contains_ofNat (K := ℝ) k) hs
  cases Nat.ble x.minus x.plus
  · have h := hnegative k _ _ (hf _ _ (Ball.contains_round (Ball.contains_add ht hks) p))
    simpa only [← Complex.exp_add, Complex.ofReal_add, add_mul, neg_add_cancel_comm_assoc] using h
  · have h := hpositive k _ _ (hf _ _ (Ball.contains_round (Ball.contains_sub ht hks) p))
    simpa only [← Complex.exp_add, Complex.ofReal_sub, sub_mul, add_sub_cancel] using h

/--
`expIWith f x h p` contains `exp (i t)` for every `t` in `x`, when `h` contains `π / 2` and `f`
returns a ball around `exp (i v)` for every member `v` of its argument.
-/
theorem mem_expIWith {f : Ball → CBall}
    (hf : ∀ (r : Ball) (v : ℝ), r.Contains v → (f r).Mem (Complex.exp ((v : ℂ) * Complex.I)))
    {x h : Ball} {t : ℝ} (hh : h.Contains (Real.pi / 2)) (ht : x.Contains t) (p : Nat) :
    (expIWith f x h p).Mem (Complex.exp ((t : ℂ) * Complex.I)) := by
  refine mem_expIReduce hf ?_ ?_ hh ht p
  · intro k z w hw
    rw [exp_quarterTurns]
    exact mem_mulIPow k hw
  · intro k z w hw
    have h := mem_mulIPow (Nat.mul 3 k) hw
    rw [Complex.exp_neg, exp_quarterTurns]
    simpa only [show Nat.mul 3 k = 3 * k from rfl, pow_mul, Complex.I_pow_three,
      ← inv_pow, Complex.inv_I] using h

/-- `expI x h j n p` contains `exp (i t)` for every `t` in `x`, when `h` contains `π / 2`. -/
theorem mem_expI {x h : Ball} {t : ℝ} (hh : h.Contains (Real.pi / 2)) (ht : x.Contains t)
    (j n p : Nat) : (expI x h j n p).Mem (Complex.exp ((t : ℂ) * Complex.I)) :=
  mem_expIWith (fun _ _ hv => mem_expISmall hv j n p) hh ht p

/--
`expIStep x step tbl j n p` contains `exp (i t)` for every `t` in `x`, when `step` contains a
number `s` and every entry `tbl k` contains `exp (i k s)`.
-/
theorem mem_expIStep {x step : Ball} {tbl : Nat → CBall} {s t : ℝ} (hs : step.Contains s)
    (htbl : ∀ k : ℕ, (tbl k).Mem (Complex.exp ((((k : ℝ) * s : ℝ) : ℂ) * Complex.I)))
    (ht : x.Contains t) (j n p : Nat) :
    (expIStep x step tbl j n p).Mem (Complex.exp ((t : ℂ) * Complex.I)) := by
  refine mem_expIReduce (fun _ _ hv => mem_expISmall hv j n p) ?_ ?_ hs ht p
  · intro k z w hw
    exact mem_round (mem_mul (htbl k) hw) p
  · intro k z w hw
    have h := mem_round (mem_mul (mem_conj (htbl k)) hw) p
    simpa only [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_neg] using h

/-- `halfPi` contains `π / 2`. -/
theorem contains_halfPi : halfPi.Contains (Real.pi / 2) := by
  rw [halfPi, Ball.contains_mk, abs_le]
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  norm_num at hlo hhi ⊢
  constructor <;> linarith

end CBall

end FloatLib.Numerics.Kernel
