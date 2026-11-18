/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Transcendental
public import Mathlib.Data.Rat.Cast.Order

/-!
# Separation for two decaying rational exponentials

A common denominator expresses both exponentials as positive integral powers
of one transcendental number. Their sum therefore cannot be rational: a
rational sum would give a nonzero polynomial annihilating that number.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Polynomial

/-- Two exponentials at negative rational arguments have irrational sum. -/
theorem exp_neg_add_exp_neg_ne_ratCast (a b r : ℚ) (ha : 0 < a) (hb : 0 < b) :
    Real.exp (-(a : ℝ)) + Real.exp (-(b : ℝ)) ≠ (r : ℝ) := by
  intro hequal
  have hr : r ≠ 0 := by
    intro hz
    have hpositive := add_pos (Real.exp_pos (-(a : ℝ))) (Real.exp_pos (-(b : ℝ)))
    rw [hequal, hz, Rat.cast_zero] at hpositive
    exact (lt_irrefl _ hpositive)
  let d : ℕ := a.den * b.den
  let m : ℕ := a.num.toNat * b.den
  let n : ℕ := b.num.toNat * a.den
  have hd : d ≠ 0 := Nat.mul_ne_zero a.den_nz b.den_nz
  have haNum : 0 < a.num := Rat.num_pos.mpr ha
  have hbNum : 0 < b.num := Rat.num_pos.mpr hb
  have hm : m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos
    (by omega : 0 < a.num.toNat) b.pos)
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos
    (by omega : 0 < b.num.toNat) a.pos)
  have hscale (q : ℚ) (hq : 0 < q) (factor : ℕ) (hfactor : factor ≠ 0) :
      ((q.num.toNat * factor : ℕ) : ℝ) *
        ((-1 / ((q.den * factor : ℕ) : ℚ) : ℚ) : ℝ) = -(q : ℝ) := by
    have hnum : (q.num.toNat : ℝ) = (q.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq.le)
    rw [Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_mul, Nat.cast_mul, hnum, Rat.cast_def]
    have hfactorReal : (factor : ℝ) ≠ 0 := by exact_mod_cast hfactor
    field_simp
  have hma : (m : ℝ) * ((-1 / (d : ℚ) : ℚ) : ℝ) = -(a : ℝ) := by
    exact hscale a ha b.den b.den_nz
  have hnb : (n : ℝ) * ((-1 / (d : ℚ) : ℚ) : ℝ) = -(b : ℝ) := by
    simpa only [n, d, Nat.mul_comm] using hscale b hb a.den a.den_nz
  apply transcendental_exp_ratCast (-1 / (d : ℚ)) (by
    exact div_ne_zero (by norm_num) (by exact_mod_cast hd))
  refine ⟨X ^ m + X ^ n - C r, ?_, ?_⟩
  · intro hzero
    have hroot : r = 0 := by
      simpa [hm, hn] using congrArg (fun p : ℚ[X] => p.eval 0) hzero
    exact hr hroot
  · simp only [map_sub, map_add, map_pow, aeval_X, aeval_C,
      ← Real.exp_nat_mul, hma, hnb, sub_eq_zero]
    exact hequal

end FloatLib.Numerics.Enclosure
