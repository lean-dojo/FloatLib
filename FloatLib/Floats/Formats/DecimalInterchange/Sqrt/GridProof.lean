/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Runtime
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Correct rounding of the square-root coefficient

The integer square root brackets the mathematical real square root. Exact
squared comparisons then give at most half-unit error in either nearest mode and the
appropriate one-sided bounds in the three directed modes.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem sqrtFloor_sq_le {x : ℚ} (hx : 0 ≤ x) : (sqrtFloor x : ℚ) ^ 2 ≤ x := by
  have hn : (sqrtFloor x : ℚ) ^ 2 ≤ (⌊x⌋₊ : ℚ) := by
    exact_mod_cast Nat.sqrt_le' ⌊x⌋₊
  exact hn.trans (Nat.floor_le hx)

theorem lt_sqrtFloor_succ_sq {x : ℚ} (hx : 0 ≤ x) :
    x < ((sqrtFloor x : ℚ) + 1) ^ 2 := by
  have hn := (Nat.floor_lt hx).mp (Nat.lt_succ_sqrt' ⌊x⌋₊)
  exact_mod_cast hn

theorem sqrtFloor_le_sqrt {x : ℚ} (hx : 0 ≤ x) :
    (sqrtFloor x : ℝ) ≤ Real.sqrt (x : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast sqrtFloor_sq_le hx

theorem sqrt_lt_sqrtFloor_succ {x : ℚ} (hx : 0 ≤ x) :
    Real.sqrt (x : ℝ) < (sqrtFloor x : ℝ) + 1 := by
  apply (Real.sqrt_lt (by exact_mod_cast hx) (by positivity)).mpr
  exact_mod_cast lt_sqrtFloor_succ_sq hx

theorem RoundingMode.sqrtRound_eq_floor_or_succ (mode : RoundingMode) (x : ℚ) :
    mode.sqrtRound x = sqrtFloor x ∨ mode.sqrtRound x = sqrtFloor x + 1 := by
  simp only [sqrtRound]
  split <;> simp

theorem RoundingMode.sqrtRound_le_floor_add_one (mode : RoundingMode) (x : ℚ) :
    mode.sqrtRound x ≤ sqrtFloor x + 1 := by
  rcases mode.sqrtRound_eq_floor_or_succ x with h | h <;> omega

/-- Integer squares yield their exact nonnegative roots in all five rounding modes. -/
theorem RoundingMode.sqrtRound_nat_sq (mode : RoundingMode) (n : Nat) :
    mode.sqrtRound ((n : ℚ) ^ 2) = n := by
  have hf : sqrtFloor ((n : ℚ) ^ 2) = n := by
    unfold sqrtFloor
    rw [← Nat.cast_pow, Nat.floor_natCast, Nat.sqrt_eq']
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have h : ¬(2 * (n : ℚ) + 1) ^ 2 ≤ 4 * (n : ℚ) ^ 2 := by nlinarith
  have h' : ¬(2 * (n : ℚ) + 1) ^ 2 = 4 * (n : ℚ) ^ 2 := by nlinarith
  cases mode <;> simp [sqrtRound, hf, sqrtIncrement, h, h', not_lt_of_ge (le_of_not_ge h)]

/-- The square of an exact half-integer lies between the same two integer squares. -/
theorem sqrtFloor_midpoint_sq (n : Nat) :
    sqrtFloor (((n : ℚ) + 1 / 2) ^ 2) = n := by
  apply Eq.symm
  apply Nat.eq_sqrt'.mpr
  constructor
  · apply Nat.le_floor
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℚ) n]
  · apply (Nat.floor_lt (sq_nonneg _)).mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℚ) n]

theorem sqrtRound_nearestEven_midpoint (n : Nat) :
    RoundingMode.nearestEven.sqrtRound (((n : ℚ) + 1 / 2) ^ 2) =
      if n % 2 = 1 then n + 1 else n := by
  have he : (2 * (n : ℚ) + 1) ^ 2 = 4 * ((n : ℚ) + 1 / 2) ^ 2 := by ring
  simp only [RoundingMode.sqrtRound, sqrtFloor_midpoint_sq, RoundingMode.sqrtIncrement,
    he, lt_self_iff_false, true_and, false_or, decide_eq_true_eq]

theorem sqrtRound_nearestAway_midpoint (n : Nat) :
    RoundingMode.nearestAway.sqrtRound (((n : ℚ) + 1 / 2) ^ 2) = n + 1 := by
  have he : (2 * (n : ℚ) + 1) ^ 2 = 4 * ((n : ℚ) + 1 / 2) ^ 2 := by ring
  simp only [RoundingMode.sqrtRound, sqrtFloor_midpoint_sq, RoundingMode.sqrtIncrement,
    he, le_refl, decide_true, ↓reduceIte]

/-- All five modes return a root less than one integer grid unit from the exact root. -/
theorem sqrtRound_error_lt_one (mode : RoundingMode) {x : ℚ} (hx : 0 ≤ x) :
    |(mode.sqrtRound x : ℝ) - Real.sqrt (x : ℝ)| < 1 := by
  have hlo := sqrtFloor_le_sqrt hx
  have hhi := sqrt_lt_sqrtFloor_succ hx
  by_cases he : (sqrtFloor x : ℝ) = Real.sqrt (x : ℝ)
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ x by exact_mod_cast hx)
    rw [← he] at hs
    have hq : (sqrtFloor x : ℚ) ^ 2 = x := by exact_mod_cast hs
    have hr : mode.sqrtRound x = sqrtFloor x := by
      conv_lhs => rw [← hq]
      exact mode.sqrtRound_nat_sq _
    rw [hr, he]
    norm_num
  · have hlt := lt_of_le_of_ne hlo he
    rcases mode.sqrtRound_eq_floor_or_succ x with h | h
    · rw [h, abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith
    · rw [h, Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
      linarith

/-- The exact square test determines which side of the real midpoint contains the root. -/
theorem sqrtRound_error_le_half (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) {x : ℚ} (hx : 0 ≤ x) :
    |(mode.sqrtRound x : ℝ) - Real.sqrt (x : ℝ)| ≤ 1 / 2 := by
  have hlo := sqrtFloor_le_sqrt hx
  have hhi := sqrt_lt_sqrtFloor_succ hx
  have upper (h : (2 * (sqrtFloor x : ℚ) + 1) ^ 2 ≤ 4 * x) :
      (sqrtFloor x : ℝ) + 1 / 2 ≤ Real.sqrt (x : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have hc : (2 * (sqrtFloor x : ℝ) + 1) ^ 2 ≤ 4 * (x : ℝ) := by
      exact_mod_cast h
    nlinarith
  have lower (h : 4 * x ≤ (2 * (sqrtFloor x : ℚ) + 1) ^ 2) :
      Real.sqrt (x : ℝ) ≤ (sqrtFloor x : ℝ) + 1 / 2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hc : 4 * (x : ℝ) ≤ (2 * (sqrtFloor x : ℝ) + 1) ^ 2 := by
      exact_mod_cast h
    nlinarith
  rcases hm with rfl | rfl
  · simp only [RoundingMode.sqrtRound, RoundingMode.sqrtIncrement, decide_eq_true_eq]
    split
    · rename_i h
      have hmid := upper (by rcases h with h | h; exact h.le; exact h.1.le)
      rw [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
      linarith
    · rename_i h
      have hmid := lower (le_of_not_gt fun ht => h (Or.inl ht))
      rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith
  · simp only [RoundingMode.sqrtRound, RoundingMode.sqrtIncrement, decide_eq_true_eq]
    split
    · rename_i h
      have hmid := upper h
      rw [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
      linarith
    · rename_i h
      have hmid := lower (le_of_not_ge h)
      rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith

theorem sqrtRound_towardZero_le {x : ℚ} (hx : 0 ≤ x) :
    (RoundingMode.towardZero.sqrtRound x : ℝ) ≤ Real.sqrt (x : ℝ) :=
  sqrtFloor_le_sqrt hx

theorem sqrtRound_towardNegative_le {x : ℚ} (hx : 0 ≤ x) :
    (RoundingMode.towardNegative.sqrtRound x : ℝ) ≤ Real.sqrt (x : ℝ) :=
  sqrtFloor_le_sqrt hx

theorem le_sqrtRound_towardPositive {x : ℚ} (hx : 0 ≤ x) :
    Real.sqrt (x : ℝ) ≤ (RoundingMode.towardPositive.sqrtRound x : ℝ) := by
  have hlo := sqrtFloor_sq_le hx
  have hhi := sqrt_lt_sqrtFloor_succ hx
  simp only [RoundingMode.sqrtRound, RoundingMode.sqrtIncrement, decide_eq_true_eq]
  split
  · push_cast
    exact hhi.le
  · rename_i h
    apply (Real.sqrt_le_left (Nat.cast_nonneg _)).mpr
    exact_mod_cast le_of_not_gt h

end FloatLib.Floats.Formats.DecimalInterchange
