/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Runtime
public import FloatLib.Kernels.IntegerRoot.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rounding an integer-degree root on the coefficient grid

The integer root of the rational floor brackets the nonnegative real root.
Exact powers compare that root with integer coefficients and their midpoints.
The degree is any positive natural number.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem rootFloor_eq_nthRoot (degree : Nat) (radicand : ℚ) :
    rootFloor degree radicand = Nat.nthRoot degree ⌊radicand⌋₊ :=
  Numerics.IntegerRoot.root_eq_nthRoot degree _

/-- The nonnegative real root used in the numerical specifications. -/
noncomputable def realRoot (degree : Nat) (x : ℝ) : ℝ := x ^ (degree : ℝ)⁻¹

theorem realRoot_nonneg (degree : Nat) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realRoot degree x :=
  Real.rpow_nonneg hx _

theorem realRoot_pow {degree : Nat} (hn : degree ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    realRoot degree x ^ degree = x :=
  Real.rpow_inv_natCast_pow hx hn

theorem le_realRoot_iff {degree : Nat} (hn : degree ≠ 0) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) :
    a ≤ realRoot degree x ↔ a ^ degree ≤ x := by
  rw [← pow_le_pow_iff_left₀ ha (realRoot_nonneg degree hx) hn, realRoot_pow hn hx]

theorem realRoot_le_iff {degree : Nat} (hn : degree ≠ 0) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) :
    realRoot degree x ≤ a ↔ x ≤ a ^ degree := by
  rw [← pow_le_pow_iff_left₀ (realRoot_nonneg degree hx) ha hn, realRoot_pow hn hx]

theorem realRoot_lt_iff {degree : Nat} (hn : degree ≠ 0) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) :
    realRoot degree x < a ↔ x < a ^ degree := by
  rw [← pow_lt_pow_iff_left₀ (realRoot_nonneg degree hx) ha hn, realRoot_pow hn hx]

theorem rootFloor_pow_le {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    (rootFloor degree x : ℚ) ^ degree ≤ x := by
  have h : (rootFloor degree x : ℚ) ^ degree ≤ (⌊x⌋₊ : ℚ) := by
    rw [rootFloor_eq_nthRoot]
    exact_mod_cast (Nat.pow_nthRoot_le_iff.mpr (Or.inl hn) :
      Nat.nthRoot degree ⌊x⌋₊ ^ degree ≤ ⌊x⌋₊)
  exact h.trans (Nat.floor_le hx)

theorem lt_rootFloor_succ_pow {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) : x < ((rootFloor degree x : ℚ) + 1) ^ degree := by
  rw [rootFloor_eq_nthRoot]
  have h := (Nat.floor_lt hx).mp (Nat.lt_pow_nthRoot_add_one hn ⌊x⌋₊)
  exact_mod_cast h

theorem rootFloor_le_realRoot {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) : (rootFloor degree x : ℝ) ≤ realRoot degree (x : ℝ) := by
  apply (le_realRoot_iff hn (by exact_mod_cast hx) (Nat.cast_nonneg _)).mpr
  exact_mod_cast rootFloor_pow_le hn hx

theorem realRoot_lt_rootFloor_succ {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    realRoot degree (x : ℝ) < (rootFloor degree x : ℝ) + 1 := by
  apply (realRoot_lt_iff hn (by exact_mod_cast hx) (by positivity)).mpr
  exact_mod_cast lt_rootFloor_succ_pow hn hx

theorem RoundingMode.rootRound_eq_floor_or_succ (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) :
    mode.rootRound s degree x = rootFloor degree x ∨
      mode.rootRound s degree x = rootFloor degree x + 1 := by
  simp only [rootRound]
  split <;> simp

theorem RoundingMode.rootRound_le_floor_add_one (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) :
    mode.rootRound s degree x ≤ rootFloor degree x + 1 := by
  rcases mode.rootRound_eq_floor_or_succ s degree x with h | h <;> omega

/-- Exact integer roots stay exact in every mode, with either output sign. -/
theorem RoundingMode.rootRound_nat_pow (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) (k : Nat) :
    mode.rootRound s degree ((k : ℚ) ^ degree) = k := by
  have hf : rootFloor degree ((k : ℚ) ^ degree) = k := by
    rw [rootFloor_eq_nthRoot, ← Nat.cast_pow, Nat.floor_natCast, Nat.nthRoot_pow hn]
  have hlt : (2 : ℚ) ^ degree * (k : ℚ) ^ degree <
      (2 * (k : ℚ) + 1) ^ degree := by
    rw [← mul_pow]
    exact pow_lt_pow_left₀ (by linarith) (by positivity) hn
  cases mode <;> simp [rootRound, hf, rootIncrement, not_le.mpr hlt,
    ne_of_gt hlt, not_lt.mpr hlt.le]

theorem rootFloor_midpoint_pow {degree : Nat} (hn : degree ≠ 0) (k : Nat) :
    rootFloor degree (((k : ℚ) + 1 / 2) ^ degree) = k := by
  rw [rootFloor_eq_nthRoot]
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.nthRoot_lt_iff hn).mpr
    apply (Nat.floor_lt (pow_nonneg (by positivity) _)).mpr
    push_cast
    exact pow_lt_pow_left₀ (by linarith) (by positivity) hn
  · apply (Nat.le_nthRoot_iff hn).mpr
    apply Nat.le_floor
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) _

theorem rootRound_nearestEven_midpoint (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) (k : Nat) :
    RoundingMode.nearestEven.rootRound s degree (((k : ℚ) + 1 / 2) ^ degree) =
      if k % 2 = 1 then k + 1 else k := by
  have he : (2 * (k : ℚ) + 1) ^ degree =
      (2 : ℚ) ^ degree * ((k : ℚ) + 1 / 2) ^ degree := by
    rw [← mul_pow]
    congr 1
    ring
  simp only [RoundingMode.rootRound, rootFloor_midpoint_pow hn,
    RoundingMode.rootIncrement, he, lt_self_iff_false, true_and, false_or,
    decide_eq_true_eq]

theorem rootRound_nearestAway_midpoint (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) (k : Nat) :
    RoundingMode.nearestAway.rootRound s degree (((k : ℚ) + 1 / 2) ^ degree) = k + 1 := by
  have he : (2 * (k : ℚ) + 1) ^ degree =
      (2 : ℚ) ^ degree * ((k : ℚ) + 1 / 2) ^ degree := by
    rw [← mul_pow]
    congr 1
    ring
  simp only [RoundingMode.rootRound, rootFloor_midpoint_pow hn,
    RoundingMode.rootIncrement, he, le_refl, decide_true, ↓reduceIte]

theorem rootRound_error_lt_one (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    |(mode.rootRound s degree x : ℝ) - realRoot degree (x : ℝ)| < 1 := by
  have hlo := rootFloor_le_realRoot hn hx
  have hhi := realRoot_lt_rootFloor_succ hn hx
  by_cases he : (rootFloor degree x : ℝ) = realRoot degree (x : ℝ)
  · have hp := realRoot_pow hn (show (0 : ℝ) ≤ x by exact_mod_cast hx)
    rw [← he] at hp
    have hq : (rootFloor degree x : ℚ) ^ degree = x := by exact_mod_cast hp
    have hr : mode.rootRound s degree x = rootFloor degree x := by
      conv_lhs => rw [← hq]
      exact mode.rootRound_nat_pow s hn _
    rw [hr, he]
    norm_num
  · have hlt := lt_of_le_of_ne hlo he
    rcases mode.rootRound_eq_floor_or_succ s degree x with h | h
    · rw [h, abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith
    · rw [h, Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
      linarith

/-- Exact power comparisons imply the nearest-mode half-grid error bound. -/
theorem rootRound_error_le_half (mode : RoundingMode) (s : Bool)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    |(mode.rootRound s degree x : ℝ) - realRoot degree (x : ℝ)| ≤ 1 / 2 := by
  have hlo := rootFloor_le_realRoot hn hx
  have hhi := realRoot_lt_rootFloor_succ hn hx
  have he : (2 * (rootFloor degree x : ℚ) + 1) ^ degree =
      (2 : ℚ) ^ degree * ((rootFloor degree x : ℚ) + 1 / 2) ^ degree := by
    rw [← mul_pow]
    congr 1
    ring
  have upper (h : (2 * (rootFloor degree x : ℚ) + 1) ^ degree ≤ 2 ^ degree * x) :
      (rootFloor degree x : ℝ) + 1 / 2 ≤ realRoot degree (x : ℝ) := by
    rw [he] at h
    have h' := (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℚ) < 2) degree)).mp h
    apply (le_realRoot_iff hn (by exact_mod_cast hx) (by positivity)).mpr
    have hc : ((((rootFloor degree x : ℚ) + 1 / 2) ^ degree : ℚ) : ℝ) ≤ (x : ℝ) :=
      Rat.cast_le.mpr h'
    simpa only [Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hc
  have lower (h : 2 ^ degree * x ≤ (2 * (rootFloor degree x : ℚ) + 1) ^ degree) :
      realRoot degree (x : ℝ) ≤ (rootFloor degree x : ℝ) + 1 / 2 := by
    rw [he] at h
    have h' := (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℚ) < 2) degree)).mp h
    apply (realRoot_le_iff hn (by exact_mod_cast hx) (by positivity)).mpr
    have hc : (x : ℝ) ≤ ((((rootFloor degree x : ℚ) + 1 / 2) ^ degree : ℚ) : ℝ) :=
      Rat.cast_le.mpr h'
    simpa only [Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hc
  rcases hm with rfl | rfl
  · simp only [RoundingMode.rootRound, RoundingMode.rootIncrement, decide_eq_true_eq]
    split
    · rename_i h
      have hmid := upper (by rcases h with h | h; exact h.le; exact h.1.le)
      rw [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
      linarith
    · rename_i h
      have hmid := lower (le_of_not_gt fun ht => h (Or.inl ht))
      rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith
  · simp only [RoundingMode.rootRound, RoundingMode.rootIncrement, decide_eq_true_eq]
    split
    · rename_i h
      have hmid := upper h
      rw [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
      linarith
    · rename_i h
      have hmid := lower (le_of_not_ge h)
      rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith

theorem rootRound_towardZero_le (s : Bool) {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    (RoundingMode.towardZero.rootRound s degree x : ℝ) ≤ realRoot degree (x : ℝ) :=
  rootFloor_le_realRoot hn hx

theorem rootRound_directed_down_le (s : Bool) {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    ((if s then RoundingMode.towardPositive else .towardNegative).rootRound
      s degree x : ℝ) ≤ realRoot degree (x : ℝ) := by
  cases s <;> exact rootFloor_le_realRoot hn hx

theorem le_rootRound_directed_up (s : Bool) {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    realRoot degree (x : ℝ) ≤
      ((if s then RoundingMode.towardNegative else .towardPositive).rootRound
        s degree x : ℝ) := by
  have hhi := realRoot_lt_rootFloor_succ hn hx
  have hfloor (h : ¬(rootFloor degree x : ℚ) ^ degree < x) :
      realRoot degree (x : ℝ) ≤ (rootFloor degree x : ℝ) := by
    apply (realRoot_le_iff hn (by exact_mod_cast hx) (Nat.cast_nonneg _)).mpr
    exact_mod_cast le_of_not_gt h
  cases s <;>
    simp only [Bool.false_eq_true, ↓reduceIte, RoundingMode.rootRound,
      RoundingMode.rootIncrement, Bool.not_false, Bool.true_and,
      decide_eq_true_eq] <;>
    split
  all_goals first
    | simpa only [Nat.cast_add, Nat.cast_one] using hhi.le
    | exact hfloor ‹_›

end FloatLib.Floats.Formats.DecimalInterchange
