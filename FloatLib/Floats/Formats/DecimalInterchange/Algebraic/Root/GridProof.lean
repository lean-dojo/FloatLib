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

/-- The executable integer root of the rational floor agrees with Mathlib's `Nat.nthRoot`. -/
theorem rootFloor_eq_nthRoot (degree : Nat) (radicand : ℚ) :
    rootFloor degree radicand = Nat.nthRoot degree ⌊radicand⌋₊ :=
  Numerics.IntegerRoot.root_eq_nthRoot degree _

/-- The nonnegative real root used in the numerical specifications. -/
noncomputable def realRoot (degree : Nat) (x : ℝ) : ℝ := x ^ (degree : ℝ)⁻¹

/-- The real root of a nonnegative number is nonnegative. -/
theorem realRoot_nonneg (degree : Nat) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realRoot degree x :=
  Real.rpow_nonneg hx _

/-- For a positive degree, raising the real root of a nonnegative number to the degree recovers the
number. -/
theorem realRoot_pow {degree : Nat} (hn : degree ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    realRoot degree x ^ degree = x :=
  Real.rpow_inv_natCast_pow hx hn

/-- For a positive degree and nonnegative numbers, `a` is at most the real root of `x` exactly when
`a ^ degree ≤ x`, so root bounds reduce to exact power comparisons. -/
theorem le_realRoot_iff {degree : Nat} (hn : degree ≠ 0) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) :
    a ≤ realRoot degree x ↔ a ^ degree ≤ x := by
  rw [← pow_le_pow_iff_left₀ ha (realRoot_nonneg degree hx) hn, realRoot_pow hn hx]

/-- For a positive degree and nonnegative numbers, the real root of `x` is at most `a` exactly when
`x ≤ a ^ degree`. -/
theorem realRoot_le_iff {degree : Nat} (hn : degree ≠ 0) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) :
    realRoot degree x ≤ a ↔ x ≤ a ^ degree := by
  rw [← pow_le_pow_iff_left₀ (realRoot_nonneg degree hx) ha hn, realRoot_pow hn hx]

/-- For a positive degree and nonnegative numbers, the real root of `x` is below `a` exactly when
`x < a ^ degree`. -/
theorem realRoot_lt_iff {degree : Nat} (hn : degree ≠ 0) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) :
    realRoot degree x < a ↔ x < a ^ degree := by
  rw [← pow_lt_pow_iff_left₀ (realRoot_nonneg degree hx) ha hn, realRoot_pow hn hx]

/-- For a positive degree, the integer root floor raised to the degree does not exceed the
nonnegative rational radicand. -/
theorem rootFloor_pow_le {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    (rootFloor degree x : ℚ) ^ degree ≤ x := by
  have h : (rootFloor degree x : ℚ) ^ degree ≤ (⌊x⌋₊ : ℚ) := by
    rw [rootFloor_eq_nthRoot]
    exact_mod_cast (Nat.pow_nthRoot_le_iff.mpr (Or.inl hn) :
      Nat.nthRoot degree ⌊x⌋₊ ^ degree ≤ ⌊x⌋₊)
  exact h.trans (Nat.floor_le hx)

/-- For a positive degree, the successor of the integer root floor raised to the degree exceeds the
rational radicand. -/
theorem lt_rootFloor_succ_pow {degree : Nat} (hn : degree ≠ 0)
    (x : ℚ) : x < ((rootFloor degree x : ℚ) + 1) ^ degree := by
  rcases lt_or_ge x 0 with hx | hx
  · exact hx.trans (by positivity)
  rw [rootFloor_eq_nthRoot]
  have h := (Nat.floor_lt hx).mp (Nat.lt_pow_nthRoot_add_one hn ⌊x⌋₊)
  exact_mod_cast h

/-- The integer root floor is a lower bound on the real root of a nonnegative rational. -/
theorem rootFloor_le_realRoot {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) : (rootFloor degree x : ℝ) ≤ realRoot degree (x : ℝ) := by
  apply (le_realRoot_iff hn (by exact_mod_cast hx) (Nat.cast_nonneg _)).mpr
  exact_mod_cast rootFloor_pow_le hn hx

/-- The real root of a nonnegative rational is strictly below the successor of its integer root
floor. -/
theorem realRoot_lt_rootFloor_succ {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    realRoot degree (x : ℝ) < (rootFloor degree x : ℝ) + 1 := by
  apply (realRoot_lt_iff hn (by exact_mod_cast hx) (by positivity)).mpr
  exact_mod_cast lt_rootFloor_succ_pow hn x

/-- Root rounding picks one of the two integers bracketing the root: the integer root floor or its
successor. -/
theorem RoundingMode.rootRound_eq_floor_or_succ (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) :
    mode.rootRound s degree x = rootFloor degree x ∨
      mode.rootRound s degree x = rootFloor degree x + 1 := by
  simp only [rootRound]
  split <;> simp

/-- Root rounding never exceeds the successor of the integer root floor. -/
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

/-- Doubling the midpoint `a + 1/2` before taking a power scales the power by `2 ^ degree`, which is
how the midpoint tests compare integer powers. -/
private theorem two_mul_add_one_pow (degree : Nat) (a : ℚ) :
    (2 * a + 1) ^ degree = (2 : ℚ) ^ degree * (a + 1 / 2) ^ degree := by
  rw [← mul_pow]
  congr 1
  ring

/-- For a positive degree, the integer root floor of the power of a midpoint `k + 1/2` is `k`. -/
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

/-- A tie, a radicand equal to the power of a midpoint `k + 1/2`, rounds to the even neighbor under
nearest-even, whatever the sign. -/
theorem rootRound_nearest_midpoint (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) (k : Nat) :
    RoundingMode.nearest.rootRound s degree (((k : ℚ) + 1 / 2) ^ degree) =
      if k % 2 = 1 then k + 1 else k := by
  simp only [RoundingMode.rootRound, rootFloor_midpoint_pow hn,
    RoundingMode.rootIncrement, two_mul_add_one_pow, lt_self_iff_false, true_and, false_or,
    decide_eq_true_eq]

/-- A tie, a radicand equal to the power of a midpoint `k + 1/2`, rounds up in magnitude to `k + 1`
under nearest-away, whatever the sign. -/
theorem rootRound_nearestAway_midpoint (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) (k : Nat) :
    RoundingMode.nearestAway.rootRound s degree (((k : ℚ) + 1 / 2) ^ degree) = k + 1 := by
  simp only [RoundingMode.rootRound, rootFloor_midpoint_pow hn,
    RoundingMode.rootIncrement, two_mul_add_one_pow, le_refl, decide_true, ↓reduceIte]

/-- In every rounding mode, the rounded integer root is less than one unit from the real root of a
nonnegative rational. -/
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

/-- An integer adjacent to the root and on the root's side of the midpoint, as decided by the exact
power test, is within half a unit of the real root. -/
private theorem abs_sub_realRoot_le_half {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x)
    {k : Nat}
    (h : k = rootFloor degree x + 1 ∧
        (2 * (rootFloor degree x : ℚ) + 1) ^ degree ≤ 2 ^ degree * x ∨
      k = rootFloor degree x ∧
        2 ^ degree * x ≤ (2 * (rootFloor degree x : ℚ) + 1) ^ degree) :
    |(k : ℝ) - realRoot degree (x : ℝ)| ≤ 1 / 2 := by
  have hlo := rootFloor_le_realRoot hn hx
  have hhi := realRoot_lt_rootFloor_succ hn hx
  have h2 := pow_pos (by norm_num : (0 : ℚ) < 2) degree
  have hcast : ((((rootFloor degree x : ℚ) + 1 / 2) ^ degree : ℚ) : ℝ) =
      ((rootFloor degree x : ℝ) + 1 / 2) ^ degree := by
    simp only [Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat]
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [two_mul_add_one_pow] at h
    have hmid : (rootFloor degree x : ℝ) + 1 / 2 ≤ realRoot degree (x : ℝ) := by
      apply (le_realRoot_iff hn (by exact_mod_cast hx) (by positivity)).mpr
      rw [← hcast]
      exact Rat.cast_le.mpr ((mul_le_mul_iff_right₀ h2).mp h)
    rw [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by linarith)]
    linarith
  · rw [two_mul_add_one_pow] at h
    have hmid : realRoot degree (x : ℝ) ≤ (rootFloor degree x : ℝ) + 1 / 2 := by
      apply (realRoot_le_iff hn (by exact_mod_cast hx) (by positivity)).mpr
      rw [← hcast]
      exact Rat.cast_le.mpr ((mul_le_mul_iff_right₀ h2).mp h)
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith

/-- Exact power comparisons imply the nearest-mode half-grid error bound. -/
theorem rootRound_error_le_half (mode : RoundingMode) (s : Bool)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    |(mode.rootRound s degree x : ℝ) - realRoot degree (x : ℝ)| ≤ 1 / 2 := by
  apply abs_sub_realRoot_le_half hn hx
  rcases hm with rfl | rfl <;>
    simp only [RoundingMode.rootRound, RoundingMode.rootIncrement, decide_eq_true_eq] <;>
    split <;> rename_i h
  · exact Or.inl ⟨rfl, by rcases h with h | h; exact h.le; exact h.1.le⟩
  · exact Or.inr ⟨rfl, le_of_not_gt fun ht => h (Or.inl ht)⟩
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, le_of_not_ge h⟩

/-- Rounding toward zero truncates: the rounded integer root never exceeds the real root. -/
theorem rootRound_towardZero_le (s : Bool) {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    (RoundingMode.towardZero.rootRound s degree x : ℝ) ≤ realRoot degree (x : ℝ) :=
  rootFloor_le_realRoot hn hx

/-- The directed mode that moves the signed result toward zero (toward positive for a negative
result, toward negative for a positive one) rounds the root magnitude down, to at most the real
root. -/
theorem rootRound_directed_down_le (s : Bool) {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    ((if s then RoundingMode.up else .down).rootRound
      s degree x : ℝ) ≤ realRoot degree (x : ℝ) := by
  cases s <;> exact rootFloor_le_realRoot hn hx

/-- The directed mode that moves the signed result away from zero (toward negative for a negative
result, toward positive for a positive one) rounds the root magnitude up, to at least the real root.
-/
theorem le_rootRound_directed_up (s : Bool) {degree : Nat} (hn : degree ≠ 0)
    {x : ℚ} (hx : 0 ≤ x) :
    realRoot degree (x : ℝ) ≤
      ((if s then RoundingMode.down else .up).rootRound
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
