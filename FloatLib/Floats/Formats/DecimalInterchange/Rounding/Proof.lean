/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Runtime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Numerical guarantees for exact coefficient rounding

The computed coefficient fixes nonnegative integers, brackets the exact
magnitude, satisfies directed inequalities, and has at most half a grid unit
of error in either nearest mode.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.RoundingMode

@[simp] theorem increment_zero (mode : RoundingMode) (s : Bool) (n : Nat) :
    mode.increment s n 0 = false := by
  cases mode <;> cases s <;> simp [increment]

/-- The integer remainder decision agrees with rounding the exact fractional part. -/
theorem roundMagnitude_eq (mode : RoundingMode) (s : Bool) (x : ℚ) :
    mode.roundMagnitude s x =
      let lower := ⌊x⌋₊
      if mode.increment s lower (x - lower) then lower + 1 else lower := by
  by_cases hx : 0 ≤ x
  · have hn : (x.num.toNat : ℚ) / x.den = x := by
      have hn : (x.num.toNat : ℚ) = (x.num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)
      rw [hn, Rat.num_div_den]
    have hf : ⌊x⌋₊ = x.num.toNat / x.den := by
      conv_lhs => rw [← hn]
      exact Rat.natFloor_natCast_div_natCast _ _
    have hr : x - (⌊x⌋₊ : ℚ) = (x.num.toNat % x.den : Nat) / (x.den : ℚ) := by
      have hr := Int.fract_div_natCast_eq_div_natCast_mod
        (k := ℚ) (m := x.num.toNat) (n := x.den)
      rw [hn, Int.fract, ← Int.natCast_floor_eq_floor hx, Int.cast_natCast] at hr
      exact hr
    have hd : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
    have hlt : (1 < 2 * (x - (⌊x⌋₊ : ℚ))) ↔ x.den < 2 * (x.num.toNat % x.den) := by
      rw [hr, ← mul_div_assoc, one_lt_div hd]
      norm_cast
    have heq : (2 * (x - (⌊x⌋₊ : ℚ)) = 1) ↔ 2 * (x.num.toNat % x.den) = x.den := by
      rw [hr, ← mul_div_assoc, div_eq_one_iff_eq hd.ne']
      norm_cast
    have hle : (1 ≤ 2 * (x - (⌊x⌋₊ : ℚ))) ↔ x.den ≤ 2 * (x.num.toNat % x.den) := by
      rw [hr, ← mul_div_assoc, one_le_div hd]
      norm_cast
    have hpos : (0 < x - (⌊x⌋₊ : ℚ)) ↔ 0 < x.num.toNat % x.den := by
      rw [hr, div_pos_iff_of_pos_right hd]
      exact Nat.cast_pos
    cases mode <;> simp [roundMagnitude, ← hf, increment, hlt, heq, hle, hpos]
  · have hn : x.num.toNat = 0 :=
      Int.toNat_of_nonpos (Rat.num_neg.mpr (lt_of_not_ge hx)).le
    have hf : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (lt_of_not_ge hx).le
    have hlt : ¬(1 < 2 * x) := by linarith
    have heq : ¬(2 * x = 1) := by linarith
    have hle : ¬(1 ≤ 2 * x) := by linarith
    have hpos : ¬(0 < x) := not_lt.mpr (lt_of_not_ge hx).le
    have hd : x.den ≠ 0 := x.den_nz
    cases mode <;> simp [roundMagnitude, increment, hn, hf, hlt, heq, hle, hpos, hd]

/-- Every nonnegative integer is fixed in every rounding direction. -/
@[simp] theorem roundMagnitude_natCast (mode : RoundingMode) (s : Bool) (n : Nat) :
    mode.roundMagnitude s (n : ℚ) = n := by
  simp [roundMagnitude_eq]

/-- The rounded coefficient is one of the two adjacent integer grid points. -/
theorem roundMagnitude_eq_floor_or_succ (mode : RoundingMode) (s : Bool) (x : ℚ) :
    mode.roundMagnitude s x = ⌊x⌋₊ ∨ mode.roundMagnitude s x = ⌊x⌋₊ + 1 := by
  simp only [roundMagnitude_eq]
  split <;> simp

theorem floor_le_roundMagnitude (mode : RoundingMode) (s : Bool) (x : ℚ) :
    ⌊x⌋₊ ≤ mode.roundMagnitude s x := by
  rcases mode.roundMagnitude_eq_floor_or_succ s x with h | h <;> omega

theorem roundMagnitude_le_floor_add_one (mode : RoundingMode) (s : Bool) (x : ℚ) :
    mode.roundMagnitude s x ≤ ⌊x⌋₊ + 1 := by
  rcases mode.roundMagnitude_eq_floor_or_succ s x with h | h <;> omega

/-- A directed or nearest rounding changes a nonnegative value by less than one grid unit. -/
theorem roundMagnitude_error_lt_one (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    |(mode.roundMagnitude s x : ℚ) - x| < 1 := by
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  by_cases heq : x = (⌊x⌋₊ : ℚ)
  · rw [heq, roundMagnitude_natCast]
    simp
  have hlt : (⌊x⌋₊ : ℚ) < x := lt_of_le_of_ne hlo (Ne.symm heq)
  rcases mode.roundMagnitude_eq_floor_or_succ s x with h | h
  · rw [h, abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  · rw [h, Nat.cast_add, Nat.cast_one, abs_of_pos (by linarith)]
    linarith

/-- Both nearest modes have an error of at most half an integer grid unit. -/
theorem roundMagnitude_error_le_half (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    |(mode.roundMagnitude s x : ℚ) - x| ≤ 1 / 2 := by
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  rcases hm with rfl | rfl
  · simp only [roundMagnitude_eq, increment, decide_eq_true_eq]
    split
    · rename_i h
      rw [Nat.cast_add, Nat.cast_one, abs_of_pos (by linarith)]
      rcases h with h | h <;> linarith
    · rename_i h
      have hh : 2 * (x - (⌊x⌋₊ : ℚ)) ≤ 1 := le_of_not_gt fun hh => h (Or.inl hh)
      rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith
  · simp only [roundMagnitude_eq, increment, decide_eq_true_eq]
    split
    · rw [Nat.cast_add, Nat.cast_one, abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith

/-- Rounding toward zero does not increase magnitude. -/
theorem roundMagnitude_towardZero_le (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    ((towardZero.roundMagnitude s x : Nat) : ℚ) ≤ x := by
  simpa [roundMagnitude_eq, increment] using Nat.floor_le hx

/-- Positive upward rounding is an upper enclosure. -/
theorem le_roundMagnitude_towardPositive {x : ℚ} (hx : 0 ≤ x) :
    x ≤ ((towardPositive.roundMagnitude false x : Nat) : ℚ) := by
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  simp only [roundMagnitude_eq, increment, Bool.not_false, Bool.true_and]
  split
  · push_cast
    linarith
  · simp only [decide_eq_true_eq, not_lt] at *
    linarith

/-- Upward rounding is an upper enclosure for either sign. -/
theorem le_roundSigned_towardPositive (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    (if s then -x else x) ≤ towardPositive.roundSigned s x := by
  cases s
  · exact le_roundMagnitude_towardPositive hx
  · simpa [roundSigned, roundMagnitude_eq, increment] using neg_le_neg (Nat.floor_le hx)

/-- Downward rounding is a lower enclosure for either sign. -/
theorem roundSigned_towardNegative_le (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    towardNegative.roundSigned s x ≤ (if s then -x else x) := by
  cases s
  · simpa [roundSigned, roundMagnitude_eq, increment] using Nat.floor_le hx
  · exact neg_le_neg (le_roundMagnitude_towardPositive hx)

/-- At an exact midpoint, nearest-even chooses the even adjacent coefficient. -/
theorem roundMagnitude_nearestEven_midpoint (s : Bool) (n : Nat) :
    nearestEven.roundMagnitude s ((n : ℚ) + 1 / 2) =
      if n % 2 = 1 then n + 1 else n := by
  have hf : ⌊(n : ℚ) + 1 / 2⌋₊ = n := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> linarith
  have hr : (n : ℚ) + 1 / 2 - n = 1 / 2 := by ring
  simp only [roundMagnitude_eq, hf, hr, increment]
  norm_num

/-- Nearest-away increases magnitude at every exact midpoint, for either sign. -/
theorem roundMagnitude_nearestAway_midpoint (s : Bool) (n : Nat) :
    nearestAway.roundMagnitude s ((n : ℚ) + 1 / 2) = n + 1 := by
  have hf : ⌊(n : ℚ) + 1 / 2⌋₊ = n := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> linarith
  have hr : (n : ℚ) + 1 / 2 - n = 1 / 2 := by ring
  simp only [roundMagnitude_eq, hf, hr, increment]
  norm_num

/-- All five modes have strictly less than one decimal grid unit of error. -/
theorem roundAt_error_lt_one (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (q : Int) :
    |(mode.roundAt s x q : ℚ) * (10 : ℚ) ^ q - x| < (10 : ℚ) ^ q := by
  have hu : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) q
  have h := mode.roundMagnitude_error_lt_one s (div_nonneg hx hu.le)
  have heq : (mode.roundAt s x q : ℚ) * (10 : ℚ) ^ q - x =
      ((mode.roundAt s x q : ℚ) - x / (10 : ℚ) ^ q) * (10 : ℚ) ^ q := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hu]
  exact (mul_lt_mul_of_pos_right h hu).trans_eq (one_mul _)

/-- The error bound scales by the actual decimal quantum, for any exponent. -/
theorem roundAt_error_le_half (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (q : Int) :
    |(mode.roundAt s x q : ℚ) * (10 : ℚ) ^ q - x| ≤ (10 : ℚ) ^ q / 2 := by
  have hu : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) q
  have h := mode.roundMagnitude_error_le_half hm s (div_nonneg hx hu.le)
  have heq : (mode.roundAt s x q : ℚ) * (10 : ℚ) ^ q - x =
      ((mode.roundAt s x q : ℚ) - x / (10 : ℚ) ^ q) * (10 : ℚ) ^ q := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hu]
  exact (mul_le_mul_of_nonneg_right h hu.le).trans_eq (by ring)

/-- A finite decimal remains exact on every finer decimal grid. -/
theorem roundAt_exact (mode : RoundingMode) (s : Bool) (c : Nat) {q r : Int} (h : r ≤ q) :
    mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) r = c * 10 ^ (q - r).toNat := by
  have he : r + ((q - r).toNat : Int) = q := by omega
  have hv : (c : ℚ) * (10 : ℚ) ^ q / (10 : ℚ) ^ r =
      ((c * 10 ^ (q - r).toNat : Nat) : ℚ) := by
    conv_lhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
    push_cast
    field_simp
  simp only [roundAt, hv, roundMagnitude_natCast]

/-- Exact grid refinement preserves value in all five modes. -/
theorem roundAt_exact_value (mode : RoundingMode) (s : Bool) (c : Nat)
    {q r : Int} (h : r ≤ q) :
    (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) r : ℚ) * (10 : ℚ) ^ r =
      (c : ℚ) * (10 : ℚ) ^ q := by
  rw [roundAt_exact mode s c h]
  have he : r + ((q - r).toNat : Int) = q := by omega
  conv_rhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
  push_cast
  ring

/-- An integer upper bound on the magnitude remains an upper bound after any rounding. -/
theorem roundMagnitude_le_nat (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (n : Nat) (hn : x ≤ n) : mode.roundMagnitude s x ≤ n := by
  have he := (abs_lt.mp (mode.roundMagnitude_error_lt_one s hx)).2
  have hlt : (mode.roundMagnitude s x : ℚ) < ((n + 1 : Nat) : ℚ) := by
    push_cast
    linarith
  have hnat : mode.roundMagnitude s x < n + 1 := by exact_mod_cast hlt
  omega

end FloatLib.Floats.Formats.DecimalInterchange.RoundingMode
