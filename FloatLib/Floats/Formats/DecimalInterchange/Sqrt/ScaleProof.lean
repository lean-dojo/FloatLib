/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.FormatProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Coefficient range for decimal square root

Halving the base-ten logarithm of the squared scaled value determines the
square-root grid. The proofs use integer logarithm bounds, without approximating
the square root.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem sqrtScaleShift_upper (p : Nat) {x : ℚ} (hx : 0 ≤ x) :
    x < (10 : ℚ) ^ (2 * (p + sqrtScaleShift p x)) := by
  have hl := Nat.lt_pow_succ_log_self (by decide : 1 < 10) ⌊x⌋₊
  have hf : x < ((10 ^ (Nat.log 10 ⌊x⌋₊ + 1) : Nat) : ℚ) :=
    (Nat.floor_lt hx).mp hl
  have hc : x < (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊ + 1) := by exact_mod_cast hf
  apply hc.trans_le
  apply pow_le_pow_right₀ (by norm_num)
  unfold sqrtScaleShift
  omega

theorem sqrtQuantum_ge_min (f : Format) (x : ℚ) : f.minQuantum ≤ sqrtQuantum f x := by
  unfold sqrtQuantum
  omega

/-- A fitting square bounds the grid shift without computing its root. -/
theorem sqrtScaleShift_le_of_lt {p k : Nat} (hp : 0 < p) {x : ℚ} (hx : 0 ≤ x)
    (h : x < (10 : ℚ) ^ (2 * (p + k))) : sqrtScaleShift p x ≤ k := by
  by_cases hz : ⌊x⌋₊ = 0
  · simp only [sqrtScaleShift, hz, Nat.log_zero_right]
    omega
  have hf : ⌊x⌋₊ < 10 ^ (2 * (p + k)) :=
    (Nat.floor_lt hx).mpr (by exact_mod_cast h)
  have hl := (Nat.log_lt_iff_lt_pow (by decide : 1 < 10) hz).mpr hf
  unfold sqrtScaleShift
  omega

/-- Every valid representation of an exact root is on a grid no finer than the selected grid. -/
theorem sqrtQuantum_le_of_valid (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hvalid : (Datum.finite s c q).Valid f) :
    sqrtQuantum f (((c : ℚ) * (10 : ℚ) ^ q) ^ 2) ≤ q := by
  have hcq := (Datum.valid_quantum_iff ..).mp hvalid
  let k := (q - f.minQuantum).toNat
  have hk : f.minQuantum + (k : Int) = q := by omega
  have hu : 0 < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have hscale : ((c : ℚ) * (10 : ℚ) ^ q) ^ 2 /
      (10 : ℚ) ^ (2 * f.minQuantum) = ((c : ℚ) * (10 : ℚ) ^ k) ^ 2 := by
    have he : (10 : ℚ) ^ (2 * f.minQuantum) = ((10 : ℚ) ^ f.minQuantum) ^ 2 := by
      rw [mul_comm 2 f.minQuantum, zpow_mul]
      norm_num
    rw [← hk, zpow_add₀ (by norm_num), zpow_natCast, he]
    field_simp
  have hc : (c : ℚ) < (10 : ℚ) ^ f.precision := by
    exact_mod_cast (show c < 10 ^ f.precision by
      simpa [Format.coefficientBound_eq] using hcq.1)
  have hroot : (c : ℚ) * (10 : ℚ) ^ k < (10 : ℚ) ^ (f.precision + k) := by
    rw [pow_add]
    exact mul_lt_mul_of_pos_right hc (pow_pos (by norm_num) _)
  have hbound : ((c : ℚ) * (10 : ℚ) ^ k) ^ 2 <
      (10 : ℚ) ^ (2 * (f.precision + k)) := by
    rw [Nat.mul_comm 2, pow_mul]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) c)
      (pow_nonneg (by norm_num : (0 : ℚ) ≤ 10) k)]
  have hp := f.precision_pos
  have h := sqrtScaleShift_le_of_lt hp
    (sq_nonneg ((c : ℚ) * (10 : ℚ) ^ k)) hbound
  unfold sqrtQuantum
  rw [hscale]
  omega

/-- The square of the scaled coefficient is strictly below the squared coefficient bound. -/
theorem div_sqrtQuantum_lt (f : Format) {x : ℚ} (hx : 0 ≤ x) :
    x / (10 : ℚ) ^ (2 * sqrtQuantum f x) < (f.coefficientBound : ℚ) ^ 2 := by
  have hu : 0 < (10 : ℚ) ^ (2 * f.minQuantum) := zpow_pos (by norm_num) _
  have h := sqrtScaleShift_upper f.precision (div_nonneg hx hu.le)
  rw [div_lt_iff₀ hu] at h
  let k := sqrtScaleShift f.precision (x / (10 : ℚ) ^ (2 * f.minQuantum))
  have he : 2 * sqrtQuantum f x = 2 * f.minQuantum + ((2 * k : Nat) : Int) := by
    simp only [sqrtQuantum, k, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he, zpow_add₀ (by norm_num), zpow_natCast]
  apply (div_lt_iff₀ (mul_pos hu (pow_pos (by norm_num) _))).mpr
  rw [Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (10 : ℚ) ^ (2 * (f.precision + k)) =
      ((10 : ℚ) ^ f.precision) ^ 2 * (10 : ℚ) ^ (2 * k) := by
    rw [Nat.mul_add, pow_add, Nat.mul_comm 2 f.precision, pow_mul]
  change x < (10 : ℚ) ^ (2 * (f.precision + k)) *
    (10 : ℚ) ^ (2 * f.minQuantum) at h
  rw [hp] at h
  nlinarith [h]

/-- A nonzero square-root grid shift retains a full leading digit before rounding. -/
theorem sqrtScaleShift_lower {p : Nat} (hp : 0 < p) {x : ℚ} (hx : 0 ≤ x)
    (hk : 0 < sqrtScaleShift p x) :
    (10 : ℚ) ^ (2 * (p + sqrtScaleShift p x - 1)) ≤ x := by
  have hlog : 2 * (p + sqrtScaleShift p x - 1) ≤ Nat.log 10 ⌊x⌋₊ := by
    unfold sqrtScaleShift at *
    omega
  by_cases hz : ⌊x⌋₊ = 0
  · simp [hz, sqrtScaleShift] at hk
    omega
  have hl := Nat.pow_log_le_self 10 hz
  have hpow : (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊) ≤ (⌊x⌋₊ : ℚ) := by exact_mod_cast hl
  exact ((pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 10) hlog).trans hpow).trans
    (Nat.floor_le hx)

/-- Above the subnormal grid, the scaled radicand is at least the square of a full leading digit. -/
theorem payloadBound_sq_le_div_sqrtQuantum (f : Format) {x : ℚ} (hx : 0 ≤ x)
    (hq : f.minQuantum < sqrtQuantum f x) :
    (f.payloadBound : ℚ) ^ 2 ≤ x / (10 : ℚ) ^ (2 * sqrtQuantum f x) := by
  have hu : 0 < (10 : ℚ) ^ (2 * f.minQuantum) := zpow_pos (by norm_num) _
  let k := sqrtScaleShift f.precision (x / (10 : ℚ) ^ (2 * f.minQuantum))
  have hk : 0 < k := by unfold sqrtQuantum at hq; omega
  have hp := f.precision_pos
  have h := sqrtScaleShift_lower hp (div_nonneg hx hu.le) hk
  have he : 2 * (f.precision + k - 1) = (f.precision - 1) * 2 + 2 * k := by omega
  have hb := f.payloadBound_eq
  change (10 : ℚ) ^ (2 * (f.precision + k - 1)) ≤ x / (10 : ℚ) ^ (2 * f.minQuantum) at h
  rw [he, pow_add, pow_mul, le_div_iff₀ hu] at h
  have hq' : 2 * sqrtQuantum f x = 2 * f.minQuantum + ((2 * k : Nat) : Int) := by
    simp only [sqrtQuantum, k, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hq', zpow_add₀ (by norm_num), zpow_natCast, hb, Nat.cast_pow, Nat.cast_ofNat]
  apply (le_div_iff₀ (mul_pos hu (pow_pos (by norm_num) _))).mpr
  nlinarith [h]

end FloatLib.Floats.Formats.DecimalInterchange
