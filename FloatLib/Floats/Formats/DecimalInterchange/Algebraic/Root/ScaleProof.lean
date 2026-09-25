/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.FormatProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Decimal coefficient range for arbitrary integer-degree roots

Dividing the integer decimal logarithm by the positive degree determines a
fitting root grid. The argument uses exact powers and applies to any format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem rootScaleShift_upper (p : Nat) {degree : Nat} (hn : 0 < degree)
    {x : ℚ} (hx : 0 ≤ x) :
    x < (10 : ℚ) ^ (degree * (p + rootScaleShift p degree x)) := by
  have hl := Nat.lt_pow_succ_log_self (by decide : 1 < 10) ⌊x⌋₊
  have hf : x < ((10 ^ (Nat.log 10 ⌊x⌋₊ + 1) : Nat) : ℚ) :=
    (Nat.floor_lt hx).mp hl
  have hc : x < (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊ + 1) := by exact_mod_cast hf
  apply hc.trans_le
  apply pow_le_pow_right₀ (by norm_num)
  have hd := Nat.lt_mul_div_succ (Nat.log 10 ⌊x⌋₊) hn
  have hp : Nat.log 10 ⌊x⌋₊ / degree + 1 ≤ p + rootScaleShift p degree x := by
    unfold rootScaleShift
    omega
  exact (Nat.succ_le_of_lt hd).trans (Nat.mul_le_mul_left degree hp)

theorem rootQuantum_ge_min (f : Format) (degree : Nat) (x : ℚ) :
    f.minQuantum ≤ rootQuantum f degree x := by
  unfold rootQuantum
  omega

/-- The scaled radicand is strictly below the power of the coefficient bound. -/
theorem div_rootQuantum_lt (f : Format) {degree : Nat} (hn : 0 < degree)
    {x : ℚ} (hx : 0 ≤ x) :
    x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) <
      (f.coefficientBound : ℚ) ^ degree := by
  have hu : 0 < (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := zpow_pos (by norm_num) _
  have h := rootScaleShift_upper f.precision hn (div_nonneg hx hu.le)
  rw [div_lt_iff₀ hu] at h
  let k := rootScaleShift f.precision degree
    (x / (10 : ℚ) ^ ((degree : Int) * f.minQuantum))
  have he : (degree : Int) * rootQuantum f degree x =
      (degree : Int) * f.minQuantum + ((degree * k : Nat) : Int) := by
    simp only [rootQuantum, k, Nat.cast_mul]
    ring
  rw [he, zpow_add₀ (by norm_num), zpow_natCast]
  apply (div_lt_iff₀ (mul_pos hu (pow_pos (by norm_num) _))).mpr
  rw [Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (10 : ℚ) ^ (degree * (f.precision + k)) =
      ((10 : ℚ) ^ f.precision) ^ degree * (10 : ℚ) ^ (degree * k) := by
    rw [Nat.mul_add, pow_add, Nat.mul_comm degree f.precision, pow_mul]
  change x < (10 : ℚ) ^ (degree * (f.precision + k)) *
    (10 : ℚ) ^ ((degree : Int) * f.minQuantum) at h
  rw [hp] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end FloatLib.Floats.Formats.DecimalInterchange
