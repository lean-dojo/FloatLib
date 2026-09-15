/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Scale
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.FormatProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Range guarantees for the selected decimal grid

The input's exact coefficient on the selected grid is less than `10 ^ precision`.
Whenever it is coarser than the subnormal grid, it also retains a full leading
digit. These bounds justify the later single-digit carry and overflow decisions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Zero has no significant digits and therefore uses the least quantum. -/
theorem roundingQuantum_zero (f : Format) : roundingQuantum f 0 = f.minQuantum := by
  simp [roundingQuantum]

/-- The zero shortcut agrees with the digit-count formula for every rational magnitude. -/
theorem roundingQuantum_eq (f : Format) (x : ℚ) :
    roundingQuantum f x =
      f.minQuantum + (scaleShift f.precision (x / (10 : ℚ) ^ f.minQuantum) : Int) := by
  by_cases hx : x = 0
  · have hp : 1 ≤ f.precision := f.precision_pos
    simp [roundingQuantum, hx, scaleShift, Nat.sub_eq_zero_of_le hp]
  · simp [roundingQuantum, hx]

theorem scaleShift_upper (p : Nat) {x : ℚ} (hx : 0 ≤ x) :
    x < (10 : ℚ) ^ (p + scaleShift p x) := by
  have hlog := Nat.lt_pow_succ_log_self (by decide : 1 < 10) ⌊x⌋₊
  have hfloor : x < ((10 ^ (Nat.log 10 ⌊x⌋₊ + 1) : Nat) : ℚ) :=
    (Nat.floor_lt hx).mp hlog
  have hpow : (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊ + 1) ≤
      (10 : ℚ) ^ (p + scaleShift p x) :=
    pow_le_pow_right₀ (by norm_num) (by unfold scaleShift; omega)
  have hfloor' : x < (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊ + 1) := by exact_mod_cast hfloor
  exact hfloor'.trans_le hpow

theorem scaleShift_lower {p : Nat} (hp : 0 < p) {x : ℚ} (hx : 0 ≤ x)
    (hk : 0 < scaleShift p x) :
    (10 : ℚ) ^ (p + scaleShift p x - 1) ≤ x := by
  have hlog : Nat.log 10 ⌊x⌋₊ = p + scaleShift p x - 1 := by
    unfold scaleShift at *
    omega
  by_cases hz : ⌊x⌋₊ = 0
  · simp [hz, scaleShift] at hk
    omega
  have hpow := Nat.pow_log_le_self 10 hz
  have hcast : (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊) ≤ (⌊x⌋₊ : ℚ) := by
    exact_mod_cast hpow
  rw [hlog] at hcast
  exact hcast.trans (Nat.floor_le hx)

/-- Any coarser grid which fits the coefficient bound is above the selected grid. -/
theorem scaleShift_le_of_lt {p k : Nat} (hp : 0 < p) {x : ℚ} (hx : 0 ≤ x)
    (h : x < (10 : ℚ) ^ (p + k)) : scaleShift p x ≤ k := by
  by_cases hz : ⌊x⌋₊ = 0
  · simp only [scaleShift, hz, Nat.log_zero_right]
    omega
  have hf : ⌊x⌋₊ < 10 ^ (p + k) :=
    (Nat.floor_lt hx).mpr (by exact_mod_cast h)
  have hl := (Nat.log_lt_iff_lt_pow (by decide : 1 < 10) hz).mpr hf
  unfold scaleShift
  omega

theorem roundingQuantum_ge_min (f : Format) (x : ℚ) :
    f.minQuantum ≤ roundingQuantum f x := by
  rw [roundingQuantum_eq]
  omega

/-- The exact scaled magnitude fits strictly below the coefficient bound. -/
theorem div_roundingQuantum_lt (f : Format) {x : ℚ} (hx : 0 ≤ x) :
    x / (10 : ℚ) ^ roundingQuantum f x < (f.coefficientBound : ℚ) := by
  have hu : 0 < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have h := scaleShift_upper f.precision (div_nonneg hx hu.le)
  rw [pow_add, div_lt_iff₀ hu] at h
  rw [roundingQuantum_eq, zpow_add₀ (by norm_num), zpow_natCast,
    Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_lt_iff₀ (mul_pos hu (pow_pos (by norm_num) _))).mpr
  nlinarith [h]

/-- The selected quantum is the smallest quantum with a fitting exact coefficient. -/
theorem roundingQuantum_le (f : Format) {x : ℚ} (hx : 0 ≤ x) {q : Int}
    (hq : f.minQuantum ≤ q)
    (hfit : x < (f.coefficientBound : ℚ) * (10 : ℚ) ^ q) :
    roundingQuantum f x ≤ q := by
  let k := (q - f.minQuantum).toNat
  have hk : f.minQuantum + (k : Int) = q := by omega
  have hu : 0 < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have hp := f.precision_pos
  have hscaled : x / (10 : ℚ) ^ f.minQuantum < (10 : ℚ) ^ (f.precision + k) := by
    rw [div_lt_iff₀ hu, pow_add]
    rw [← hk, zpow_add₀ (by norm_num), zpow_natCast,
      Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat] at hfit
    nlinarith [hfit]
  have h := scaleShift_le_of_lt hp (div_nonneg hx hu.le) hscaled
  rw [roundingQuantum_eq]
  omega

/-- Above the subnormal grid, the exact scaled coefficient has a full leading digit. -/
theorem payloadBound_le_div_roundingQuantum (f : Format) {x : ℚ} (hx : 0 ≤ x)
    (hq : f.minQuantum < roundingQuantum f x) :
    (f.payloadBound : ℚ) ≤ x / (10 : ℚ) ^ roundingQuantum f x := by
  have hu : 0 < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  let k := scaleShift f.precision (x / (10 : ℚ) ^ f.minQuantum)
  have hk : 0 < k := by rw [roundingQuantum_eq] at hq; omega
  have hp := f.precision_pos
  have h := scaleShift_lower hp (div_nonneg hx hu.le) hk
  have he : f.precision + k - 1 = (f.precision - 1) + k := by omega
  have hb := f.payloadBound_eq
  change (10 : ℚ) ^ (f.precision + k - 1) ≤ x / (10 : ℚ) ^ f.minQuantum at h
  rw [he, pow_add, le_div_iff₀ hu] at h
  rw [roundingQuantum_eq, zpow_add₀ (by norm_num), zpow_natCast, hb,
    Nat.cast_pow, Nat.cast_ofNat]
  apply (le_div_iff₀ (mul_pos hu (pow_pos (by norm_num) _))).mpr
  change (10 : ℚ) ^ (f.precision - 1) * ((10 : ℚ) ^ f.minQuantum * (10 : ℚ) ^ k) ≤ x
  nlinarith [h]

end FloatLib.Floats.Formats.DecimalInterchange
