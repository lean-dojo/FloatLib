/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Scale
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.FormatProof

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

/-- A nonnegative rational is below the power of ten one place above the leading digit of its
integer part. -/
theorem lt_ten_pow_log_floor_succ {x : ℚ} (hx : 0 ≤ x) :
    x < (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊ + 1) := by
  have hfloor : x < ((10 ^ (Nat.log 10 ⌊x⌋₊ + 1) : Nat) : ℚ) :=
    (Nat.floor_lt hx).mp (Nat.lt_pow_succ_log_self (by decide : 1 < 10) ⌊x⌋₊)
  exact_mod_cast hfloor

/-- A nonnegative rational below `10 ^ n`, with `n` positive, has an integer part with fewer than
`n + 1` digits: its decimal logarithm is below `n`. -/
theorem log_floor_lt_of_lt {n : Nat} (hn : 0 < n) {x : ℚ} (hx : 0 ≤ x)
    (h : x < (10 : ℚ) ^ n) : Nat.log 10 ⌊x⌋₊ < n := by
  by_cases hz : ⌊x⌋₊ = 0
  · simpa [hz] using hn
  exact (Nat.log_lt_iff_lt_pow (by decide : 1 < 10) hz).mpr
    ((Nat.floor_lt hx).mpr (by exact_mod_cast h))

/-- The grid shift is large enough: a scaled magnitude is below `10 ^ (p + shift)`, so it has at
most `p` digits after the shift. -/
theorem scaleShift_upper (p : Nat) (x : ℚ) :
    x < (10 : ℚ) ^ (p + scaleShift p x) := by
  rcases lt_or_ge x 0 with hx | hx
  · exact hx.trans (pow_pos (by norm_num) _)
  exact (lt_ten_pow_log_floor_succ hx).trans_le
    (pow_le_pow_right₀ (by norm_num) (by unfold scaleShift; omega))

/-- A nonzero grid shift keeps a full leading digit: the scaled magnitude is at least
`10 ^ (p + shift - 1)`. -/
theorem scaleShift_lower {p : Nat} (hp : 0 < p) {x : ℚ}
    (hk : 0 < scaleShift p x) :
    (10 : ℚ) ^ (p + scaleShift p x - 1) ≤ x := by
  have hlog : Nat.log 10 ⌊x⌋₊ = p + scaleShift p x - 1 := by
    unfold scaleShift at *
    omega
  by_cases hz : ⌊x⌋₊ = 0
  · simp [hz, scaleShift] at hk
    omega
  have hx : 0 ≤ x := zero_le_one.trans (Nat.floor_pos.mp (Nat.pos_of_ne_zero hz))
  have hpow := Nat.pow_log_le_self 10 hz
  have hcast : (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊) ≤ (⌊x⌋₊ : ℚ) := by
    exact_mod_cast hpow
  rw [hlog] at hcast
  exact hcast.trans (Nat.floor_le hx)

/-- Any coarser grid which fits the coefficient bound is above the selected grid. -/
theorem scaleShift_le_of_lt {p k : Nat} (hp : 0 < p) {x : ℚ} (hx : 0 ≤ x)
    (h : x < (10 : ℚ) ^ (p + k)) : scaleShift p x ≤ k := by
  have hl := log_floor_lt_of_lt (by omega) hx h
  unfold scaleShift
  omega

/-- The rounding grid is never finer than the format's least quantum. -/
theorem roundingQuantum_ge_min (f : Format) (x : ℚ) :
    f.minQuantum ≤ roundingQuantum f x := by
  rw [roundingQuantum_eq]
  omega

/-- Dividing by the power of ten at `m + k` divides by `10 ^ m` and then by `10 ^ k`, the step from
the least-quantum scaling to the selected grid. -/
private theorem div_zpow_add_natCast (x : ℚ) (m : Int) (k : Nat) :
    x / (10 : ℚ) ^ (m + (k : Int)) = x / (10 : ℚ) ^ m / (10 : ℚ) ^ k := by
  rw [zpow_add₀ (by norm_num), zpow_natCast, div_div]

/-- The exact scaled magnitude fits strictly below the coefficient bound. -/
theorem div_roundingQuantum_lt (f : Format) (x : ℚ) :
    x / (10 : ℚ) ^ roundingQuantum f x < (f.coefficientBound : ℚ) := by
  rw [roundingQuantum_eq, div_zpow_add_natCast, div_lt_iff₀ (pow_pos (by norm_num) _),
    Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  exact scaleShift_upper f.precision _

/-- The selected quantum is the smallest quantum with a fitting exact coefficient. -/
theorem roundingQuantum_le (f : Format) {x : ℚ} (hx : 0 ≤ x) {q : Int}
    (hq : f.minQuantum ≤ q)
    (hfit : x < (f.coefficientBound : ℚ) * (10 : ℚ) ^ q) :
    roundingQuantum f x ≤ q := by
  let k := (q - f.minQuantum).toNat
  have hk : f.minQuantum + (k : Int) = q := by omega
  have hu : 0 < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have hscaled : x / (10 : ℚ) ^ f.minQuantum < (10 : ℚ) ^ (f.precision + k) := by
    rw [← hk, ← div_lt_iff₀ (zpow_pos (by norm_num) _), div_zpow_add_natCast,
      Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat] at hfit
    rwa [pow_add, ← div_lt_iff₀ (pow_pos (by norm_num) _)]
  have h := scaleShift_le_of_lt f.precision_pos (div_nonneg hx hu.le) hscaled
  rw [roundingQuantum_eq]
  omega

/-- Above the subnormal grid, the exact scaled coefficient has a full leading digit. -/
theorem payloadBound_le_div_roundingQuantum (f : Format) {x : ℚ}
    (hq : f.minQuantum < roundingQuantum f x) :
    (f.payloadBound : ℚ) ≤ x / (10 : ℚ) ^ roundingQuantum f x := by
  rw [roundingQuantum_eq] at hq ⊢
  set k := scaleShift f.precision (x / (10 : ℚ) ^ f.minQuantum)
  have h := scaleShift_lower f.precision_pos (by omega : 0 < k)
  have he : f.precision + k - 1 = (f.precision - 1) + k := by
    have hp := f.precision_pos
    omega
  rw [div_zpow_add_natCast, le_div_iff₀ (pow_pos (by norm_num) _), f.payloadBound_eq,
    Nat.cast_pow, Nat.cast_ofNat, ← pow_add, ← he]
  exact h

end FloatLib.Floats.Formats.DecimalInterchange
