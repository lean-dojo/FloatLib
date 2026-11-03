/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.ScaleProof

/-!
# Decimal coefficient range for arbitrary integer-degree roots

Dividing the integer decimal logarithm by the positive degree determines a
fitting root grid. The argument uses exact powers and applies to any format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The root grid shift is large enough: a scaled radicand is below `10 ^ (degree * (p + shift))`,
so its root has at most `p` digits after the shift. -/
theorem rootScaleShift_upper (p : Nat) {degree : Nat} (hn : 0 < degree) (x : ℚ) :
    x < (10 : ℚ) ^ (degree * (p + rootScaleShift p degree x)) := by
  rcases lt_or_ge x 0 with hx | hx
  · exact hx.trans (pow_pos (by norm_num) _)
  apply (lt_ten_pow_log_floor_succ hx).trans_le
  apply pow_le_pow_right₀ (by norm_num)
  have hd := Nat.lt_mul_div_succ (Nat.log 10 ⌊x⌋₊) hn
  have hp : Nat.log 10 ⌊x⌋₊ / degree + 1 ≤ p + rootScaleShift p degree x := by
    unfold rootScaleShift
    omega
  exact (Nat.succ_le_of_lt hd).trans (Nat.mul_le_mul_left degree hp)

/-- A nonzero root grid shift keeps a full leading digit: the scaled radicand is at least
`10 ^ (degree * (p + shift - 1))`. -/
theorem rootScaleShift_lower {p degree : Nat} (hp : 0 < p) {x : ℚ}
    (hk : 0 < rootScaleShift p degree x) :
    (10 : ℚ) ^ (degree * (p + rootScaleShift p degree x - 1)) ≤ x := by
  have hm : p + rootScaleShift p degree x - 1 = Nat.log 10 ⌊x⌋₊ / degree := by
    unfold rootScaleShift at hk ⊢
    generalize Nat.log 10 ⌊x⌋₊ / degree = m at hk ⊢
    omega
  have hz : ⌊x⌋₊ ≠ 0 := by
    intro hz
    simp only [rootScaleShift, hz, Nat.log_zero_right, Nat.zero_div] at hk
    omega
  have hx : 0 ≤ x := zero_le_one.trans (Nat.floor_pos.mp (Nat.pos_of_ne_zero hz))
  have hlog : degree * (p + rootScaleShift p degree x - 1) ≤ Nat.log 10 ⌊x⌋₊ := by
    rw [hm]
    exact Nat.mul_div_le _ _
  have hpow : (10 : ℚ) ^ (Nat.log 10 ⌊x⌋₊) ≤ (⌊x⌋₊ : ℚ) := by
    exact_mod_cast Nat.pow_log_le_self 10 hz
  exact ((pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 10) hlog).trans hpow).trans
    (Nat.floor_le hx)

/-- A radicand that fits `degree * (p + k)` digits bounds the root grid shift by `k`. -/
theorem rootScaleShift_le_of_lt {p degree k : Nat} (hp : 0 < p) (hn : 0 < degree) {x : ℚ}
    (hx : 0 ≤ x) (h : x < (10 : ℚ) ^ (degree * (p + k))) : rootScaleShift p degree x ≤ k := by
  have hl := log_floor_lt_of_lt (Nat.mul_pos hn (by omega)) hx h
  have hd : Nat.log 10 ⌊x⌋₊ / degree < p + k :=
    (Nat.div_lt_iff_lt_mul hn).mpr (by rwa [Nat.mul_comm] at hl)
  unfold rootScaleShift
  omega

/-- The root grid is never finer than the format's least quantum. -/
theorem rootQuantum_ge_min (f : Format) (degree : Nat) (x : ℚ) :
    f.minQuantum ≤ rootQuantum f degree x := by
  unfold rootQuantum
  omega

/-- Scaling by the root grid divides by the least-quantum scale and then by `10 ^ (degree * k)`,
where `k` is the grid shift. -/
private theorem div_rootQuantum_eq (f : Format) (degree : Nat) (x : ℚ) :
    x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) =
      x / (10 : ℚ) ^ ((degree : Int) * f.minQuantum) /
        (10 : ℚ) ^ (degree * rootScaleShift f.precision degree
          (x / (10 : ℚ) ^ ((degree : Int) * f.minQuantum))) := by
  rw [rootQuantum, mul_add, ← Nat.cast_mul, zpow_add₀ (by norm_num), zpow_natCast, div_div]

/-- The scaled radicand is strictly below the power of the coefficient bound. -/
theorem div_rootQuantum_lt (f : Format) {degree : Nat} (hn : 0 < degree) (x : ℚ) :
    x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) <
      (f.coefficientBound : ℚ) ^ degree := by
  rw [div_rootQuantum_eq, div_lt_iff₀ (pow_pos (by norm_num) _), Format.coefficientBound_eq,
    Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add, Nat.mul_comm f.precision, ← Nat.mul_add]
  exact rootScaleShift_upper f.precision hn _

/-- The selected root grid is the smallest grid on which the root fits the precision: any quantum
`q` at least the least quantum with `x < coefficientBound ^ degree * 10 ^ (degree * q)` is at least
the selected one. -/
theorem rootQuantum_le (f : Format) {degree : Nat} (hn : 0 < degree) {x : ℚ} (hx : 0 ≤ x)
    {q : Int} (hq : f.minQuantum ≤ q)
    (hfit : x < (f.coefficientBound : ℚ) ^ degree * (10 : ℚ) ^ ((degree : Int) * q)) :
    rootQuantum f degree x ≤ q := by
  let k := (q - f.minQuantum).toNat
  have hk : f.minQuantum + (k : Int) = q := by omega
  have hu : 0 < (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := zpow_pos (by norm_num) _
  have hscaled : x / (10 : ℚ) ^ ((degree : Int) * f.minQuantum) <
      (10 : ℚ) ^ (degree * (f.precision + k)) := by
    rw [← hk, mul_add, ← Nat.cast_mul, zpow_add₀ (by norm_num), zpow_natCast,
      Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] at hfit
    rw [div_lt_iff₀ hu, Nat.mul_add, pow_add, Nat.mul_comm degree f.precision]
    linarith
  have h := rootScaleShift_le_of_lt f.precision_pos hn (div_nonneg hx hu.le) hscaled
  unfold rootQuantum
  omega

/-- Above the subnormal grid, the scaled radicand is at least the `degree`-th power of a full
leading digit. -/
theorem payloadBound_pow_le_div_rootQuantum (f : Format) {degree : Nat} {x : ℚ}
    (hq : f.minQuantum < rootQuantum f degree x) :
    (f.payloadBound : ℚ) ^ degree ≤
      x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) := by
  let k := rootScaleShift f.precision degree
    (x / (10 : ℚ) ^ ((degree : Int) * f.minQuantum))
  have hk : 0 < k := by unfold rootQuantum at hq; omega
  have hp := f.precision_pos
  have he : degree * (f.precision + k - 1) = (f.precision - 1) * degree + degree * k := by
    rw [show f.precision + k - 1 = (f.precision - 1) + k by omega, Nat.mul_add,
      Nat.mul_comm degree]
  have h := rootScaleShift_lower hp hk
  rw [he, pow_add, pow_mul] at h
  rw [div_rootQuantum_eq, f.payloadBound_eq, Nat.cast_pow, Nat.cast_ofNat,
    le_div_iff₀ (pow_pos (by norm_num) _)]
  exact h

end FloatLib.Floats.Formats.DecimalInterchange
