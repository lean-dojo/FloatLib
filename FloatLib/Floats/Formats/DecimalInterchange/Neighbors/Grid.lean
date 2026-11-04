/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Exact

/-!
# Decimal grid gaps

Why is there nothing representable between consecutive coefficients? A least-quantum
representation is either on the subnormal grid or has a full leading digit. Every representation
on a finer grid stays below that leading digit, and every representation on a coarser grid sits on
an integer point of the current grid. Between them, those two facts leave no room.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- A bounded finer-grid coefficient lies below the next grid's full leading digit. -/
theorem neighbor_finer_lt (f : Format) (d : Nat) (q r : Int)
    (hd : d < f.coefficientBound) (hr : r < q) :
    (d : ℚ) * (10 : ℚ) ^ r < (f.payloadBound : ℚ) * (10 : ℚ) ^ q := by
  have he : q = (q - 1) + 1 := by omega
  have hp : (10 : ℚ) ^ r ≤ (10 : ℚ) ^ (q - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hd' : (d : ℚ) < (f.coefficientBound : ℚ) := by exact_mod_cast hd
  have hb : (f.coefficientBound : ℚ) = 10 * (f.payloadBound : ℚ) := by
    simp [Format.coefficientBound]
  have hmul := mul_lt_mul_of_pos_right hd' (zpow_pos (by norm_num : (0 : ℚ) < 10) r)
  have hnonneg : (0 : ℚ) ≤ f.coefficientBound := Nat.cast_nonneg _
  have hbound := mul_le_mul_of_nonneg_left hp hnonneg
  rw [he, zpow_add₀ (by norm_num), zpow_one]
  rw [hb] at hmul hbound
  nlinarith

/-- Coarser decimal grids contain only integer points of every finer grid. -/
theorem neighbor_integer_gap (c d : Nat) (q r : Int) (hqr : q ≤ r)
    (hlt : (c : ℚ) * (10 : ℚ) ^ q < (d : ℚ) * (10 : ℚ) ^ r) :
    ((c + 1 : Nat) : ℚ) * (10 : ℚ) ^ q ≤ (d : ℚ) * (10 : ℚ) ^ r := by
  have hp : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) _
  rw [← finer_grid_value d r q hqr] at hlt ⊢
  have hc : c < d * 10 ^ (r - q).toNat := by exact_mod_cast (mul_lt_mul_iff_left₀ hp).mp hlt
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hc) hp.le

/-- No valid decimal value occurs between a normalized coefficient and its successor. -/
theorem neighbor_gap (f : Format) (c d : Nat) (q r : Int)
    (hfull : q = f.minQuantum ∨ f.payloadBound ≤ c)
    (hd : d < f.coefficientBound) (hr : f.minQuantum ≤ r)
    (hlt : (c : ℚ) * (10 : ℚ) ^ q < (d : ℚ) * (10 : ℚ) ^ r) :
    ((c + 1 : Nat) : ℚ) * (10 : ℚ) ^ q ≤ (d : ℚ) * (10 : ℚ) ^ r := by
  by_cases hqr : q ≤ r
  · exact neighbor_integer_gap c d q r hqr hlt
  · have hf := neighbor_finer_lt f d q r hd (by omega)
    rcases hfull with hq | hc
    · omega
    · have hc' : (f.payloadBound : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc
      have hh := mul_le_mul_of_nonneg_right hc' (zpow_pos (by norm_num : (0 : ℚ) < 10) q).le
      linarith

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
