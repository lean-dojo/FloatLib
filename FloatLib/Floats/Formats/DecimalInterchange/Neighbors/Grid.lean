/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Exact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Decimal grid gaps

A least-quantum representation is either on the subnormal grid or has a full
leading digit. Every finer-grid representation is below that leading digit;
every coarser-grid representation occupies an integer point on the current grid.
These two facts exclude all representable values between consecutive coefficients.
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
  let k := d * 10 ^ (r - q).toNat
  have he : q + ((r - q).toNat : Int) = r := by omega
  have hv : (k : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r := by
    conv_rhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
    simp only [k, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hp : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) _
  rw [← hv] at hlt ⊢
  have hc : c < k := by exact_mod_cast (mul_lt_mul_iff_left₀ hp).mp hlt
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

/-- Any normalized pair is the least-quantum member of its entire valid cohort. -/
theorem neighbor_quantum_minimal (f : Format) (c d : Nat) (q r : Int)
    (hfull : q = f.minQuantum ∨ f.payloadBound ≤ c)
    (hd : d < f.coefficientBound) (hr : f.minQuantum ≤ r)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  rcases hfull with hq | hc
  · omega
  · exact quantum_le_of_full_coefficient f c d q r hc hd he

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
