/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Proof
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Closest preferred exponent

A higher-quantum member of a finite cohort differs by an exact power of ten in
its integer coefficient. Consequently, a coefficient with no trailing zero
cannot move to a higher quantum. Starting from the smallest representable quantum,
`preferredCohort` therefore selects the exponent closest to the preferred one.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Equality of decimal values on nested grids gives an exact integer coefficient factor. -/
theorem coefficient_eq_mul_of_quantum_le (c d : Nat) {q r : Int} (hqr : q ≤ r)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    c = d * 10 ^ (r - q).toNat := by
  have he : q + ((r - q).toNat : Int) = r := by omega
  have hv : ((d * 10 ^ (r - q).toNat : Nat) : ℚ) * (10 : ℚ) ^ q =
      (d : ℚ) * (10 : ℚ) ^ r := by
    conv_rhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
    push_cast
    ring
  have hc := mul_right_cancel₀ (zpow_ne_zero q (by norm_num : (10 : ℚ) ≠ 0))
    (hvalue.trans hv.symm)
  exact_mod_cast hc

/-- A higher exponent requires a trailing zero in the original coefficient. -/
theorem coefficient_mod_ten_eq_zero_of_quantum_lt (c d : Nat) {q r : Int}
    (hqr : q < r)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    c % 10 = 0 := by
  rw [coefficient_eq_mul_of_quantum_le c d hqr.le hvalue]
  have hk : 0 < (r - q).toNat := by omega
  exact Nat.mod_eq_zero_of_dvd
    (dvd_mul_of_dvd_right (dvd_pow_self 10 (Nat.ne_of_gt hk)) d)

/-- Among coarser representable members, the chosen exponent is closest to the preferred one.
The minimal-quantum premise is discharged for projection by its coefficient range theorem. -/
theorem preferredCohort_quantum_closest (f : Format) (c : Nat) (q preferred : Int)
    (hq : q ≤ f.maxQuantum)
    (hminimal : ∀ (d : Nat) (r : Int), d < f.coefficientBound →
      f.minQuantum ≤ r → r ≤ f.maxQuantum →
      (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r → q ≤ r)
    (d : Nat) (r : Int) (hd : d < f.coefficientBound)
    (hrmin : f.minQuantum ≤ r) (hrmax : r ≤ f.maxQuantum)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    |preferred - (q + ((stripTrailing (min preferred f.maxQuantum - q).toNat c).2 : Int))| ≤
      |preferred - r| := by
  let fuel := (min preferred f.maxQuantum - q).toNat
  let result := stripTrailing fuel c
  have hcount : result.2 ≤ fuel := stripTrailing_count_le fuel c
  have hstart := hminimal d r hd hrmin hrmax hvalue
  by_cases hp : preferred < q
  · have hf : fuel = 0 := by dsimp [fuel]; omega
    have hk : result.2 = 0 := by omega
    change |preferred - (q + (result.2 : Int))| ≤ |preferred - r|
    rw [hk]
    simp only [Nat.cast_zero, add_zero]
    rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
    omega
  · have hf : (fuel : Int) = min preferred f.maxQuantum - q := by
      dsimp [fuel]
      omega
    have hout : q + (result.2 : Int) ≤ preferred := by omega
    have htarget : q + (result.2 : Int) ≤ f.maxQuantum := by omega
    change |preferred - (q + (result.2 : Int))| ≤ |preferred - r|
    rw [abs_of_nonneg (by omega)]
    by_cases hr : r ≤ q + (result.2 : Int)
    · rw [abs_of_nonneg (by omega)]
      omega
    · have hstop := stripTrailing_stopped fuel c
      change result.2 = fuel ∨ result.1 % 10 ≠ 0 at hstop
      rcases hstop with hstop | hstop
      · have he : q + (result.2 : Int) = preferred := by omega
        rw [he, sub_self]
        exact abs_nonneg _
      · have hcohort := preferredCohort_sameCohort f false c q preferred
        change _ ∧ (c : ℚ) * (10 : ℚ) ^ q =
          (result.1 : ℚ) * (10 : ℚ) ^ (q + (result.2 : Int)) at hcohort
        have hv := hcohort.2.symm.trans hvalue
        exact False.elim (hstop
          (coefficient_mod_ten_eq_zero_of_quantum_lt result.1 d (by omega) hv))

/-- A coefficient with a full leading digit cannot be represented at a finer quantum.
This statement compares equal numerical values; trailing zeros do not affect it. -/
theorem quantum_le_of_full_coefficient (f : Format) (c d : Nat) (q r : Int)
    (hc : f.payloadBound ≤ c) (hd : d < f.coefficientBound)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  by_contra h
  have hlt : r < q := by omega
  have he := coefficient_eq_mul_of_quantum_le d c hlt.le hvalue.symm
  have hk : 1 ≤ (q - r).toNat := by omega
  have hp : 10 ≤ 10 ^ (q - r).toNat := by
    simpa using (pow_le_pow_right₀ (by decide : 1 ≤ (10 : Nat)) hk)
  have hbound : f.coefficientBound ≤ d := by
    rw [he, Format.coefficientBound]
    calc
      10 * f.payloadBound ≤ 10 * c := Nat.mul_le_mul_left 10 hc
      _ = c * 10 := Nat.mul_comm ..
      _ ≤ c * 10 ^ (q - r).toNat := Nat.mul_le_mul_left c hp
  omega

end FloatLib.Floats.Formats.DecimalInterchange
