/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Proof

/-!
# Closest preferred exponent

This file proves that `preferredCohort` picks the right cohort member. When two members of a
finite cohort have different quanta, their integer coefficients differ by a power of ten, so a
coefficient with no trailing zero can't move to a higher quantum. Starting from the smallest
representable quantum, stripping trailing zeros therefore stops at the exponent closest to the
preferred one.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Equality of decimal values on nested grids gives an exact integer coefficient factor. -/
theorem coefficient_eq_mul_of_quantum_le (c d : Nat) {q r : Int} (hqr : q ≤ r)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    c = d * 10 ^ (r - q).toNat := by
  have hc := mul_right_cancel₀ (zpow_ne_zero q (by norm_num : (10 : ℚ) ≠ 0))
    (hvalue.trans (Arithmetic.finer_grid_value d r q hqr).symm)
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
  have hq : q ≤ f.maxQuantum := hstart.trans hrmax
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

/-- Starting from a pair `(c, q)` whose quantum is at most that of every in-range representation of
its value (`hminimal`), the datum `preferredCohort` delivers has an exponent at least as close to
the preferred one as that of every valid representation `(e, t)` of that value. The premise is
needed because `preferredCohort` only strips trailing zeros, so it never reaches a finer quantum
than `q`. -/
theorem preferredCohort_quantum_closest_of_eq (f : Format) (s : Bool) (c : Nat)
    (q preferred : Int)
    (hminimal : ∀ (d : Nat) (r : Int), d < f.coefficientBound →
      f.minQuantum ≤ r → r ≤ f.maxQuantum →
      (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r → q ≤ r)
    (d : Nat) (r : Int) (hout : preferredCohort f s c q preferred = .finite s d r)
    (e : Nat) (t : Int) (he : (Datum.finite s e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (e : ℚ) * (10 : ℚ) ^ t) :
    |preferred - r| ≤ |preferred - t| := by
  have he' := (Datum.valid_quantum_iff ..).mp he
  rw [← (Datum.finite.inj hout).2.2]
  exact preferredCohort_quantum_closest f c q preferred hminimal e t he'.1 he'.2.1 he'.2.2 hvalue

/-- A coefficient with a full leading digit cannot be represented at a finer quantum.
It compares equal numerical values, so trailing zeros don't affect it. -/
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

namespace Arithmetic

/-- A pair `(c, q)` on the least grid or with a full leading digit has the least quantum among the
representations of its value: every `(d, r)` with `d` below the coefficient bound, `r` at least the
least quantum and `d * 10 ^ r = c * 10 ^ q` has `q ≤ r`. This covers the whole valid cohort, and
neither pair needs to be valid otherwise. -/
theorem quantum_le_of_minimum_or_full (f : Format) (c d : Nat) (q r : Int)
    (hfull : q = f.minQuantum ∨ f.payloadBound ≤ c)
    (hd : d < f.coefficientBound) (hr : f.minQuantum ≤ r)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  rcases hfull with hq | hc
  · omega
  · exact quantum_le_of_full_coefficient f c d q r hc hd he

end Arithmetic

end FloatLib.Floats.Formats.DecimalInterchange
