/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Runtime

/-!
# Cohort preservation and preferred-exponent bounds

Moving an exact result to its preferred cohort must not change it. Removing trailing zeros keeps the
exact rational value and the sign, and a representable datum stays representable in the same format.
The loop stops at its exponent limit or at a coefficient with no trailing zero, so it never throws
away a significant decimal digit.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Stripping trailing zeros removes at most `fuel` digits. -/
theorem stripTrailing_count_le (fuel c : Nat) : (stripTrailing fuel c).2 ≤ fuel := by
  induction fuel generalizing c with
  | zero => simp [stripTrailing]
  | succ fuel ih =>
      simp only [stripTrailing]
      split
      · simp
      · split
        · simpa using Nat.succ_le_succ (ih (c / 10))
        · simp

/-- The stripped coefficient times ten to the number of removed zeros is the original coefficient,
zero included. -/
theorem stripTrailing_value (fuel c : Nat) :
    c = (stripTrailing fuel c).1 * 10 ^ (stripTrailing fuel c).2 := by
  induction fuel generalizing c with
  | zero => simp [stripTrailing]
  | succ fuel ih =>
      simp only [stripTrailing]
      split
      · rename_i h
        simp [h]
      · split
        · rename_i hzero hmod
          simp only
          have hdiv : c / 10 * 10 = c := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
          calc
            c = (c / 10) * 10 := hdiv.symm
            _ = (stripTrailing fuel (c / 10)).1 *
                10 ^ ((stripTrailing fuel (c / 10)).2 + 1) := by
              conv_lhs => rw [ih (c / 10)]
              rw [pow_succ, Nat.mul_assoc]
        · simp

/-- The adjusted coefficient never exceeds the original one. -/
theorem stripTrailing_coefficient_le (fuel c : Nat) : (stripTrailing fuel c).1 ≤ c := by
  conv_rhs => rw [stripTrailing_value fuel c]
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))

/-- Stopping before the requested quantum means that no further exact decimal shift is possible. -/
theorem stripTrailing_stopped (fuel c : Nat) :
    (stripTrailing fuel c).2 = fuel ∨ (stripTrailing fuel c).1 % 10 ≠ 0 := by
  induction fuel generalizing c with
  | zero => simp [stripTrailing]
  | succ fuel ih =>
      simp only [stripTrailing]
      split
      · simp
      · split
        · simpa using ih (c / 10)
        · simp_all

/-- Cohort adjustment preserves the exact coefficient-times-quantum value and sign. -/
theorem preferredCohort_sameCohort (f : Format) (s : Bool) (c : Nat) (q preferred : Int) :
    Datum.SameCohort (.finite s c q) (preferredCohort f s c q preferred) := by
  simp only [preferredCohort, Datum.SameCohort, true_and]
  have h := stripTrailing_value (min preferred f.maxQuantum - q).toNat c
  have hc : (c : ℚ) =
      ((stripTrailing (min preferred f.maxQuantum - q).toNat c).1 : ℚ) *
        (10 : ℚ) ^ (stripTrailing (min preferred f.maxQuantum - q).toNat c).2 := by
    exact_mod_cast h
  rw [hc, zpow_add₀ (by norm_num), zpow_natCast]
  ring

/-- The selected cohort member has the original signed rational value. -/
theorem preferredCohort_toRat? (f : Format) (s : Bool) (c : Nat) (q preferred : Int) :
    (preferredCohort f s c q preferred).toRat? =
      some ((if s then -1 else 1) * (c : ℚ) * (10 : ℚ) ^ q) := by
  have h := (preferredCohort_sameCohort f s c q preferred).2
  simp only [preferredCohort, Datum.toRat?_eq, mul_assoc]
  rw [← h]

/-- Cohort adjustment keeps a representable finite datum in the same format. -/
theorem preferredCohort_valid (f : Format) (s : Bool) (c : Nat) (q preferred : Int)
    (h : (Datum.finite s c q).Valid f) :
    (preferredCohort f s c q preferred).Valid f := by
  rw [Datum.valid_quantum_iff] at h
  simp only [preferredCohort]
  rw [Datum.valid_quantum_iff]
  refine ⟨(stripTrailing_coefficient_le _ _).trans_lt h.1, ?_, ?_⟩
  · omega
  · have hk := stripTrailing_count_le (min preferred f.maxQuantum - q).toNat c
    omega

end FloatLib.Floats.Formats.DecimalInterchange
