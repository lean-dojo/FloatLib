/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Remainder.Runtime

/-!
# The unbounded nearest-even quotient

The quotient is characterized by an error of at most one half and even parity at
the two possible midpoints. The remainder coefficient never exceeds the original
dividend or half the divisor. These integer bounds will prove representability
at the preferred decimal quantum, without rounding the result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

theorem remainderCoefficient_le (a b : Nat) :
    remainderCoefficient a b ≤ a := by
  have hr := Nat.mod_le a b
  unfold remainderCoefficient remainderRoundUp
  split
  · simp only [decide_eq_true_eq] at *
    omega
  · exact hr

theorem remainderCoefficient_twice_le (a b : Nat) (hb : b ≠ 0) :
    2 * remainderCoefficient a b ≤ b := by
  have hr := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  unfold remainderCoefficient remainderRoundUp
  split <;> simp only [decide_eq_true_eq] at * <;> omega

theorem remainderCoefficient_eq_zero_iff (a b : Nat) (hb : b ≠ 0) :
    remainderCoefficient a b = 0 ↔ a % b = 0 := by
  have hr := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  unfold remainderCoefficient remainderRoundUp
  split <;> simp only [decide_eq_true_eq] at *
  all_goals omega

/-- Zero residuals use the lower quotient and therefore retain the input sign. -/
theorem remainderRoundUp_eq_false_of_zero (a b : Nat) (hb : b ≠ 0)
    (hz : remainderCoefficient a b = 0) : remainderRoundUp a b = false := by
  have hr := (remainderCoefficient_eq_zero_iff a b hb).mp hz
  simp [remainderRoundUp, hr, hb]

/-- The natural coefficient and sign encode the exact signed integer residual. -/
theorem remainderCoefficient_signed (a b : Nat) (hb : b ≠ 0) :
    (if remainderRoundUp a b then -(remainderCoefficient a b : ℚ)
      else (remainderCoefficient a b : ℚ)) =
      (a : ℚ) - (remainderQuotient a b : ℚ) * (b : ℚ) := by
  have hr := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  have he : ((a % b : Nat) : ℚ) + ((a / b : Nat) : ℚ) * (b : ℚ) = (a : ℚ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using Nat.mod_add_div a b)
  unfold remainderCoefficient remainderQuotient
  split <;> simp only [Nat.cast_add, Nat.cast_one, add_zero]
  · rw [Nat.cast_sub hr.le]
    linarith
  · linarith

theorem remainderQuotient_error (a b : Nat) (hb : b ≠ 0) :
    2 * |(a : ℚ) - (remainderQuotient a b : ℚ) * (b : ℚ)| ≤ (b : ℚ) := by
  rw [← remainderCoefficient_signed a b hb]
  have h : (2 : ℚ) * (remainderCoefficient a b : ℚ) ≤ (b : ℚ) := by
    exact_mod_cast remainderCoefficient_twice_le a b hb
  split <;> simpa using h

/-- Either midpoint chooses the even integer, with no bound on quotient precision. -/
theorem remainderQuotient_even_at_tie (a b : Nat) (hb : b ≠ 0)
    (htie : 2 * remainderCoefficient a b = b) :
    remainderQuotient a b % 2 = 0 := by
  have hr := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  have hp := Nat.mod_lt (a / b) (by decide : 0 < 2)
  by_cases h : remainderRoundUp a b = true
  · simp [remainderCoefficient, h] at htie
    simp [remainderQuotient, h]
    simp only [remainderRoundUp, decide_eq_true_eq] at h
    omega
  · simp [remainderCoefficient, h] at htie
    simp [remainderQuotient, h]
    simp only [remainderRoundUp, decide_eq_true_eq] at h
    omega

/-- Every other integer quotient has at least as large a residual magnitude. -/
theorem remainderQuotient_nearest (a b : Nat) (hb : b ≠ 0) (n : Int) :
    |(a : ℚ) - (remainderQuotient a b : ℚ) * (b : ℚ)| ≤
      |(a : ℚ) - (n : ℚ) * (b : ℚ)| := by
  have hhalf := remainderQuotient_error a b hb
  have hb' : (0 : ℚ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  rcases lt_trichotomy n (remainderQuotient a b : Int) with hn | hn | hn
  · have hn' : (n : ℚ) + 1 ≤ (remainderQuotient a b : ℚ) := by
      exact_mod_cast hn
    have hlo := neg_abs_le ((a : ℚ) - (remainderQuotient a b : ℚ) * b)
    have hprod := mul_le_mul_of_nonneg_right hn' hb'.le
    have ht := le_abs_self ((a : ℚ) - (n : ℚ) * b)
    nlinarith
  · simp [hn]
  · have hn' : (remainderQuotient a b : ℚ) + 1 ≤ (n : ℚ) := by
      exact_mod_cast hn
    have hhi := le_abs_self ((a : ℚ) - (remainderQuotient a b : ℚ) * b)
    have hprod := mul_le_mul_of_nonneg_right hn' hb'.le
    have ht := neg_le_abs ((a : ℚ) - (n : ℚ) * b)
    nlinarith

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
