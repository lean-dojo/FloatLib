/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Optimal

/-!
# Exact representable square roots

On a finer decimal grid, a representable root has an integer coefficient.
Squaring that integer identifies the scaled radicand exactly, so every rounding
mode recovers the same root. No test for irrationality is needed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Refining a root's decimal grid produces an exact integer square after scaling. -/
theorem scaled_decimal_sq (c : Nat) {q r : Int} (hqr : r ≤ q) :
    ((c : ℚ) * (10 : ℚ) ^ q) ^ 2 / (10 : ℚ) ^ (2 * r) =
      (((c * 10 ^ (q - r).toNat : Nat) : ℚ)) ^ 2 := by
  have he : r + ((q - r).toNat : Int) = q := by omega
  have hp : (10 : ℚ) ^ (2 * r) = ((10 : ℚ) ^ r) ^ 2 := by
    rw [mul_comm 2 r, zpow_mul]
    norm_num
  conv_lhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
  rw [hp]
  push_cast
  field_simp

/-- Recovering a representable root on any finer grid preserves its exact value. -/
theorem RoundingMode.sqrtRound_exact_value (mode : RoundingMode) (c : Nat)
    {q r : Int} (hqr : r ≤ q) :
    (mode.sqrtRound (((c : ℚ) * (10 : ℚ) ^ q) ^ 2 / (10 : ℚ) ^ (2 * r)) : ℚ) *
        (10 : ℚ) ^ r = (c : ℚ) * (10 : ℚ) ^ q := by
  rw [scaled_decimal_sq c hqr, mode.sqrtRound_nat_sq]
  have he : r + ((q - r).toNat : Int) = q := by omega
  conv_rhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
  push_cast
  ring

/-- The coefficient of an exact representable root cannot require a carry. -/
theorem sqrtRound_lt_coefficientBound_of_valid (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hvalid : (Datum.finite s c q).Valid f) :
    mode.sqrtRound (((c : ℚ) * (10 : ℚ) ^ q) ^ 2 /
      (10 : ℚ) ^ (2 * sqrtQuantum f (((c : ℚ) * (10 : ℚ) ^ q) ^ 2))) <
      f.coefficientBound := by
  have hq := sqrtQuantum_le_of_valid f s c q hvalid
  have hbound := div_sqrtQuantum_lt f (sq_nonneg ((c : ℚ) * (10 : ℚ) ^ q))
  rw [scaled_decimal_sq c hq] at hbound ⊢
  rw [mode.sqrtRound_nat_sq]
  have hn : (0 : ℚ) ≤ ((c * 10 ^
      (q - sqrtQuantum f (((c : ℚ) * (10 : ℚ) ^ q) ^ 2)).toNat : Nat) : ℚ) :=
    Nat.cast_nonneg _
  have hb : (0 : ℚ) ≤ f.coefficientBound := Nat.cast_nonneg _
  exact_mod_cast (show (((c * 10 ^
      (q - sqrtQuantum f (((c : ℚ) * (10 : ℚ) ^ q) ^ 2)).toNat : Nat) : ℚ)) <
      (f.coefficientBound : ℚ) by nlinarith)

/-- An exact root's normalized grid is no coarser than any valid representation of that root. -/
theorem sqrtPair_quantum_le_of_valid (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hvalid : (Datum.finite s c q).Valid f) :
    (sqrtPair f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2)).2 ≤ q := by
  have hlt := sqrtRound_lt_coefficientBound_of_valid f mode s c q hvalid
  simp only [sqrtPair, f.carry_eq, ite_eq_right (Nat.ne_of_lt hlt)]
  exact sqrtQuantum_le_of_valid f s c q hvalid

/-- All five modes recover every representable nonnegative root exactly. -/
theorem sqrtPair_exact_value (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hvalid : (Datum.finite s c q).Valid f) :
    ((sqrtPair f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2)).1 : ℚ) *
        (10 : ℚ) ^ (sqrtPair f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2)).2 =
      (c : ℚ) * (10 : ℚ) ^ q := by
  rw [sqrtPair_value]
  exact mode.sqrtRound_exact_value c (sqrtQuantum_le_of_valid f s c q hvalid)

/-- Exact representable roots raise none of the five default exception flags. -/
theorem sqrtMagnitude_exact_status (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q preferred : Int) (hvalid : (Datum.finite s c q).Valid f) :
    (sqrtMagnitude f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2) preferred).status = {} := by
  have hq := (sqrtPair_quantum_le_of_valid f mode s c q hvalid).trans
    ((Datum.valid_quantum_iff ..).mp hvalid).2.2
  have hv := sqrtPair_exact_value f mode s c q hvalid
  simp [sqrtMagnitude, not_lt.mpr hq, hv]

/-- Exact square-root projection returns the nonnegative root, regardless of its representation. -/
theorem sqrtMagnitude_exact (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q preferred : Int) (hvalid : (Datum.finite s c q).Valid f) :
    (sqrtMagnitude f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2) preferred).value.toRat? =
      some ((c : ℚ) * (10 : ℚ) ^ q) := by
  rw [sqrtMagnitude_value f mode _ preferred
    ((sqrtPair_quantum_le_of_valid f mode s c q hvalid).trans
      ((Datum.valid_quantum_iff ..).mp hvalid).2.2)]
  rw [mode.sqrtRound_exact_value c (sqrtQuantum_le_of_valid f s c q hvalid)]

end FloatLib.Floats.Formats.DecimalInterchange
