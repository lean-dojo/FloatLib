/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.DecimalText.Precision
public import FloatLib.Numerics.Exact.DecimalText.Proof
public import FloatLib.Numerics.Exact.RadixText.PrecisionProof

/-!
# Format-independent significant-digit representation laws

Decimal carry preserves the exact rational value at every positive requested precision.
Significant-digit conversion preserves the input sign and the numerical result of the caller's
magnitude rounding on the selected decimal grid.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- Carrying into a new decade changes the coefficient and quantum, but not the value. -/
@[simp] theorem carryDecimal_toRat (digits : ℕ+) (value : Decimal) :
    (carryDecimal digits value).toRat = value.toRat := by
  have h := RadixText.carry_value 10 (by decide) digits value.significand value.exponent
  cases hs : value.negative <;>
    simp only [carryDecimal, Decimal.toRat, hs, Bool.false_eq_true, ite_true, ite_false]
  · exact h
  · simpa only [neg_mul, Nat.cast_ofNat] using congrArg Neg.neg h

/-- The sign does not depend on the chosen precision or magnitude rounder. -/
@[simp] theorem significantDecimal_negative (roundMagnitude : Bool → ℚ → Nat)
    (value : Decimal) (digits : ℕ+) :
    (significantDecimal roundMagnitude value digits).negative = value.negative := by
  rfl

/-- A carry preserves the numerical result of the caller's grid rounding. -/
theorem significantDecimal_value (roundMagnitude : Bool → ℚ → Nat)
    (value : Decimal) (digits : ℕ+) :
    (significantDecimal roundMagnitude value digits).toRat =
      (if value.negative then (-1 : ℚ) else 1) *
        (roundMagnitude value.negative
          ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent /
            (10 : ℚ) ^ significantQuantum value.significand value.exponent digits) : ℚ) *
        (10 : ℚ) ^ significantQuantum value.significand value.exponent digits := by
  rw [significantDecimal, carryDecimal_toRat]
  cases hs : value.negative <;> simp [roundDecimal, RadixText.roundCoefficient, Decimal.toRat, hs]

end FloatLib.Numerics.DecimalText
