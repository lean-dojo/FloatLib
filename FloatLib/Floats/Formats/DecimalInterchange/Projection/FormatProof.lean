/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Format
public import FloatLib.Numerics.Exact.RadixText.PrecisionProof
import Mathlib.Data.Nat.Basic

/-!
# Decimal coefficient bounds

Projection, square root and adjacent-value proofs use the same relation between
a full coefficient and its trailing digits. These consequences of the descriptor
laws apply to every admissible custom layout as well as the named presets.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Format

/-- The trailing digits fill all but one position of the significand precision. -/
theorem payloadBound_eq (f : Format) : f.payloadBound = 10 ^ (f.precision - 1) := by
  rw [Nat.pow_sub_one (by decide : (10 : Nat) ≠ 0) f.precision_pos.ne',
    ← f.coefficientBound_eq]
  simp [coefficientBound]

theorem payloadBound_lt_coefficientBound (f : Format) :
    f.payloadBound < f.coefficientBound := by
  have h := f.payloadBound_pos
  dsimp [coefficientBound]
  omega

theorem payloadBound_le_coefficientBound_sub_one (f : Format) :
    f.payloadBound ≤ f.coefficientBound - 1 := by
  exact Nat.le_sub_one_of_lt f.payloadBound_lt_coefficientBound

theorem one_lt_coefficientBound (f : Format) : 1 < f.coefficientBound := by
  have h := f.payloadBound_pos
  dsimp [coefficientBound]
  omega

/-- A carry at the coefficient bound leaves exactly one leading digit.
This identifies the generic radix carry with the descriptor's coefficient limits. -/
theorem carry_eq (f : Format) (coefficient : Nat) (quantum : Int) :
    Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ coefficient quantum =
      if coefficient = f.coefficientBound then (f.payloadBound, quantum + 1)
      else (coefficient, quantum) := by
  simp only [Numerics.RadixText.carry, PNat.mk_coe, ← f.coefficientBound_eq, ← f.payloadBound_eq]

/-- Normalizing a coefficient bounded by `10^precision` makes the bound strict. -/
theorem carry_coefficient_lt (f : Format) {coefficient : Nat}
    (hc : coefficient ≤ f.coefficientBound) (quantum : Int) :
    (Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ coefficient quantum).1 <
      f.coefficientBound := by
  rw [f.carry_eq]
  split
  · exact f.payloadBound_lt_coefficientBound
  · next h => exact lt_of_le_of_ne hc h

/-- A carry either preserves the quantum or increases it by one. -/
theorem le_carry_quantum (f : Format) (coefficient : Nat) (quantum : Int) :
    quantum ≤
      (Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ coefficient quantum).2 := by
  rw [f.carry_eq]
  split <;> simp

end FloatLib.Floats.Formats.DecimalInterchange.Format
