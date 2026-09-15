/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Tactic.NormNum
public import FloatLib.Floats.Formats.P3109.Projection.Runtime

/-!
# Precision-grid proofs for P3109 projection

P3109 rounds to a descriptor-dependent binary grid before applying saturation. This module proves
that the width-independent rounding kernel always produces either zero or a finite value that
fits the descriptor precision and minimum quantum.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/-- Every descriptor-selected quantum is no smaller than the minimum encodable quantum. -/
theorem quantumExponent_lower
    (format : Format) (leading : Int) :
    format.minimumQuantumExponent ≤
      max leading format.minimumNormalExponent -
        Int.ofNat format.precision + 1 := by
  have minimum_le :
      format.minimumNormalExponent ≤
        max leading format.minimumNormalExponent :=
    le_max_right _ _
  unfold minimumQuantumExponent minimumNormalExponent
  omega

/-- A left shift that keeps the leading bit below the precision stays below `2^P`. -/
private theorem shiftLeft_lt_precision
    (format : Format) (significand shift : Nat)
    (hzero : significand ≠ 0)
    (hbound :
      significand.log2 + 1 + shift ≤ format.precision) :
    Nat.shiftLeft significand shift <
      2 ^ format.precision := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  calc
    significand * 2 ^ shift <
        2 ^ (significand.log2 + 1) * 2 ^ shift :=
      Nat.mul_lt_mul_of_pos_right ((Nat.log2_lt hzero).1 (Nat.lt_succ_self _))
        (Nat.two_pow_pos _)
    _ = 2 ^ (significand.log2 + 1 + shift) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ format.precision := Nat.pow_le_pow_right (by decide) hbound

/-- Discarding enough low bits leaves a significand below `2^P`. -/
private theorem shiftRight_lt_precision
    (format : Format) (significand discardedBits : Nat)
    (hzero : significand ≠ 0)
    (hbound :
      significand.log2 + 1 ≤
        format.precision + discardedBits) :
    Nat.shiftRight significand discardedBits <
      2 ^ format.precision := by
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Nat.div_lt_iff_lt_mul (Nat.two_pow_pos discardedBits), ← Nat.pow_add]
  exact lt_of_lt_of_le ((Nat.log2_lt hzero).1 (Nat.lt_succ_self _))
    (Nat.pow_le_pow_right (by decide) hbound)

/-- Precision and minimum-quantum bounds for a dyadic, before finite-range saturation. -/
def FitsPrecisionGrid
    (format : Format) (value : Numerics.Dyadic) : Prop :=
  value.significand = 0 ∨
    (value.significand ≤ 2 ^ format.precision ∧
      format.minimumQuantumExponent ≤ value.exponent)

/--
Precision rounding lands on the descriptor grid for every P3109 rounding mode.

The bound includes the carry significand `2^P`, which the encoder advances to the next exponent
row.
-/
theorem roundFiniteToPrecision_fitsPrecisionGrid
    (format : Format) (mode : RoundingMode)
    (value : Numerics.Dyadic) :
    format.FitsPrecisionGrid
      (format.roundFiniteToPrecision mode value) := by
  unfold FitsPrecisionGrid roundFiniteToPrecision
  simp only [beq_iff_eq]
  split
  next hzero => simp
  next hzero =>
    have hquantum :=
      format.quantumExponent_lower (Int.ofNat value.significand.log2 + value.exponent)
    have hleading :=
      le_max_left (Int.ofNat value.significand.log2 + value.exponent)
        format.minimumNormalExponent
    simp only [Int.ofNat_eq_natCast] at hquantum hleading ⊢
    split
    next shift heq =>
      simp only [Int.ofNat_eq_natCast] at heq
      exact Or.inr
        ⟨Nat.le_of_lt (format.shiftLeft_lt_precision _ _ hzero (by omega)), hquantum⟩
    next shift heq =>
      have hlower : Nat.shiftRight value.significand (shift + 1) < 2 ^ format.precision :=
        format.shiftRight_lt_precision _ _ hzero (by
          rw [Int.negSucc_eq] at heq
          omega)
      split <;> split
      · simp
      · exact Or.inr ⟨by dsimp only; omega, hquantum⟩
      · simp
      · exact Or.inr ⟨by dsimp only; omega, hquantum⟩

end Format
end FloatLib.Floats.Formats.P3109
