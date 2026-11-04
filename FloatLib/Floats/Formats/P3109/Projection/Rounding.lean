/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Runtime
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Pow

/-!
# Precision-grid proofs for P3109 projection

Before saturation, P3109 rounds to a binary grid that depends on the descriptor. The encoder needs
the result on that grid, and this module proves it: the width-independent rounding kernel always
produces zero or a finite value that fits the descriptor precision and minimum quantum.
`Projection.Direction` proves the rest, that the result keeps the selected quantum exponent and
how it relates to the input (`roundFiniteToPrecision_exponent`, `roundFiniteToPrecision_spec`).
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

/-- A left shift that keeps the leading bit below the precision stays below `2^P`. This includes a
zero significand, which shifts to zero. -/
theorem shiftLeft_lt_precision
    (format : Format) (significand shift : Nat)
    (hbound :
      significand.log2 + 1 + shift ≤ format.precision) :
    Nat.shiftLeft significand shift <
      2 ^ format.precision := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  calc
    significand * 2 ^ shift <
        2 ^ (significand.log2 + 1) * 2 ^ shift :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
    _ = 2 ^ (significand.log2 + 1 + shift) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ format.precision := Nat.pow_le_pow_right (by decide) hbound

/-- Discarding enough low bits leaves a significand below `2^P`. -/
private theorem shiftRight_lt_precision
    (format : Format) (significand discardedBits : Nat)
    (hbound :
      significand.log2 + 1 ≤
        format.precision + discardedBits) :
    Nat.shiftRight significand discardedBits <
      2 ^ format.precision := by
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Nat.div_lt_iff_lt_mul (Nat.two_pow_pos discardedBits), ← Nat.pow_add]
  exact lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hbound)

/--
Precision and minimum-quantum bounds on a dyadic record, before finite-range saturation: a zero
significand, or a significand of at most `2^P` at an exponent no finer than the least quantum.
The bound `2^P` admits the carry of an all-ones significand, which the encoder writes in the next
exponent row. Such a record's value lies on the descriptor's precision grid. The predicate fixes
neither the exponent of the row nor any relation to a rounded input.
-/
def FitsPrecisionGrid
    (format : Format) (value : Numerics.Dyadic) : Prop :=
  value.significand = 0 ∨
    (value.significand ≤ 2 ^ format.precision ∧
      format.minimumQuantumExponent ≤ value.exponent)

/-- A rounded significand of at most `2^P` at a quantum no finer than the least quantum lands on
the grid, with a zero significand canonicalized to the zero dyadic. -/
theorem fitsPrecisionGrid_of_rounded (format : Format) (negative : Bool) {rounded : Nat}
    {quantum : Int} (hrounded : rounded ≤ 2 ^ format.precision)
    (hquantum : format.minimumQuantumExponent ≤ quantum) :
    format.FitsPrecisionGrid
      (if rounded = 0 then .zero else ⟨negative, rounded, quantum⟩) := by
  by_cases hzero : rounded = 0
  · simp [hzero, FitsPrecisionGrid]
  · simp [hzero, FitsPrecisionGrid, hrounded, hquantum]

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
        ⟨Nat.le_of_lt (format.shiftLeft_lt_precision _ _ (by omega)), hquantum⟩
    next shift heq =>
      have hlower : Nat.shiftRight value.significand (shift + 1) < 2 ^ format.precision :=
        format.shiftRight_lt_precision _ _ (by
          rw [Int.negSucc_eq] at heq
          omega)
      split <;> split
      · simp
      · exact Or.inr ⟨by dsimp only; omega, hquantum⟩
      · simp
      · exact Or.inr ⟨by dsimp only; omega, hquantum⟩

end Format
end FloatLib.Floats.Formats.P3109
