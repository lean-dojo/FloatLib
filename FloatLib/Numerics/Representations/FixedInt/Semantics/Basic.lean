/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.FixedInt.Core
public import FloatLib.Numerics.Core.Proof
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Representation semantics of fixed-width signed integers

The executable two's-complement carrier has a `NumericalSystem` interpretation. The
representation laws characterize the signed interval, encoding and decoding, and the clamp used
by saturating arithmetic.

Keeping this adapter separate from arithmetic is useful: generic operation contracts only need to
know what a code denotes, while the implementation remains free to use `BitVec` overflow
instructions and fixed-width storage.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations.FixedInt

/-- Fixed-width integers interpreted as their signed two's-complement values. -/
def numericalSystem (width : Nat) : NumericalSystem :=
  NumericalSystem.ofFinite (fun value : FixedInt width ↦ value.toInt)

/-- A fixed-width word with an erased proof of its signed value. -/
abbrev AtFinite (width : Nat) (value : Int) :=
  (numericalSystem width).AtFinite value

/-- Representation by a fixed-width integer is equality with its signed two's-complement value. -/
@[simp, grind =] theorem numericalSystem_represents_iff {width : Nat}
    (code : FixedInt width) (value : Int) :
    (numericalSystem width).Represents code value ↔ code.toInt = value := by
  simp [numericalSystem]

/-- Converting an integer to fixed width denotes centered reduction modulo `2 ^ width`. -/
@[simp, grind =] theorem toInt_ofInt {width : Nat} (value : Int) :
    (ofInt (width := width) value).toInt = value.bmod (2 ^ width) :=
  BitVec.toInt_ofInt value

/-- Re-encoding the signed value of a fixed-width integer recovers its original bits. -/
@[simp, grind =] theorem ofInt_toInt {width : Nat} (value : FixedInt width) :
    ofInt value.toInt = value := by
  cases value
  simp [ofInt, toInt, BitVec.ofInt_toInt]

/-- The minimum fixed-width code denotes the signed lower bound. -/
@[simp, grind =] theorem toInt_minCode {width : Nat} :
    (minCode width).toInt = minValue width :=
  rfl

/-- The maximum fixed-width code denotes the signed upper bound. -/
@[simp, grind =] theorem toInt_maxCode {width : Nat} :
    (maxCode width).toInt = maxValue width :=
  rfl

/-- At positive width, the signed lower bound is `-(2 ^ (width - 1))`. -/
theorem minValue_eq {width : Nat} (hwidth : 0 < width) :
    minValue width = -(2 ^ (width - 1) : Int) := by
  simp [minValue, BitVec.toInt_intMin_of_pos hwidth]

/-- The signed upper bound is `2 ^ (width - 1) - 1`. -/
theorem maxValue_eq (width : Nat) :
    maxValue width = (2 ^ (width - 1) : Int) - 1 := by
  simp [maxValue]

/-- At positive width, the signed storage interval is nonempty. -/
theorem minValue_le_maxValue {width : Nat} (hwidth : 0 < width) :
    minValue width ≤ maxValue width := by
  rw [minValue_eq hwidth, maxValue_eq]
  have hpow : (0 : Int) < 2 ^ (width - 1) := Int.pow_pos (by decide)
  omega

/-- Clamping at positive width always produces an in-range integer. -/
theorem clamp_inRange {width : Nat} (hwidth : 0 < width) (value : Int) :
    InRange width (clamp width value) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (minValue_le_maxValue hwidth) (min_le_left _ _)

/-- Clamping fixes every integer already in the signed storage interval. -/
theorem clamp_eq_self {width : Nat} {value : Int} (hvalue : InRange width value) :
    clamp width value = value := by
  rw [clamp, Quantization.Saturating.clamp, min_eq_right hvalue.2, max_eq_right hvalue.1]

/-- Encoding an in-range integer at positive width preserves its exact signed value. -/
theorem toInt_ofInt_eq_self {width : Nat} (hwidth : 0 < width)
    {value : Int} (hvalue : InRange width value) :
    (ofInt (width := width) value).toInt = value := by
  apply BitVec.toInt_ofInt_eq_self hwidth
  · rw [← minValue_eq hwidth]
    exact hvalue.1
  · have hupper := hvalue.2
    rw [maxValue_eq] at hupper
    omega

/-- Saturating conversion denotes exact clamping to the signed storage interval. -/
@[simp, grind =] theorem toInt_ofIntSaturating {width : Nat} (hwidth : 0 < width)
    (value : Int) :
    (ofIntSaturating (width := width) value).toInt = clamp width value := by
  apply toInt_ofInt_eq_self hwidth
  exact clamp_inRange hwidth value

end FloatLib.Numerics.Representations.FixedInt
