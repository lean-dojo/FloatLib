/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Arithmetic semantics of fixed-width signed integers

These are the carrier-level correctness lemmas for wrapping, checked, and saturating signed
arithmetic. They connect overflow predicates and `BitVec` operations to ordinary integer sums,
differences, and products.

The file deliberately stops short of the library-wide operation interface. `Refinement` builds
that reusable layer from these concrete facts, which keeps low-level overflow reasoning out of
generic numerical proofs.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations.FixedInt

/-- Wrapping addition denotes centered modular addition. -/
@[simp, grind =] theorem toInt_wrapAdd {width : Nat} (left right : FixedInt width) :
    (wrapAdd left right).toInt =
      (left.toInt + right.toInt).bmod (2 ^ width) :=
  BitVec.toInt_add left.bits right.bits

/-- Wrapping subtraction denotes centered modular subtraction. -/
@[simp, grind =] theorem toInt_wrapSub {width : Nat} (left right : FixedInt width) :
    (wrapSub left right).toInt =
      (left.toInt - right.toInt).bmod (2 ^ width) :=
  BitVec.toInt_sub

/-- Wrapping multiplication denotes centered modular multiplication. -/
@[simp, grind =] theorem toInt_wrapMul {width : Nat} (left right : FixedInt width) :
    (wrapMul left right).toInt =
      (left.toInt * right.toInt).bmod (2 ^ width) :=
  BitVec.toInt_mul left.bits right.bits

private theorem noAddOverflow_of_inRange {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt + right.toInt)) :
    left.bits.saddOverflow right.bits = false := by
  change minValue width ≤ left.bits.toInt + right.bits.toInt ∧
    left.bits.toInt + right.bits.toInt ≤ maxValue width at hresult
  rw [minValue_eq hwidth, maxValue_eq] at hresult
  simp only [BitVec.saddOverflow, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor <;> omega

private theorem noSubOverflow_of_inRange {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt - right.toInt)) :
    left.bits.ssubOverflow right.bits = false := by
  change minValue width ≤ left.bits.toInt - right.bits.toInt ∧
    left.bits.toInt - right.bits.toInt ≤ maxValue width at hresult
  rw [minValue_eq hwidth, maxValue_eq] at hresult
  simp only [BitVec.ssubOverflow, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor <;> omega

private theorem noMulOverflow_of_inRange {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt * right.toInt)) :
    left.bits.smulOverflow right.bits = false := by
  change minValue width ≤ left.bits.toInt * right.bits.toInt ∧
    left.bits.toInt * right.bits.toInt ≤ maxValue width at hresult
  rw [minValue_eq hwidth, maxValue_eq] at hresult
  simp only [BitVec.smulOverflow, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor <;> omega

/-- Checked addition succeeds when the exact sum is in range. -/
theorem checkedAdd_eq_some {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt + right.toInt)) :
    checkedAdd left right = some (wrapAdd left right) := by
  simp [checkedAdd, noAddOverflow_of_inRange hwidth left right hresult]

/-- Checked subtraction succeeds when the exact difference is in range. -/
theorem checkedSub_eq_some {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt - right.toInt)) :
    checkedSub left right = some (wrapSub left right) := by
  simp [checkedSub, noSubOverflow_of_inRange hwidth left right hresult]

/-- Checked multiplication succeeds when the exact product is in range. -/
theorem checkedMul_eq_some {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt * right.toInt)) :
    checkedMul left right = some (wrapMul left right) := by
  simp [checkedMul, noMulOverflow_of_inRange hwidth left right hresult]

/-- Wrapping addition is exact whenever its mathematical sum is in range. -/
theorem toInt_wrapAdd_of_inRange {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt + right.toInt)) :
    (wrapAdd left right).toInt = left.toInt + right.toInt := by
  apply BitVec.toInt_add_of_not_saddOverflow
  rw [noAddOverflow_of_inRange hwidth left right hresult]
  decide

/-- Wrapping subtraction is exact whenever its mathematical difference is in range. -/
theorem toInt_wrapSub_of_inRange {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt - right.toInt)) :
    (wrapSub left right).toInt = left.toInt - right.toInt := by
  apply BitVec.toInt_sub_of_not_ssubOverflow
  rw [noSubOverflow_of_inRange hwidth left right hresult]
  decide

/-- Wrapping multiplication is exact whenever its mathematical product is in range. -/
theorem toInt_wrapMul_of_inRange {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt * right.toInt)) :
    (wrapMul left right).toInt = left.toInt * right.toInt := by
  apply BitVec.toInt_mul_of_not_smulOverflow
  rw [noMulOverflow_of_inRange hwidth left right hresult]
  decide

/-- Saturating addition denotes exact addition followed by signed-range clamping. -/
@[simp, grind =] theorem toInt_saturatingAdd {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width) :
    (saturatingAdd left right).toInt = clamp width (left.toInt + right.toInt) :=
  toInt_ofIntSaturating hwidth _

/-- Saturating subtraction denotes exact subtraction followed by signed-range clamping. -/
@[simp, grind =] theorem toInt_saturatingSub {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width) :
    (saturatingSub left right).toInt = clamp width (left.toInt - right.toInt) :=
  toInt_ofIntSaturating hwidth _

/-- Saturating multiplication denotes exact multiplication followed by signed-range clamping. -/
@[simp, grind =] theorem toInt_saturatingMul {width : Nat} (hwidth : 0 < width)
    (left right : FixedInt width) :
    (saturatingMul left right).toInt = clamp width (left.toInt * right.toInt) :=
  toInt_ofIntSaturating hwidth _

end FloatLib.Numerics.Representations.FixedInt
