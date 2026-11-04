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
differences, and products. A checked operation returns the wrapped result when the exact value is in
range (`checkedAdd_eq_some`) and `none` exactly when it isn't (`checkedAdd_eq_none_iff`).

On purpose, the file stops short of the library-wide operation interface. `Refinement` builds that
reusable layer from these concrete facts, which keeps low-level overflow reasoning out of generic
numerical proofs.
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

/--
The signed overflow test of `BitVec`, applied to an exact integer result at a positive width, is
clear exactly when the result is in range. Width zero is handled by each operation.
-/
private theorem overflowTest_eq_false_iff {width : Nat} (hwidth : 0 < width) (result : Int) :
    (decide (result ≥ 2 ^ (width - 1)) || decide (result < -2 ^ (width - 1))) = false ↔
      InRange width result := by
  change _ ↔ minValue width ≤ result ∧ result ≤ maxValue width
  rw [minValue_eq hwidth, maxValue_eq]
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

private theorem saddOverflow_eq_false_iff {width : Nat} (left right : FixedInt width) :
    left.bits.saddOverflow right.bits = false ↔ InRange width (left.toInt + right.toInt) := by
  rcases Nat.eq_zero_or_pos width with rfl | hwidth
  · simp [BitVec.saddOverflow, BitVec.toInt_zero_length, InRange, minValue, maxValue, toInt]
  exact overflowTest_eq_false_iff hwidth _

private theorem ssubOverflow_eq_false_iff {width : Nat} (left right : FixedInt width) :
    left.bits.ssubOverflow right.bits = false ↔ InRange width (left.toInt - right.toInt) := by
  rcases Nat.eq_zero_or_pos width with rfl | hwidth
  · simp [BitVec.ssubOverflow, BitVec.toInt_zero_length, InRange, minValue, maxValue, toInt]
  exact overflowTest_eq_false_iff hwidth _

private theorem smulOverflow_eq_false_iff {width : Nat} (left right : FixedInt width) :
    left.bits.smulOverflow right.bits = false ↔ InRange width (left.toInt * right.toInt) := by
  rcases Nat.eq_zero_or_pos width with rfl | hwidth
  · simp [BitVec.smulOverflow, BitVec.toInt_zero_length, InRange, minValue, maxValue, toInt]
  exact overflowTest_eq_false_iff hwidth _

/-- Checked addition succeeds when the exact sum is in range. -/
theorem checkedAdd_eq_some {width : Nat}
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt + right.toInt)) :
    checkedAdd left right = some (wrapAdd left right) := by
  simp [checkedAdd, (saddOverflow_eq_false_iff left right).2 hresult]

/-- Checked subtraction succeeds when the exact difference is in range. -/
theorem checkedSub_eq_some {width : Nat}
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt - right.toInt)) :
    checkedSub left right = some (wrapSub left right) := by
  simp [checkedSub, (ssubOverflow_eq_false_iff left right).2 hresult]

/-- Checked multiplication succeeds when the exact product is in range. -/
theorem checkedMul_eq_some {width : Nat}
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt * right.toInt)) :
    checkedMul left right = some (wrapMul left right) := by
  simp [checkedMul, (smulOverflow_eq_false_iff left right).2 hresult]

/-- Checked addition returns `none` exactly when the exact sum is out of range. -/
theorem checkedAdd_eq_none_iff {width : Nat} (left right : FixedInt width) :
    checkedAdd left right = none ↔ ¬InRange width (left.toInt + right.toInt) := by
  rw [← saddOverflow_eq_false_iff]
  cases h : left.bits.saddOverflow right.bits <;> simp [checkedAdd, h]

/-- Checked subtraction returns `none` exactly when the exact difference is out of range. -/
theorem checkedSub_eq_none_iff {width : Nat} (left right : FixedInt width) :
    checkedSub left right = none ↔ ¬InRange width (left.toInt - right.toInt) := by
  rw [← ssubOverflow_eq_false_iff]
  cases h : left.bits.ssubOverflow right.bits <;> simp [checkedSub, h]

/-- Checked multiplication returns `none` exactly when the exact product is out of range. -/
theorem checkedMul_eq_none_iff {width : Nat} (left right : FixedInt width) :
    checkedMul left right = none ↔ ¬InRange width (left.toInt * right.toInt) := by
  rw [← smulOverflow_eq_false_iff]
  cases h : left.bits.smulOverflow right.bits <;> simp [checkedMul, h]

/-- Wrapping addition is exact whenever its mathematical sum is in range. -/
theorem toInt_wrapAdd_of_inRange {width : Nat}
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt + right.toInt)) :
    (wrapAdd left right).toInt = left.toInt + right.toInt := by
  apply BitVec.toInt_add_of_not_saddOverflow
  rw [(saddOverflow_eq_false_iff left right).2 hresult]
  decide

/-- Wrapping subtraction is exact whenever its mathematical difference is in range. -/
theorem toInt_wrapSub_of_inRange {width : Nat}
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt - right.toInt)) :
    (wrapSub left right).toInt = left.toInt - right.toInt := by
  apply BitVec.toInt_sub_of_not_ssubOverflow
  rw [(ssubOverflow_eq_false_iff left right).2 hresult]
  decide

/-- Wrapping multiplication is exact whenever its mathematical product is in range. -/
theorem toInt_wrapMul_of_inRange {width : Nat}
    (left right : FixedInt width)
    (hresult : InRange width (left.toInt * right.toInt)) :
    (wrapMul left right).toInt = left.toInt * right.toInt := by
  apply BitVec.toInt_mul_of_not_smulOverflow
  rw [(smulOverflow_eq_false_iff left right).2 hresult]
  decide

/-- Saturating addition denotes exact addition followed by signed-range clamping. -/
@[simp, grind =] theorem toInt_saturatingAdd {width : Nat}
    (left right : FixedInt width) :
    (saturatingAdd left right).toInt = clamp width (left.toInt + right.toInt) :=
  toInt_ofIntSaturating _

/-- Saturating subtraction denotes exact subtraction followed by signed-range clamping. -/
@[simp, grind =] theorem toInt_saturatingSub {width : Nat}
    (left right : FixedInt width) :
    (saturatingSub left right).toInt = clamp width (left.toInt - right.toInt) :=
  toInt_ofIntSaturating _

/-- Saturating multiplication denotes exact multiplication followed by signed-range clamping. -/
@[simp, grind =] theorem toInt_saturatingMul {width : Nat}
    (left right : FixedInt width) :
    (saturatingMul left right).toInt = clamp width (left.toInt * right.toInt) :=
  toInt_ofIntSaturating _

end FloatLib.Numerics.Representations.FixedInt
