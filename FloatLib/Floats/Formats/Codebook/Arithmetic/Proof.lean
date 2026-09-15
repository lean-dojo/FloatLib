/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Arithmetic.Runtime
public import FloatLib.Numerics.Operation.Semantics
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Correctness of catalog-codebook arithmetic

For the one-bit bipolar and two-bit ternary catalog tables, negation and multiplication agree
with the corresponding integer operations on finite inputs. The proofs enumerate these tables'
stored words. The ternary refinement statements assume finite operands; separate rejection
theorems cover multiplication with a reserved operand.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Codebook

private theorem bitVec1_cases (x : BitVec 1) :
    x = BitVec.ofNat 1 0 ∨ x = BitVec.ofNat 1 1 := by
  revert x
  decide

private theorem bitVec2_cases (x : BitVec 2) :
    x = BitVec.ofNat 2 0 ∨ x = BitVec.ofNat 2 1 ∨
      x = BitVec.ofNat 2 2 ∨ x = BitVec.ofNat 2 3 := by
  revert x
  decide

namespace Catalog.bipolar1

/-- Bipolar negation exactly refines integer negation. -/
theorem neg_refines :
    Operation.Finite1 Catalog.bipolar1.numericalSystem
      Catalog.bipolar1.numericalSystem neg (fun x : ℤ => -x) := by
  intro code value hvalue
  rcases bitVec1_cases code with hcode | hcode <;> subst code
  all_goals
    simp [NumericalSystem.Represents, Codebook.numericalSystem,
      Catalog.bipolar1] at hvalue
  all_goals
    injection hvalue with hvalue
    subst value
    simp [NumericalSystem.Represents, Codebook.numericalSystem,
      Catalog.bipolar1, neg]

/-- Bipolar multiplication exactly refines integer multiplication. -/
theorem mul_refines :
    Operation.Finite2 Catalog.bipolar1.numericalSystem
      Catalog.bipolar1.numericalSystem Catalog.bipolar1.numericalSystem
      mul (fun x y : ℤ => x * y) := by
  intro left right x y hx hy
  rcases bitVec1_cases left with hleft | hleft <;> subst left <;>
    rcases bitVec1_cases right with hright | hright <;> subst right
  all_goals
    simp [NumericalSystem.Represents, Codebook.numericalSystem,
      Catalog.bipolar1] at hx hy
  all_goals
    injection hx with hx
    injection hy with hy
    subst x
    subst y
    simp [NumericalSystem.Represents, Codebook.numericalSystem,
      Catalog.bipolar1, mul]

end Catalog.bipolar1

namespace Catalog.ternary2

/-- A reserved left operand is rejected, including when the right operand is zero. -/
@[simp] theorem mul_reserved_left (x : Code Catalog.ternary2) :
    mul? (BitVec.ofNat 2 3) x = none := by
  rcases bitVec2_cases x with h | h | h | h <;> subst x <;> rfl

/-- A reserved right operand is rejected, including when the left operand is zero. -/
@[simp] theorem mul_reserved_right (x : Code Catalog.ternary2) :
    mul? x (BitVec.ofNat 2 3) = none := by
  rcases bitVec2_cases x with h | h | h | h <;> subst x <;> rfl

/-- Checked ternary negation exactly refines integer negation on finite inputs. -/
theorem neg_refines :
    Operation.Checked1 Catalog.ternary2.numericalSystem
      Catalog.ternary2.numericalSystem neg? (fun x : ℤ => .finite (-x)) := by
  intro code value hvalue
  rcases bitVec2_cases code with hcode | hcode | hcode | hcode <;> subst code
  all_goals
    simp [NumericalSystem.Represents, Codebook.numericalSystem,
      Catalog.ternary2] at hvalue
  all_goals
    injection hvalue with hvalue
    subst value
    simp [Codebook.Code, Codebook.numericalSystem, Catalog.ternary2, neg?]

/-- Checked ternary multiplication exactly refines integer multiplication on finite inputs. -/
theorem mul_refines :
    Operation.Checked2 Catalog.ternary2.numericalSystem
      Catalog.ternary2.numericalSystem Catalog.ternary2.numericalSystem
      mul? (fun x y : ℤ => .finite (x * y)) := by
  intro left right x y hx hy
  rcases bitVec2_cases left with hleft | hleft | hleft | hleft <;> subst left <;>
    rcases bitVec2_cases right with hright | hright | hright | hright <;> subst right
  all_goals
    simp [NumericalSystem.Represents, Codebook.numericalSystem,
      Catalog.ternary2] at hx hy
  all_goals
    injection hx with hx
    injection hy with hy
    subst x
    subst y
    simp [Codebook.Code, Codebook.numericalSystem, Catalog.ternary2, mul?]

end Catalog.ternary2

end FloatLib.Floats.Formats.Codebook
