/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.ExtendedRat.Runtime
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.CasesM

/-!
# Algebra of closed extended-rational arithmetic

Exact addition is associative and commutative; multiplication is commutative. The finite
operations agree with rational arithmetic, and casting to the reals preserves their complete
expressions. These statements concern exact values before any format-specific projection.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Exact closed addition is commutative, including exceptional operands. -/
theorem add_comm (left right : NumericalValue Rat) :
    Add left right = Add right left := by
  cases left <;> cases right <;> simp only [Add, _root_.add_comm, beq_iff_eq]
  rename_i left right
  cases left <;> cases right <;> rfl

/-- Exact closed multiplication is commutative, including zero times infinity. -/
theorem mul_comm (left right : NumericalValue Rat) :
    Multiply left right = Multiply right left := by
  cases left <;> cases right <;> simp only [Multiply, _root_.mul_comm, beq_iff_eq,
    NumericalValue.infinity.injEq]
  rename_i left right
  cases left <;> cases right <;> rfl

/-- Exact closed addition is associative, and opposite infinities stay indeterminate. -/
theorem add_assoc (left middle right : NumericalValue Rat) :
    Add (Add left middle) right = Add left (Add middle right) := by
  cases left <;> cases middle <;> cases right <;>
    (repeat' cases_type Bool) <;> simp [Add, nan, _root_.add_assoc]

/-- Subtracting a finite datum from itself gives the unique exact zero. -/
@[simp] theorem sub_self (value : Rat) :
    Subtract (.finite value) (.finite value) = .finite 0 := by
  simp [Subtract, Add, Negate]

/-- Zero denominators are NaN, even for infinite numerators. -/
@[simp] theorem div_zero (value : NumericalValue Rat) :
    Divide value (.finite 0) = nan := by
  cases value <;> simp [Divide]

/-- Every finite numerator divided by either infinity gives the unique zero. -/
@[simp] theorem div_infinity (value : Rat) (negative : Bool) :
    Divide (.finite value) (.infinity negative) = .finite 0 :=
  rfl

/-- Finite nonzero division cancels before any destination rounding. -/
theorem div_mul_cancel (left right : Rat) (hright : right ≠ 0) :
    Multiply (Divide (.finite left) (.finite right)) (.finite right) = .finite left := by
  simp [Divide, Multiply, hright]

/-- Finite fused multiply-add retains the whole rational expression. -/
@[simp] theorem fma_finite (left right addend : Rat) :
    FMA (.finite left) (.finite right) (.finite addend) =
      .finite (left * right + addend) :=
  rfl

/-- Fused add-add is independent of the grouping of the exact additions. -/
theorem faa_eq_add_add (left middle right : NumericalValue Rat) :
    FAA left middle right = Add left (Add middle right) :=
  add_assoc left middle right

/-- Rational addition embeds as addition in the reals. -/
theorem add_finite_real (left right : Rat) :
    (Add (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) + (right : Real)) := by
  simp [Add, NumericalValue.map]

/-- Rational subtraction embeds as subtraction in the reals. -/
theorem sub_finite_real (left right : Rat) :
    (Subtract (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) - (right : Real)) := by
  simp [Subtract, Add, Negate, NumericalValue.map, sub_eq_add_neg]

/-- Rational multiplication embeds as multiplication in the reals. -/
theorem mul_finite_real (left right : Rat) :
    (Multiply (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) * (right : Real)) := by
  simp [Multiply, NumericalValue.map]

/-- Nonzero rational division embeds as division in the reals. -/
theorem div_finite_real (left right : Rat) (hright : right ≠ 0) :
    (Divide (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) / (right : Real)) := by
  simp [Divide, NumericalValue.map, hright]

/-- FMA computes the real expression with no rounded intermediate product. -/
theorem fma_finite_real (left right addend : Rat) :
    (FMA (.finite left) (.finite right) (.finite addend)).map
        (fun value : Rat => (value : Real)) =
      .finite ((left : Real) * (right : Real) + (addend : Real)) := by
  simp [NumericalValue.map]

end FloatLib.Floats.Formats.P3109.Arithmetic
