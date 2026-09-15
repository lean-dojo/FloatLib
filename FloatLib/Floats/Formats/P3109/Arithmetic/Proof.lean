/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Proof
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Cases

/-!
# Mathematical semantics of P3109 rational arithmetic

Finite arithmetic is exact rational arithmetic, and rational embedding into the reals preserves
the complete expression. The algebraic results here precede rounding: associativity of exact
addition does not assert associativity of rounded addition. The decoding theorems connect the
public executable operations to one report projection of that exact result.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Exact closed addition is commutative, including exceptional operands. -/
theorem add_comm (left right : NumericalValue Rat) :
    add left right = add right left := by
  cases left <;> cases right <;> simp [add, _root_.add_comm]
  rename_i left right
  cases left <;> cases right <;> rfl

/-- Exact closed multiplication is commutative, including zero times infinity. -/
theorem mul_comm (left right : NumericalValue Rat) :
    mul left right = mul right left := by
  cases left <;> cases right <;> simp [mul, _root_.mul_comm]
  rename_i left right
  cases left <;> cases right <;> rfl

/-- Exact closed addition is associative; opposite infinities remain indeterminate. -/
theorem add_assoc (left middle right : NumericalValue Rat) :
    add (add left middle) right = add left (add middle right) := by
  cases left <;> cases middle <;> cases right <;>
    (repeat' cases_type Bool) <;> simp [add, nan, _root_.add_assoc]

/-- Subtracting a finite datum from itself gives the unique exact zero. -/
@[simp] theorem sub_self (value : Rat) :
    sub (.finite value) (.finite value) = .finite 0 := by
  simp [sub, add, neg]

/-- Zero denominators are NaN, even for infinite numerators. -/
@[simp] theorem div_zero (value : NumericalValue Rat) :
    div value (.finite 0) = nan := by
  cases value <;> simp [div]

/-- Every finite numerator divided by either infinity gives the unique zero. -/
@[simp] theorem div_infinity (value : Rat) (negative : Bool) :
    div (.finite value) (.infinity negative) = .finite 0 :=
  rfl

/-- Finite nonzero division cancels before any destination rounding. -/
theorem div_mul_cancel (left right : Rat) (hright : right ≠ 0) :
    mul (div (.finite left) (.finite right)) (.finite right) = .finite left := by
  simp [div, mul, hright]

/-- Finite fused multiply-add retains the whole rational expression. -/
@[simp] theorem fma_finite (left right addend : Rat) :
    fma (.finite left) (.finite right) (.finite addend) =
      .finite (left * right + addend) :=
  rfl

/-- Fused add-add is independent of the grouping of the exact additions. -/
theorem faa_eq_add_add (left middle right : NumericalValue Rat) :
    faa left middle right = add left (add middle right) :=
  add_assoc left middle right

/-- Rational addition embeds as addition in the reals. -/
theorem add_finite_real (left right : Rat) :
    (add (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) + (right : Real)) := by
  simp [add, NumericalValue.map]

/-- Rational subtraction embeds as subtraction in the reals. -/
theorem sub_finite_real (left right : Rat) :
    (sub (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) - (right : Real)) := by
  simp [sub, add, neg, NumericalValue.map, sub_eq_add_neg]

/-- Rational multiplication embeds as multiplication in the reals. -/
theorem mul_finite_real (left right : Rat) :
    (mul (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) * (right : Real)) := by
  simp [mul, NumericalValue.map]

/-- Nonzero rational division embeds as division in the reals. -/
theorem div_finite_real (left right : Rat) (hright : right ≠ 0) :
    (div (.finite left) (.finite right)).map (fun value : Rat => (value : Real)) =
      .finite ((left : Real) / (right : Real)) := by
  simp [div, NumericalValue.map, hright]

/-- FMA computes the real expression with no rounded intermediate product. -/
theorem fma_finite_real (left right addend : Rat) :
    (fma (.finite left) (.finite right) (.finite addend)).map
        (fun value : Rat => (value : Real)) =
      .finite ((left : Real) * (right : Real) + (addend : Real)) := by
  simp [NumericalValue.map]

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source leftFormat rightFormat thirdFormat : Format}

/-- The executable unary operation decodes to one projection of its exact closed result. -/
theorem decode_unaryTo (destination : Format) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat)
    (value : ExecFloat.P3109 source) :
    Format.SameDatum (decode (unaryTo destination policy operation value))
      (destination.projectRatValue policy (operation value.toClosedRat)) :=
  decode_projectRat policy _

/-- The executable binary operation decodes to one projection of its exact closed result. -/
theorem decode_binaryTo (destination : Format) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat) :
    Format.SameDatum (decode (binaryTo destination policy operation left right))
      (destination.projectRatValue policy (operation left.toClosedRat right.toClosedRat)) :=
  decode_projectRat policy _

/-- The executable fused operation decodes to one projection of the whole exact expression. -/
theorem decode_ternaryTo (destination : Format) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (third : ExecFloat.P3109 thirdFormat) :
    Format.SameDatum (decode (ternaryTo destination policy operation left right third))
      (destination.projectRatValue policy
        (operation left.toClosedRat right.toClosedRat third.toClosedRat)) :=
  decode_projectRat policy _

/-- Finite FMA is one projection of the exact rational product plus addend. -/
theorem decode_fmaTo_finite (destination : Format) (policy : ProjectionPolicy)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (addend : ExecFloat.P3109 thirdFormat) (x y z : Rat)
    (hleft : left.toClosedRat = .finite x) (hright : right.toClosedRat = .finite y)
    (haddend : addend.toClosedRat = .finite z) :
    Format.SameDatum (decode (fmaTo destination policy left right addend))
      (destination.projectRatValue policy (.finite (x * y + z))) := by
  simpa [fmaTo, hleft, hright, haddend] using
    decode_ternaryTo destination policy Arithmetic.fma left right addend

end FloatLib.Floats.ExecFloat.P3109
