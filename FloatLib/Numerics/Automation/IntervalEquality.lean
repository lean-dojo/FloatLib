/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Numerics.Automation.IntervalReify

/-!
# Equalities for reified interval expressions

Congruence combines the equalities of individual operands. Rational leaves use the certificates
from `norm_num`; variables agree by reduction with their entries in the input environment.
This avoids simplifying the entire expanded expression and every coordinate lookup together.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

/-- Match unary operands with the same definitional unfolding used by the reifier. -/
private def unaryOperand (op : Q(UnaryOp)) (source : Q(ℝ)) : MetaM Q(ℝ) := do
  match op, source with
  | ~q(UnaryOp.neg), ~q(-$a) => return a
  | ~q(UnaryOp.abs), ~q(abs $a) => return a
  | ~q(UnaryOp.inv), ~q($a⁻¹) => return a
  | ~q(UnaryOp.pow $n), ~q($a ^ ($m : Nat)) =>
    unless ← isDefEq n m do throwError "interval found inconsistent natural powers"
    return a
  | ~q(UnaryOp.exp), ~q(Real.exp $a) => return a
  | ~q(UnaryOp.log), ~q(Real.log $a) => return a
  | ~q(UnaryOp.sin), ~q(Real.sin $a) => return a
  | ~q(UnaryOp.cos), ~q(Real.cos $a) => return a
  | ~q(UnaryOp.tan), ~q(Real.tan $a) => return a
  | ~q(UnaryOp.asin), ~q(Real.arcsin $a) => return a
  | ~q(UnaryOp.acos), ~q(Real.arccos $a) => return a
  | ~q(UnaryOp.atan), ~q(Real.arctan $a) => return a
  | ~q(UnaryOp.sinh), ~q(Real.sinh $a) => return a
  | ~q(UnaryOp.cosh), ~q(Real.cosh $a) => return a
  | ~q(UnaryOp.tanh), ~q(Real.tanh $a) => return a
  | ~q(UnaryOp.sqrt), ~q(Real.sqrt $a) => return a
  | _, _ => throwError "interval could not recover the operand of {source}"

/-- Match binary operands without assuming that a local definition is a literal application. -/
private def binaryOperands (op : Q(BinaryOp)) (source : Q(ℝ)) :
    MetaM (Q(ℝ) × Q(ℝ)) := do
  match op, source with
  | ~q(BinaryOp.add), ~q($a + $b) => return (a, b)
  | ~q(BinaryOp.sub), ~q($a - $b) => return (a, b)
  | ~q(BinaryOp.mul), ~q($a * $b) => return (a, b)
  | ~q(BinaryOp.div), ~q($a / $b) => return (a, b)
  | ~q(BinaryOp.min), ~q(min $a $b) => return (a, b)
  | ~q(BinaryOp.max), ~q(max $a $b) => return (a, b)
  | _, _ => throwError "interval could not recover the operands of {source}"

/--
Prove that a source expression equals the real interpretation of its reified expression.

The source and syntax follow the same arithmetic operations. A variable's source term must
agree definitionally with its environment entry; no numerical evaluation of a real atom is used.
-/
partial def evalEquality (source : Q(ℝ)) (expression : Q(Interval.Expr))
    (values : Q(Nat → ℝ)) (cache : RationalCache) : MetaM Lean.Expr := do
  let source : Q(ℝ) ← pure source.consumeMData
  match expression with
  | ~q(Interval.Expr.const $c) =>
    let some value := cache.get? source
      | throwError "interval could not recover the rational value of {source}"
    unless ← isDefEq value.rational c do
      throwError "interval found inconsistent rational expressions"
    return value.equality
  | ~q(Interval.Expr.var $_i) => mkEqRefl source
  | ~q(Interval.Expr.unary $op $a) =>
    let input ← unaryOperand op source
    let h ← evalEquality input a values cache
    mkCongrArg q(UnaryOp.eval $op) h
  | ~q(Interval.Expr.binary $op $a $b) =>
    let (left, right) ← binaryOperands op source
    let hleft ← evalEquality left a values cache
    let hright ← evalEquality right b values cache
    mkCongr (← mkCongrArg q(BinaryOp.eval $op) hleft) hright
  | ~q(Interval.Expr.ternary $op $a $b $c) =>
    let ~q($first * $second + $third) := source
      | throwError "interval could not recover the multiply-add operands of {source}"
    let hfirst ← evalEquality first a values cache
    let hsecond ← evalEquality second b values cache
    let hthird ← evalEquality third c values cache
    mkCongr (← mkCongr (← mkCongrArg q(TernaryOp.eval $op) hfirst) hsecond) hthird
  | _ => throwError "interval could not interpret its reified expression"

end FloatLib.Numerics.Interval.Tactic
