/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval.Aggregates
public import FloatLib.Numerics.Automation.Interval.Registry
public import FloatLib.Numerics.Enclosure.Expression.Real
public import Mathlib.Tactic.NormNum
public meta import FloatLib.Numerics.Enclosure.Expression.Basic
public meta import Mathlib.Util.Qq

/-!
# Reification for interval proofs

The interval tactic translates real arithmetic into the common expression language and proves
its real interpretation equal to the original expression. Numerical constants carry `norm_num`
certificates. Unrecognized subexpressions become atoms whose bounds are collected by `Bounds`.
One state keeps atom indices, shared syntax, and the certificates needed for equality proofs.
-/

public section

namespace FloatLib.Numerics.Interval.Tactic

open Mathlib.Meta.NormNum

/-- Interpret the rational certificate produced by `norm_num` as a real equality. -/
theorem eq_rat_of_isRat {x : ℝ} {n : ℤ} {d : ℕ} (h : IsRat x n d) :
    x = ((mkRat n d : ℚ) : ℝ) := by
  rw [Rat.cast_mkRat_of_ne_zero n h.den_nz]
  exact h.to_raw_eq

end FloatLib.Numerics.Interval.Tactic

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

open Mathlib.Meta.NormNum

/-- A rational value, its syntax, and a proof that a real expression has that value. -/
structure RationalValue (e : Q(ℝ)) where
  /-- The normalized rational value, used when comparing candidate bounds. -/
  value : ℚ
  /-- Quoted rational expression for the value. -/
  rational : Q(ℚ)
  /-- Proof that the original real expression equals this rational. -/
  equality : Q($e = ($rational : ℝ))

/-- Obtain a rational certificate using the registered `norm_num` extensions. -/
def deriveRationalValue (e : Q(ℝ)) : MetaM (RationalValue e) := do
  let ⟨value, n, d, h⟩ ← deriveRat e q(inferInstance)
  let rational : Q(ℚ) := q(mkRat $n $d)
  let equality : Lean.Expr := q(eq_rat_of_isRat $h)
  return ⟨value, rational, equality⟩

/-- Recognize a closed rational expression, exposing numerical coercions when necessary. -/
def rationalValue? (e : Q(ℝ)) : MetaM (Option (RationalValue e)) := do
  let reduced : Q(ℝ) ← zetaReduce e
  if reduced.hasFVar then return none
  try
    let value ← deriveRationalValue reduced
    return some ⟨value.value, value.rational, value.equality⟩
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    try
      let normalized ← normalizeAggregateNumerals reduced
      if normalized.expr == reduced then return none
      let scalar : Q(ℝ) := normalized.expr
      let value ← deriveRationalValue scalar
      let equality ← mkEqTrans (← normalized.getProof) value.equality
      return some ⟨value.value, value.rational, equality⟩
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      return none

/-- Share reified subexpressions and retain their rational certificates. -/
structure ReifyState where
  /-- Real atoms in variable-index order. -/
  atoms : Array Q(ℝ) := #[]
  /-- Equalities relating real leaves to their reified rational constants. -/
  rationals : Lean.ExprMap Lean.Expr := {}
  /-- Reified expressions, including atoms and repeated scalar subexpressions. -/
  expressions : Lean.ExprMap Q(Interval.Expr) := {}
  /-- Registration names, in call-index order. -/
  extensions : Array Name := #[]
  /-- Source arguments of registered calls, retained for their equality proofs. -/
  calls : Lean.ExprMap (Array Q(ℝ)) := {}

/-- Reuse an atom index, or add a previously unseen real subexpression. -/
private def reifyAtom (e : Q(ℝ)) : StateRefT ReifyState MetaM Q(Interval.Expr) := do
  let atoms := (← get).atoms
  if let some index := atoms.findIdx? (· == e) then
    let index : Q(Nat) := mkNatLit index
    return q(Interval.Expr.var $index)
  let index : Q(Nat) := mkNatLit atoms.size
  modify fun state => { state with atoms := state.atoms.push e }
  return q(Interval.Expr.var $index)

/--
Reify real arithmetic, natural powers, and elementary functions.

Registered functions and rational constants are recognized before the structural cases.
An unsupported operation is kept
as an atom, so the caller must supply an interval for that complete real subexpression.
-/
partial def reify (e : Q(ℝ)) :
    StateRefT ReifyState MetaM Q(Interval.Expr) := do
  let e : Q(ℝ) ← pure e.consumeMData
  if let some result := (← get).expressions.get? e then return result
  let result ← build e
  modify fun cache ↦ { cache with expressions := cache.expressions.insert e result }
  return result
where
  /-- Recognize a scalar expression that has not yet been reified. -/
  build (e : Q(ℝ)) :
      StateRefT ReifyState MetaM Q(Interval.Expr) := do
    if let some (proof, realArgs) ← registeredApplication? e then
      let cache ← get
      let index := cache.extensions.findIdx? (· == proof) |>.getD cache.extensions.size
      if index == cache.extensions.size then
        modify fun cache => { cache with extensions := cache.extensions.push proof }
      let quotedIndex : Q(Nat) := mkNatLit index
      modify fun cache => { cache with calls := cache.calls.insert e realArgs }
      let mut expressions : Q(List Interval.Expr) := q([])
      for arg in realArgs.reverse do
        let expression ← reify arg
        expressions := q($expression :: $expressions)
      return q(Interval.Expr.call $quotedIndex $expressions)
    if let some value ← rationalValue? e then
      modify fun cache ↦
        { cache with rationals := cache.rationals.insert e value.equality }
      let q := value.rational
      return q(Interval.Expr.const $q)
    match e with
    | ~q($a * $b + $c) => do
      let a ← reify a
      let b ← reify b
      let c ← reify c
      return q(Interval.Expr.ternary .fma $a $b $c)
    | ~q($a + $b) => binary q(BinaryOp.add) a b
    | ~q($a - $b) => binary q(BinaryOp.sub) a b
    | ~q($a * $b) => binary q(BinaryOp.mul) a b
    | ~q($a / $b) => binary q(BinaryOp.div) a b
    | ~q(min $a $b) => binary q(BinaryOp.min) a b
    | ~q(max $a $b) => binary q(BinaryOp.max) a b
    | ~q(-$a) => unary q(UnaryOp.neg) a
    | ~q(abs $a) => unary q(UnaryOp.abs) a
    | ~q($a⁻¹) => unary q(UnaryOp.inv) a
    | ~q($a ^ ($n : Nat)) =>
      let n : Q(Nat) ← whnf n
      if let some value := n.rawNatLit? then
        let n : Q(Nat) := mkNatLit value
        let a ← reify a
        return q(Interval.Expr.unary (.pow $n) $a)
      reifyAtom e
    | _ => reifyAtom e
  /-- Reify one operand and apply its quoted unary operation. -/
  unary (op : Q(UnaryOp)) (a : Q(ℝ)) : StateRefT ReifyState MetaM Q(Interval.Expr) := do
    let a ← reify a
    return q(Interval.Expr.unary $op $a)
  /-- Reify two operands and apply their quoted binary operation. -/
  binary (op : Q(BinaryOp)) (a b : Q(ℝ)) : StateRefT ReifyState MetaM Q(Interval.Expr) := do
    let a ← reify a
    let b ← reify b
    return q(Interval.Expr.binary $op $a $b)

/-- Match unary operands with the same definitional unfolding used by the reifier. -/
private def unaryOperand (op : Q(UnaryOp)) (source : Q(ℝ)) : MetaM Q(ℝ) := do
  match op, source with
  | ~q(UnaryOp.neg), ~q(-$a) => return a
  | ~q(UnaryOp.abs), ~q(abs $a) => return a
  | ~q(UnaryOp.inv), ~q($a⁻¹) => return a
  | ~q(UnaryOp.pow $n), ~q($a ^ ($m : Nat)) =>
    unless ← isDefEq n m do throwError "interval found inconsistent natural powers"
    return a
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
    (values : Q(Nat → ℝ)) (cache : ReifyState)
    (functions : Q(Nat → List ℝ → ℝ)) : MetaM Lean.Expr := do
  let source : Q(ℝ) ← pure source.consumeMData
  match expression with
  | ~q(Interval.Expr.const $c) =>
    let some equality := cache.rationals.get? source
      | throwError "interval could not recover the rational value of {source}"
    unless ← isDefEq (← inferType equality) q($source = ($c : ℝ)) do
      throwError "interval found inconsistent rational expressions"
    return equality
  | ~q(Interval.Expr.var $_i) => mkEqRefl source
  | ~q(Interval.Expr.unary $op $a) =>
    let input ← unaryOperand op source
    let h ← evalEquality input a values cache functions
    mkCongrArg q(UnaryOp.eval $op) h
  | ~q(Interval.Expr.binary $op $a $b) =>
    let (left, right) ← binaryOperands op source
    let hleft ← evalEquality left a values cache functions
    let hright ← evalEquality right b values cache functions
    mkCongr (← mkCongrArg q(BinaryOp.eval $op) hleft) hright
  | ~q(Interval.Expr.ternary $op $a $b $c) =>
    let ~q($first * $second + $third) := source
      | throwError "interval could not recover the multiply-add operands of {source}"
    let hfirst ← evalEquality first a values cache functions
    let hsecond ← evalEquality second b values cache functions
    let hthird ← evalEquality third c values cache functions
    mkCongr (← mkCongr (← mkCongrArg q(TernaryOp.eval $op) hfirst) hsecond) hthird
  | ~q(Interval.Expr.call $index $args) =>
    let some inputs := cache.calls.get? source
      | throwError "interval could not recover registered arguments of {source}"
    let mut sourceArgs : Q(List ℝ) := q([])
    let mut equality : Lean.Expr := ← mkEqRefl sourceArgs
    let mut nodes := args
    let mut expressions : Array Q(Interval.Expr) := #[]
    for _ in inputs do
      let ~q($head :: $tail) := nodes
        | throwError "interval found inconsistent registered arguments"
      expressions := expressions.push head
      nodes := tail
    for input in inputs.reverse, expression in expressions.reverse do
      let h ← evalEquality input expression values cache functions
      equality ← mkCongr (← mkCongrArg q(List.cons (α := ℝ)) h) equality
      sourceArgs := q($input :: $sourceArgs)
    let sourceEquality ← mkEqRefl source
    unless ← isDefEq source q($functions $index $sourceArgs) do
      throwError "interval found an inconsistent registered real function"
    mkEqTrans sourceEquality (← mkCongrArg q($functions $index) equality)
  | _ => throwError "interval could not interpret its reified expression"

end FloatLib.Numerics.Interval.Tactic
