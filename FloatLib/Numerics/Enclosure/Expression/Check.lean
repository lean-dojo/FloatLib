/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic

/-!
# Checking real inequalities on rational boxes

`Expr.check` evaluates an interval expression and checks its decoded upper bound against zero.
An inconclusive evaluation can subdivide the widest positive-width input interval at its exact
rational midpoint. Both children must succeed. Precision and elementary-function approximation
settings belong to the backend; the checker controls only the subdivision depth.

Input coordinates have explicit rational bounds. A missing variable, failed endpoint conversion,
or rejected operation makes a leaf fail. `CheckProof` proves that successful checks establish the
inequality for every real assignment in the original box.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Rational bounds for variables numbered from zero. -/
abbrev Box := List (Interval ℚ)

/-- Whether the expression must be nonpositive or strictly negative throughout the box. -/
inductive Relation where
  | nonpositive
  | negative
  deriving DecidableEq, Repr

/-- Test a rational upper bound against zero. -/
def Relation.check (relation : Relation) (hi : ℚ) : Bool :=
  match relation with
  | .nonpositive => decide (hi ≤ 0)
  | .negative => decide (hi < 0)

/-- Enclose both rational endpoints and keep the outward-facing bounds. -/
def Backend.encloseInterval? {α : Type*} (B : Backend α)
    (I : Interval ℚ) : Option (Interval α) := do
  let lower ← B.const? I.lo
  let upper ← B.const? I.hi
  pure ⟨lower.lo, upper.hi⟩

/-- Enclose every coordinate, failing if either endpoint of any coordinate cannot be enclosed. -/
def Box.enclose? {α : Type*} (box : Box) (B : Backend α) :
    Option (List (Interval α)) :=
  match box with
  | [] => some []
  | I :: tail => do
    let J ← B.encloseInterval? I
    let rest ← Box.enclose? tail B
    pure (J :: rest)

/-- Index and width of the widest positive-width coordinate; ties choose the first coordinate. -/
def Box.widest? (box : Box) : Option (Nat × ℚ) :=
  match box with
  | [] => none
  | I :: tail =>
    let later := (Box.widest? tail).map (fun (i, width) => (i + 1, width))
    let width := I.hi - I.lo
    if 0 < width then
      match later with
      | none => some (0, width)
      | some (i, other) => if width < other then some (i, other) else some (0, width)
    else later

/--
Bisect the widest positive-width coordinate at its exact rational midpoint.

The two closed children share the midpoint and cover the original box.
-/
def Box.bisect? (box : Box) : Option (Box × Box) := do
  let (i, _) ← box.widest?
  let I ← box[i]?
  if I.lo < I.hi then
    let mid := (I.lo + I.hi) / 2
    pure (box.set i ⟨I.lo, mid⟩, box.set i ⟨mid, I.hi⟩)
  else none

/-- Check one box using the decoded upper endpoint of a successful expression evaluation. -/
def Expr.checkBox {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) : Bool :=
  match box.enclose? B with
  | none => false
  | some intervals =>
    match e.eval? B (fun i => intervals[i]?) with
    | none => false
    | some I =>
      match B.decode I.hi with
      | none => false
      | some hi => relation.check hi

/--
Check a real inequality, subdividing inconclusive boxes up to the supplied depth.

Depth zero performs a single interval evaluation. A split succeeds only when both children
succeed, including when the original evaluation rejected an operation's domain.
-/
def Expr.check {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) (depth : Nat) : Bool :=
  if e.checkBox B relation box then true
  else
    match depth with
    | 0 => false
    | depth + 1 =>
      match box.bisect? with
      | none => false
      | some (left, right) =>
        e.check B relation left depth && e.check B relation right depth

end FloatLib.Numerics.Interval
