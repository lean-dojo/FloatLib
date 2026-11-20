/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Form

/-!
# Checking that a constraint set has no point in a rational box

A `Constraint` combines atoms by `and` and `or`. An atom `fails relation e` says that the relation
(`e ≤ 0` or `e < 0`) does not hold of the interval expression `e`, so `0 < e` and `0 ≤ e` are the
two kinds of atom, and an equality is the conjunction of two of them. An atom `form strict f` says
that a quadratic form is nonpositive, or negative when `strict`. Negations are pushed to the
atoms before a constraint is built, which is why there is no constructor for them.

A `Refutation` is a certificate that a constraint has no point in a box: a tree whose inner nodes
cut the box along one coordinate and whose leaves say which part of the constraint is false on the
whole leaf box. `Constraint.refutes` checks a certificate. It evaluates an expression only at a
leaf, and only the atom that the leaf names, with the checker of `Check` (`Expr.checkZero`), so
a leaf may also ask for that checker's own bisection. `ConstraintProof` proves that an accepted
certificate excludes every real point of the box (`Constraint.refutes_sound`).

At a boundary, subdivision alone can leave a constraint undecided. If a form's matrix is
positive definite on the box (`Form.definiteOn`), the form cannot be negative (`definite`).
If the form is nonpositive, all its coordinates vanish. The `pin` certificate checks the
remaining constraints with those coordinates fixed.

The search for a certificate is not part of the check: `FloatLib.Tactic.Interval`
runs it as compiled code and hands the result to the kernel.

## Main definitions

* `Constraint`, `Refutation`: constraints and the certificates that refute them.
* `Box.cut`, `Box.halve`: the two closed parts of a box on either side of a point of one
  coordinate, and of its midpoint.
* `Constraint.conjunct?`: a conjunct of a constraint, by its path.
* `Constraint.refutes`: the check of a certificate against a constraint and a box.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/--
A constraint on the variables of interval expressions. `fails relation e` holds at a point where
the relation does not hold of the value of `e`: `fails .negative e` is `0 ≤ e` and
`fails .nonpositive e` is `0 < e`.
-/
inductive Constraint where
  /-- The relation does not hold of the expression. -/
  | fails (relation : Relation) (e : Expr)
  /-- The quadratic form is nonpositive, or negative when `strict`. -/
  | form (strict : Bool) (f : Form)
  /-- Both constraints hold. -/
  | and (left right : Constraint)
  /-- One of the constraints holds. -/
  | or (left right : Constraint)
  deriving Repr

/--
A certificate that a constraint has no point in a box. The check of each constructor is
`Constraint.refutes`.
-/
inductive Refutation where
  /-- The constraint is an atom whose relation holds on the whole box, by `Expr.checkZero` with at
  most `depth` bisections of the widest coordinate along a branch. -/
  | atom (depth : Nat)
  /-- The constraint is a conjunction whose left part has no point in the box. -/
  | left (r : Refutation)
  /-- The constraint is a conjunction whose right part has no point in the box. -/
  | right (r : Refutation)
  /-- The constraint is a disjunction and neither part has a point in the box. -/
  | both (left right : Refutation)
  /-- The constraint has no point in either half of the box, cut at the midpoint of
  coordinate `i`. -/
  | bisect (i : Nat) (lower upper : Refutation)
  /-- The constraint has no point in either part of the box, cut at `point` along
  coordinate `i`. -/
  | cut (i : Nat) (point : ℚ) (lower upper : Refutation)
  /-- The constraint is a form atom whose matrix is positive semidefinite on the box, for a
  negative form, or positive definite with a coordinate that cannot vanish on the box, for a
  nonpositive form. -/
  | definite
  /-- The conjunct at `path` (`false` for left, `true` for right) is a nonpositive form whose
  matrix is positive definite on the box, and the constraint has no point where every
  coordinate of the form vanishes: such a point is outside the box, or `rest` refutes the
  constraint on the box with those variables at their centers. -/
  | pin (path : List Bool) (rest : Refutation)
  deriving Repr

/-- The conjunct of a constraint at a path through its conjunctions, `false` for the left part
and `true` for the right. -/
def Constraint.conjunct? : List Bool → Constraint → Option Constraint
  | [], c => some c
  | false :: path, .and a _ => Constraint.conjunct? path a
  | true :: path, .and _ b => Constraint.conjunct? path b
  | _, _ => none

/--
The two closed parts of a box below and above `point` along coordinate `i`, or `none` when the box
has no such coordinate. The parts share the point and cover the box (`Box.containsReal_cut`),
wherever the point lies.
-/
def Box.cut (box : Box) (i : Nat) (point : ℚ) : Option (Box × Box) :=
  Option.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Seq.nth? box i) none
    (fun I => some (box.set i ⟨I.lo, point⟩, box.set i ⟨point, I.hi⟩))

/--
The two closed halves of a box, cut at the midpoint of coordinate `i`: `Box.cut` at
`(I.lo + I.hi) / 2` (`Box.halve_eq`).
-/
def Box.halve (box : Box) (i : Nat) : Option (Box × Box) :=
  Option.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Seq.nth? box i) none
    (fun I => box.cut i (Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1))

/-- A box is halved by a cut at the midpoint of the coordinate. -/
theorem Box.halve_eq (box : Box) (i : Nat) :
    box.halve i = (box[i]?).bind (fun I => box.cut i ((I.lo + I.hi) / 2)) := by
  unfold Box.halve
  rw [Kernel.Seq.nth?_eq]
  cases box[i]? with
  | none => rfl
  | some I =>
    change box.cut i (Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1) = _
    rw [Kernel.Q.divPow2_eq, Kernel.Q.add_eq, pow_one]
    rfl

/--
Check a certificate against a constraint and a box.

A leaf `atom depth` asks `Expr.checkZero` for the relation of the atom on the box. `left` and
`right` choose the part of a conjunction that fails, `both` needs each part of a disjunction to
fail, and `bisect` and `cut` need the constraint to fail on both parts of the box. `definite`
and `pin` ask `Form.definiteOn` for the matrix of a form atom on the box. Any other combination
of certificate and constraint is rejected.
-/
def Constraint.refutes {α : Type*} (B : Backend α) : Refutation → Constraint → Box → Bool
  | .atom depth, .fails relation e, box => e.checkZero B relation box depth
  | .left r, .and a _, box => Constraint.refutes B r a box
  | .right r, .and _ b, box => Constraint.refutes B r b box
  | .both l r, .or a b, box => Constraint.refutes B l a box && Constraint.refutes B r b box
  | .bisect i l u, c, box =>
    match box.halve i with
    | none => false
    | some parts => Constraint.refutes B l c parts.1 && Constraint.refutes B u c parts.2
  | .cut i point l u, c, box =>
    match box.cut i point with
    | none => false
    | some parts => Constraint.refutes B l c parts.1 && Constraint.refutes B u c parts.2
  | .definite, .form true f, box => f.definiteOn B false box
  | .definite, .form false f, box => f.definiteOn B true box && f.excluded box
  | .pin path r, c, box =>
    match c.conjunct? path with
    | some (.form false f) =>
      f.definiteOn B true box && (f.excluded box || Constraint.refutes B r c (f.pinned box))
    | _ => false
  | _, _, _ => false

end FloatLib.Numerics.Interval
