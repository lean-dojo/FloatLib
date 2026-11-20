/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Check

/-!
# Quadratic forms with interval coefficients

A `Form` is a quadratic form `Σ M k k * d k ^ 2 + 2 * Σ_{k < l} M k l * d k * d l` in coordinates
`d k` that are powers of variables shifted by rationals, or the constant one, with a symmetric
matrix `M` whose entries are interval expressions. It is the certificate for a constraint whose
margin vanishes at a point: interval evaluation of `g` never separates `g` from zero near a point
where `g` is zero, but when `g` is such a form and `M` is positive definite on a box around the
point, `g` is positive on the box except at the point itself.

`Form.definiteOn` checks positive definiteness on a box, in any dimension: it encloses the entries
on the box and eliminates one coordinate at a time. With pivot `a` and border `t`, the form is
`a * (d 0 + (Σ t j * d j) / a) ^ 2` plus the form of the Schur complement `M j l - t j * t l / a`,
so it is enough that the pivot enclosure is positive and that the complement, computed with the
interval operations of the backend, passes the same check. For a form that need only be
nonnegative, a pivot that is merely nonnegative is allowed when its border is zero.
`FormProof` proves that an accepted form is nonnegative on the box, and with the strict check
that it vanishes only where every coordinate does
(`Form.nonneg_of_definiteOn`, `Form.vanishes_of_definiteOn`).

## Main definitions

* `Shift`, `Form`: the coordinates and the form.
* `Form.eliminate`, `Form.reduce`, `Form.definite`: the Schur complement and the check of an
  interval matrix.
* `Form.definiteOn`: the check of a form on a box.
* `Form.excluded`, `Form.pinned`: whether some coordinate cannot vanish on a box, and the part of
  the box where every coordinate vanishes.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- A coordinate of a quadratic form: a power of variable `i` minus a rational, or the constant
one. -/
inductive Shift where
  /-- The variable `i` minus `center`, to the power `extra + 1`. A form whose lowest term in a
  variable has degree four has its square as a coordinate, with `extra = 1`. -/
  | var (i : Nat) (center : ℚ) (extra : Nat)
  /-- The constant one, the coordinate of the linear and constant terms. -/
  | one
  deriving Repr

/--
A quadratic form: its coordinates, and the upper triangle of its symmetric matrix by rows, row
`k` holding the entries `M k k`, `M k (k + 1)`, … as expressions.
-/
structure Form where
  /-- The coordinates. -/
  coordinates : List Shift
  /-- The upper triangle of the symmetric matrix. -/
  rows : List (List Expr)
  deriving Repr

namespace Form

variable {α : Type*} (B : Backend α)

/-- `x - w * y` entry by entry, or `none` when the lengths differ or an operation fails. -/
def eliminate (w : Interval α) : List (Interval α) → List (Interval α) →
    Option (List (Interval α))
  | [], [] => some []
  | x :: xs, y :: ys =>
    match B.binary? .mul w y with
    | none => none
    | some p =>
      match B.binary? .sub x p with
      | none => none
      | some d =>
        match eliminate w xs ys with
        | none => none
        | some rest => some (d :: rest)
  | _, _ => none

/--
The Schur complement of the pivot `a` with border `border` in the remaining rows: row `j` loses
`border j / a` times the part of the border from `j` on. It is `none` when the shapes do not fit
or an operation fails, as a division by a pivot enclosure that contains zero does.
-/
def reduce (a : Interval α) : List (Interval α) → List (List (Interval α)) →
    Option (List (List (Interval α)))
  | [], [] => some []
  | t :: border, row :: rows =>
    match B.binary? .div t a with
    | none => none
    | some w =>
      match eliminate B w row (t :: border) with
      | none => none
      | some first =>
        match reduce a border rows with
        | none => none
        | some rest => some (first :: rest)
  | _, _ => none

/-- Whether an enclosure is the point zero (`Backend.isZero`). -/
def isZero (I : Interval α) : Bool := B.isZero I

/--
Whether every symmetric matrix in an interval matrix, given by the rows of its upper triangle, is
positive definite (`strict`) or positive semidefinite. `fuel` bounds the eliminations and should
be the number of rows. A pivot enclosure must be positive; without `strict`, a nonnegative pivot
with a zero border is passed over.
-/
def definite (strict : Bool) : Nat → List (List (Interval α)) → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] :: _ => false
  | fuel + 1, (a :: border) :: rows =>
    match B.decode a.lo with
    | none => false
    | some lo =>
      if Kernel.Q.lt 0 lo then
        match reduce B a border rows with
        | none => false
        | some reduced => definite strict fuel reduced
      else
        !strict && Kernel.Q.le 0 lo && border.all (isZero B) && definite strict fuel rows

/-- The enclosures of the entries of one row on enclosed variables. -/
def encloseRow (intervals : List (Interval α)) : List Expr → Option (List (Interval α))
  | [] => some []
  | e :: es =>
    match e.evalZero? B (fun i => Kernel.Seq.nth? intervals i) with
    | none => none
    | some I =>
      match encloseRow intervals es with
      | none => none
      | some rest => some (I :: rest)

/-- The enclosures of the entries of the rows on enclosed variables. -/
def encloseRows (intervals : List (Interval α)) : List (List Expr) →
    Option (List (List (Interval α)))
  | [] => some []
  | row :: rows =>
    match encloseRow B intervals row with
    | none => none
    | some first =>
      match encloseRows intervals rows with
      | none => none
      | some rest => some (first :: rest)

/--
Whether the matrix of a form is positive definite (`strict`) or semidefinite at every point of a
box: the entries are enclosed on the box and the interval matrix is checked by `definite`. A form
whose rows and coordinates differ in number is rejected.
-/
def definiteOn (strict : Bool) (f : Form) (box : Box) : Bool :=
  match box.enclose? B with
  | none => false
  | some intervals =>
    match encloseRows B intervals f.rows with
    | none => false
    | some rows => f.coordinates.length == rows.length && definite B strict rows.length rows

end Form

/-- Whether a coordinate cannot vanish on a box: the constant one, or a variable whose center
lies outside its interval. A variable without interval may vanish. -/
def Shift.excluded (box : Box) : Shift → Bool
  | .one => true
  | .var i center _ =>
    match Kernel.Seq.nth? box i with
    | none => false
    | some I => Kernel.Q.lt center I.lo || Kernel.Q.lt I.hi center

/-- The box with the variable of a coordinate set to its center. -/
def Shift.pin (box : Box) : Shift → Box
  | .one => box
  | .var i center _ => box.set i ⟨center, center⟩

/-- Whether some coordinate of a form cannot vanish on a box. -/
def Form.excluded (f : Form) (box : Box) : Bool :=
  f.coordinates.any (Shift.excluded box)

/-- The part of a box where every coordinate of a form vanishes: each variable at its center. -/
def Form.pinned (f : Form) (box : Box) : Box :=
  f.coordinates.foldl Shift.pin box

end FloatLib.Numerics.Interval
