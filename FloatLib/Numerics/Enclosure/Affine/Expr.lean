/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.Model
public import FloatLib.Numerics.Enclosure.Expression.Check

/-!
# Affine ranges of interval expressions

Interval evaluation treats the occurrences of a variable as independent, so `x * (1 - x)` on
`[0, 1]` gets the range `[0, 1]`, four times as wide as the true range `[0, 1 / 4]`. Affine
arithmetic keeps the correlation: variable `i` with interval `[lo, hi]` becomes the affine form
`(lo + hi) / 2 + (hi - lo) / 2 * εᵢ`, with a noise symbol `εᵢ` of its own that ranges over
`[-1, 1]`, and the operations act on these forms. On `x * (1 - x)` this gives the true range.

`Expr.affineModel? e box` compiles the polynomial fragment of an expression into an
`AffineModel` over a box: rational constants, variables, negation, natural powers, sums,
differences, products and fused multiply-adds. Any other operation, a registered call, or a
variable that the box does not bound makes it return `none`. Sums and negations keep the affine
part exact, while products and powers move their nonlinear terms into the interval remainder of
the model, where correlations are lost. `Expr.affineRange? e box` is the range of that model.

`ExprProof` proves that the range contains the value of the expression at every real point of the
box (`Expr.containsReal_affineRange?`).

## Main definitions

* `variableForm i I`: the affine form of variable `i` on the interval `I`.
* `Expr.affineModel?`: the affine model of an expression on a box.
* `Expr.affineRange?`: its range.

## References

* Marcus Vinicius Alvim Andrade, João Luiz Dihl Comba and Jorge Stolfi, "Affine Arithmetic",
  Interval'94, St. Petersburg, Russia, March 1994; authors' draft at
  <https://graphics.stanford.edu/~comba/papers/aa-93-12-petersburg-paper.pdf>. Section 3.1 for
  the affine form of an input interval, Section 4.1 for the exact affine operations.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Affine

open FloatLib.Numerics.Interval (Box Expr)

/-- The affine form of variable `i` on the interval `I`: the center `(I.lo + I.hi) / 2` plus the
radius `(I.hi - I.lo) / 2` times the noise symbol `i`. -/
def variableForm (i : Nat) (I : Interval ℚ) : AffineForm :=
  (AffineForm.const (Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1)).add
    (AffineForm.scale (Kernel.Q.divPow2 (Kernel.Q.sub I.hi I.lo) 1) (AffineForm.noise i))

/--
The affine model of an expression on a box, or `none` outside the polynomial fragment.

A constant is the constant model, and variable `i` is `variableForm i I` with no remainder, where
`I` is coordinate `i` of the box. Negation, natural powers, sums, differences and products are the
operations of `AffineModel`, and the fused multiply-add `x * y + z` is a product and a sum. Every
other operation, every registered call and every variable that the box does not bound give `none`.
-/
def Expr.affineModel? (e : Expr) (box : Box) : Option AffineModel :=
  match e with
  | .const q => some (AffineModel.const q)
  | .var i => (Kernel.Seq.nth? box i).map fun I => AffineModel.ofAffine (variableForm i I)
  | .unary .neg a => (Expr.affineModel? a box).map AffineModel.neg
  | .unary (.pow n) a => (Expr.affineModel? a box).map fun A => A.pow n
  | .binary .add a b => do
    let A ← Expr.affineModel? a box
    let B ← Expr.affineModel? b box
    pure (A.add B)
  | .binary .sub a b => do
    let A ← Expr.affineModel? a box
    let B ← Expr.affineModel? b box
    pure (A.sub B)
  | .binary .mul a b => do
    let A ← Expr.affineModel? a box
    let B ← Expr.affineModel? b box
    pure (A.mul B)
  | .ternary .fma a b c => do
    let A ← Expr.affineModel? a box
    let B ← Expr.affineModel? b box
    let C ← Expr.affineModel? c box
    pure ((A.mul B).add C)
  | _ => none
termination_by structural e

/-- The range of the affine model of an expression on a box (`Expr.affineModel?`), or `none`
outside the polynomial fragment. -/
def Expr.affineRange? (e : Expr) (box : Box) : Option (Interval ℚ) :=
  (Expr.affineModel? e box).map AffineModel.range

end FloatLib.Numerics.Enclosure.Affine
