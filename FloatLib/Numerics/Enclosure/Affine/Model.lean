/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.Form
public import Mathlib.Data.Nat.BinaryRec

/-!
# Affine models

An affine model is an affine form together with an interval for the remainder: it represents a
real `x` at a noise assignment `ε` when `x` minus the value of the form at `ε` lies in the
remainder. Sums and negations act on the two parts separately. A product keeps the constant and
linear terms of the product of the forms (`AffineForm.linearMul`) and adds everything else to the
remainder by interval arithmetic: the product of the two deviations, each form times the other
remainder, and the product of the remainders. Powers use binary exponentiation. `range` is the
range of the form on the unit box plus the remainder. `ModelProof` proves that sums and negations
preserve what a model represents, that products and powers do when every noise symbol lies in
`[-1, 1]`, and that `range` then contains every represented value.

The product of the deviations, `(Σ i, aᵢ εᵢ) * (Σ j, bⱼ εⱼ)`, is enclosed pair by pair
(`quadraticRange`): `aᵢ bⱼ εᵢ εⱼ` with `εᵢ εⱼ` in `[0, 1]` when `i = j` and in `[-1, 1]`
otherwise. The recursion takes the term of the first symbol of both forms, the terms of the first
symbol of one form with the other symbols of the other, and then the remaining symbols of both.

## Main definitions

* `AffineModel`: an affine form and a rational remainder interval.
* `AffineModel.const`, `ofAffine`, `add`, `neg`, `sub`, `mul`, `pow`: the operations.
* `AffineModel.range`: the enclosure of every represented value on the unit box.

## Implementation notes

The papers cited in `Form` replace the nonlinear part of a product by a new noise symbol whose
coefficient bounds it, at simplest `(Σ i, |aᵢ|) * (Σ i, |bᵢ|)`, and add rounding errors to such
coefficients. We keep an interval remainder instead, so the noise symbols stay fixed and a model
is a first-order Taylor model in the noise symbols. On the unit box `AffineForm.mulRemainderOn`
is the symmetric interval with that simplest radius, and the pairwise bound `quadraticRange` lies
inside it. The arithmetic is exact, so there are no rounding errors to add.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Affine

/-- An affine form together with an interval for the terms it leaves out. -/
structure AffineModel where
  /-- The constant and linear part, which keeps the dependence on the noise symbols. -/
  affine : AffineForm
  /-- An enclosure of the terms that `affine` leaves out. -/
  remainder : Interval ℚ
  deriving DecidableEq, Repr

namespace AffineModel

/-- The constant model `q`, with remainder zero. -/
def const (q : ℚ) : AffineModel :=
  ⟨.const q, Interval.point 0⟩

/-- An affine form as a model with remainder zero. -/
def ofAffine (a : AffineForm) : AffineModel :=
  ⟨a, Interval.point 0⟩

/-- The sum of two models: the sum of the forms and the sum of the remainders. -/
def add (a b : AffineModel) : AffineModel :=
  ⟨a.affine.add b.affine, Interval.Exact.add a.remainder b.remainder⟩

/-- The negation of a model: the negation of the form and of the remainder. -/
def neg (a : AffineModel) : AffineModel :=
  ⟨a.affine.neg, Interval.Exact.neg a.remainder⟩

/-- The difference of two models, `a + (-b)`. -/
def sub (a b : AffineModel) : AffineModel :=
  a.add b.neg

/-- The interval `[0, 1]`, which contains the square of a noise value in `[-1, 1]`. -/
def unitSquare : Interval ℚ :=
  ⟨0, 1⟩

/--
An enclosure of `(Σ i, xs[i] * εᵢ) * (Σ j, ys[j] * εⱼ)` when every noise symbol lies in
`[-1, 1]`: the sum over all ordered pairs `(i, j)` of `termRange (xs[i] * ys[j])` of `[0, 1]`
when `i = j` and of `[-1, 1]` otherwise. The recursion encloses the pair of first symbols, the
first symbol of `xs` with the other symbols of `ys`, the first symbol of `ys` with the other
symbols of `xs`, and then the pairs of the remaining symbols.
-/
def quadraticRange : List ℚ → List ℚ → Interval ℚ
  | [], _ => Interval.point 0
  | _ :: _, [] => Interval.point 0
  | x :: xs, y :: ys =>
    Interval.Exact.add
      (Interval.Exact.add
        (Interval.Exact.add (AffineForm.termRange (Kernel.Q.mul x y) unitSquare)
          (AffineForm.termsRange AffineForm.unitBox (ys.map (Kernel.Q.mul x))))
        (AffineForm.termsRange AffineForm.unitBox (xs.map (Kernel.Q.mul y))))
      (quadraticRange xs ys)

/--
The product of two models. For represented values `x = A + r` and `y = B + s`, with `A` and `B`
the values of the forms, the form of the product is the affine part of `A * B`
(`AffineForm.linearMul`). Its remainder encloses, in this order, the product of the two
deviations (`quadraticRange`), `A * s`, `B * r` and `r * s`.
-/
def mul (a b : AffineModel) : AffineModel :=
  ⟨a.affine.linearMul b.affine,
    Interval.Exact.add
      (Interval.Exact.add
        (Interval.Exact.add (quadraticRange a.affine.coefficients b.affine.coefficients)
          (Interval.Exact.mul a.affine.range b.remainder))
        (Interval.Exact.mul b.affine.range a.remainder))
      (Interval.Exact.mul a.remainder b.remainder)⟩

/--
One step of binary exponentiation for `pow`. From `accumulator`, the model of `a ^ n`, it returns
the model of `a ^ (2 * n + 1)` when `odd` is `true` and of `a ^ (2 * n)` otherwise. When `odd` is
`false` and `n = 0` it returns `accumulator` unchanged, the base case that `Nat.binaryRec_eq`
needs.
-/
def powStep (a : AffineModel) (odd : Bool) (n : Nat) (accumulator : AffineModel) :
    AffineModel :=
  if odd then
    (accumulator.mul accumulator).mul a
  else if n = 0 then
    accumulator
  else
    accumulator.mul accumulator

/-- A natural power of a model by binary exponentiation, starting from the constant model one. -/
def pow (a : AffineModel) (n : Nat) : AffineModel :=
  Nat.binaryRec (const 1) (powStep a) n

/-- An enclosure of every value the model represents on the unit box: the range of the form
plus the remainder. -/
def range (m : AffineModel) : Interval ℚ :=
  Interval.Exact.add m.affine.range m.remainder

end AffineModel

end FloatLib.Numerics.Enclosure.Affine
