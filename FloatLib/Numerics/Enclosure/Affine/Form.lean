/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Exact
public import FloatLib.Numerics.Kernel.QProof

/-!
# Affine forms

An affine form `c + a₀ ε₀ + a₁ ε₁ + ⋯` is a real number that depends linearly on noise symbols
`εᵢ`, each of which usually stands for an unknown in `[-1, 1]`. The center `c` and the
coefficients `aᵢ` are exact rationals. Symbols are numbered from zero and the coefficients are a
list, entry `i` for `εᵢ`. A symbol past the end of the list has coefficient zero, so forms with
lists of different lengths share their symbols, and a sum pads the shorter list with zeros.

Sharing symbols is the point of affine arithmetic. If `x` is `1 + ε₀`, the form of `x - x` is
exactly zero, where interval arithmetic on `[0, 2]` gives `[-2, 2]`.

The enclosures are exact rational intervals, computed with the operations of `Interval.Exact`.
`rangeOn a box` encloses the values of `a` when each `εᵢ` lies in `box i`: the center plus the
products of the coefficients with their intervals. `range` is the case of the unit box, where it
is `c ± Σ i, |aᵢ|`. `mulRangeOn a b box` encloses a product of two forms. The affine part
`linearMul a b` keeps the constant and linear terms of the product, and what is left, the product
of the two deviations, is enclosed by the product of their ranges (`mulRemainderOn`).
`FormProof` gives the values of forms and proves that these enclosures contain them.

## Main definitions

* `AffineForm`: a rational center and a list of rational coefficients.
* `AffineForm.const`, `noise`, `add`, `neg`, `sub`, `scale`, `deviation`, `linearMul`: the exact
  operations on forms.
* `AffineForm.rangeOn`, `range`, `mulRangeOn`, `mulRange`: enclosures on a box of noise values
  and on the unit box.

## References

* Marcus Vinicius Alvim Andrade, João Luiz Dihl Comba and Jorge Stolfi, "Affine Arithmetic",
  Interval'94, St. Petersburg, Russia, March 1994; authors' draft at
  <https://graphics.stanford.edu/~comba/papers/aa-93-12-petersburg-paper.pdf>. Section 3 for
  affine forms and noise symbols, Section 4.3 for their product.
* Luiz Henrique de Figueiredo and Jorge Stolfi, "Affine Arithmetic: Concepts and Applications",
  *Numerical Algorithms* 37 (2004), pp. 147-158,
  <https://doi.org/10.1023/B:NUMA.0000049462.70970.b6>; preprint at
  <https://lhf.impa.br/ftp/papers/aa.ps.gz>. In the preprint, Section 3 for affine forms and their
  range, Section 3.4 for the product and its simplest error bound.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Affine

/-- An affine form `center + Σ i, coefficients[i] * εᵢ` with a rational center and rational
coefficients. The noise symbols past the end of the list have coefficient zero. -/
structure AffineForm where
  /-- The constant part. -/
  center : ℚ
  /-- The coefficients: entry `i` multiplies the noise symbol `εᵢ`. -/
  coefficients : List ℚ
  deriving DecidableEq, Repr

namespace AffineForm

/-- The entrywise sum of two coefficient lists, with the shorter one padded with zeros. -/
def addCoefficients : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => Kernel.Q.add x y :: addCoefficients xs ys

/-- The constant form `q`, with no noise. -/
def const (q : ℚ) : AffineForm :=
  ⟨q, []⟩

/-- The noise symbol `εᵢ` as a form: center zero and coefficient one at position `i`. -/
def noise (i : Nat) : AffineForm :=
  ⟨0, List.replicate i 0 ++ [1]⟩

/-- The sum of two forms. -/
def add (a b : AffineForm) : AffineForm :=
  ⟨Kernel.Q.add a.center b.center, addCoefficients a.coefficients b.coefficients⟩

/-- The negation of a form. -/
def neg (a : AffineForm) : AffineForm :=
  ⟨Kernel.Q.neg a.center, a.coefficients.map Kernel.Q.neg⟩

/-- The difference of two forms, `a + (-b)`. -/
def sub (a b : AffineForm) : AffineForm :=
  a.add b.neg

/-- The form times `q`: the center and every coefficient multiplied by `q`. -/
def scale (q : ℚ) (a : AffineForm) : AffineForm :=
  ⟨Kernel.Q.mul q a.center, a.coefficients.map (Kernel.Q.mul q)⟩

/-- The form without its center. -/
def deviation (a : AffineForm) : AffineForm :=
  ⟨0, a.coefficients⟩

/--
The affine part of the product of two forms, `a₀ b₀ + Σ i, (a₀ bᵢ + b₀ aᵢ) εᵢ`, where `a₀` and
`b₀` are the centers and `aᵢ`, `bᵢ` the coefficients. It leaves out the product of the two
deviations, which is quadratic in the noise.
-/
def linearMul (a b : AffineForm) : AffineForm :=
  ⟨Kernel.Q.mul a.center b.center,
    addCoefficients (b.coefficients.map (Kernel.Q.mul a.center))
      (a.coefficients.map (Kernel.Q.mul b.center))⟩

/-! ## Enclosures -/

/-- The unit box: every noise symbol lies in `[-1, 1]`. -/
def unitBox (_ : Nat) : Interval ℚ :=
  ⟨-1, 1⟩

/-- An enclosure of `q * x` for `x` in `I`: the exact product of the point `q` and `I`. -/
def termRange (q : ℚ) (I : Interval ℚ) : Interval ℚ :=
  Interval.Exact.mul (Interval.point q) I

/-- An enclosure of `Σ i, cs[i] * εᵢ` when each `εᵢ` lies in `box i`: the sum of the term
enclosures `termRange cs[i] (box i)`, and the point zero for no terms. -/
def termsRange (box : Nat → Interval ℚ) : List ℚ → Interval ℚ
  | [] => Interval.point 0
  | c :: cs => Interval.Exact.add (termRange c (box 0)) (termsRange (fun i => box (i + 1)) cs)

/-- An enclosure of the values of `a` when each noise symbol `εᵢ` lies in `box i`: the center
plus the enclosure of the noise terms. -/
def rangeOn (a : AffineForm) (box : Nat → Interval ℚ) : Interval ℚ :=
  Interval.Exact.add (Interval.point a.center) (termsRange box a.coefficients)

/-- An enclosure of the product of the deviations of `a` and `b` on a box, the part of the
product that `linearMul` leaves out: the product of the two deviation ranges. -/
def mulRemainderOn (a b : AffineForm) (box : Nat → Interval ℚ) : Interval ℚ :=
  Interval.Exact.mul (a.deviation.rangeOn box) (b.deviation.rangeOn box)

/-- An enclosure of the product of `a` and `b` on a box: the range of the affine part
`linearMul a b` plus the enclosure of the product of the deviations. -/
def mulRangeOn (a b : AffineForm) (box : Nat → Interval ℚ) : Interval ℚ :=
  Interval.Exact.add ((a.linearMul b).rangeOn box) (a.mulRemainderOn b box)

/-- An enclosure of the values of `a` when every noise symbol lies in `[-1, 1]`, which is
`center ± Σ i, |coefficients[i]|` (`range_lo`, `range_hi`). -/
def range (a : AffineForm) : Interval ℚ :=
  a.rangeOn unitBox

/-- An enclosure of the product of `a` and `b` when every noise symbol lies in `[-1, 1]`. -/
def mulRange (a b : AffineForm) : Interval ℚ :=
  a.mulRangeOn b unitBox

end AffineForm

end FloatLib.Numerics.Enclosure.Affine
