/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Roundoff.Extension
public import FloatLib.Tactic.ComplexRule

/-!
# `roundoff` rules for complex programs

`roundoff` analyzes scalar operations. A program on `ExecComplex fmt` reaches them through the
components of its complex operations, and the rules here say what those components are: each
states the real value of a component of `x + y`, `x - y`, `x * y`, `mulFma x y`, `x / y`, `-z`,
`conj z`, `normSq z` or `magnitude z` as the real value of the scalar expression that computes
it. They are observation equalities, so they add no error of their own, and the scalar rules of
`roundoff` then bound each rounding.

With this module and the `FloatLib.Tactic.Roundoff` import, `roundoff`, `roundoff theorem` and
`roundoff mixed theorem` prove a bound for a component of any complex program, for every IEEE
descriptor, with the finiteness of the intermediate values as its premise. The bound of a
component is absolute: it adds the half-ulp of every rounding, propagated through the exact
operations, so an underflow is counted where it happens. The branch of a division is kept as
the program chooses it, by the comparison of the divisor's components.

The normwise bounds of the whole operations (`√5 u` for the product, `2u` with fused
multiply-adds, `√2 γ₇` for the division) are theorems about a complex number and are not
`roundoff` rules: `Complex.ErrorBounds` states them, and they apply to the result of one
operation whatever computed its operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecComplex

variable {fmt : FloatFormat}

complex_rule toReal_neg (z : ExecComplex fmt) : -z := Model.neg z.re, Model.neg z.im

complex_rule toReal_conj (z : ExecComplex fmt) : conj z := z.re, Model.neg z.im

complex_rule toReal_add (x y : ExecComplex fmt) : x + y :=
  Model.add x.re y.re, Model.add x.im y.im

complex_rule toReal_sub (x y : ExecComplex fmt) : x - y :=
  Model.sub x.re y.re, Model.sub x.im y.im

complex_rule toReal_mul (x y : ExecComplex fmt) : x * y :=
  Model.sub (Model.mul x.re y.re) (Model.mul x.im y.im),
  Model.add (Model.mul x.re y.im) (Model.mul x.im y.re)

complex_rule toReal_mulFma (x y : ExecComplex fmt) : mulFma x y :=
  Model.fma x.re y.re (Model.neg (Model.mul x.im y.im)),
  Model.fma x.re y.im (Model.mul x.im y.re)

complex_rule toReal_swap (z : ExecComplex fmt) : Internal.swap z := z.im, z.re

complex_rule toReal_divRealDominant (x y : ExecComplex fmt) : Internal.divRealDominant x y :=
  Model.div (Model.add x.re (Model.mul x.im (Model.div y.im y.re)))
    (Model.add y.re (Model.mul y.im (Model.div y.im y.re))),
  Model.div (Model.sub x.im (Model.mul x.re (Model.div y.im y.re)))
    (Model.add y.re (Model.mul y.im (Model.div y.im y.re)))

complex_rule toReal_magnitudeRatios (z : ExecComplex fmt) : Internal.magnitudeRatios z :=
  Model.div z.re (Internal.magnitudeScale z), Model.div z.im (Internal.magnitudeScale z)

/-- The real component of a quotient is that of the branch the divisor selects: the ratio
formula on the exchanged components when the imaginary component of the divisor is larger. -/
@[roundoff_rule] theorem toReal_div_re (x y : ExecComplex fmt) :
    Model.toReal (x / y).re =
      Model.toReal (if Internal.imagDominant y then
        (Internal.divRealDominant (Internal.swap x) (Internal.swap y)).re
      else (Internal.divRealDominant x y).re) := by
  change Model.toReal (div x y).re = _
  unfold div
  split <;> rfl

/-- The imaginary component of a quotient is that of the branch the divisor selects, negated
after the exchange of the components. -/
@[roundoff_rule] theorem toReal_div_im (x y : ExecComplex fmt) :
    Model.toReal (x / y).im =
      Model.toReal (if Internal.imagDominant y then
        Model.neg (Internal.divRealDominant (Internal.swap x) (Internal.swap y)).im
      else (Internal.divRealDominant x y).im) := by
  change Model.toReal (div x y).im = _
  unfold div
  split <;> rfl

/-- The squared magnitude is two rounded squares and their rounded sum. -/
@[roundoff_rule] theorem toReal_normSq (z : ExecComplex fmt) :
    Model.toReal (normSq z) =
      Model.toReal (Model.add (Model.mul z.re z.re) (Model.mul z.im z.im)) := rfl

/-- The scale of a magnitude is the absolute value of the component that the comparison
selects. -/
@[roundoff_rule] theorem toReal_magnitudeScale (z : ExecComplex fmt) :
    Model.toReal (Internal.magnitudeScale z) =
      Model.toReal (if Internal.imagDominant z then Model.abs z.im else Model.abs z.re) := rfl

/-- The magnitude of a finite value with a nonzero scale is the scale times the rounded square
root of the squared magnitude of the scaled components. -/
@[roundoff_rule] theorem toReal_magnitude (z : ExecComplex fmt) (hz : isFinite z = true)
    (hscale : Model.isZero (Internal.magnitudeScale z) = false) :
    Model.toReal (magnitude z) =
      Model.toReal (Model.mul (Internal.magnitudeScale z)
        (Model.sqrt (normSq (Internal.magnitudeRatios z)))) := by
  simp [magnitude, hz, hscale]

end FloatLib.Floats.Formats.BinaryInterchange.ExecComplex
