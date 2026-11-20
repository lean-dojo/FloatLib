/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Runtime

/-!
# `rSqrt`, `hypot`, `rootn` and `pown` in every rounding direction, with flags

`Model.rSqrt`, `hypot`, `rootn` and `pown` round to nearest-even and return a value. This
module gives the same four functions of IEEE 754-2019 §9.2 as the other recommended functions
are given in `Transcendentals.Recommended`: each returns an `IEEEOutcome`, the value with its
exception flags and ternary value, and takes the rounding direction `mode` (nearest-even by
default). The special cases are those of IEEE 754-2019 §9.2.1.

The rules are tables over `ComparisonRounding.Operand`, so they do not depend on the format:
`rSqrtRule`, `hypotRule`, `rootnRule` and `pownRule` say what each function delivers at finite
operands and at infinities. A root is located by exact comparisons of integer powers
(`Posit.Model.RootRounding.compareRoot`), and an integer power is an exact rational number.
Nothing limits the comparisons, so every operand has a result. `Algebraic.Directed.Proof`
proves the results correctly rounded in every direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Algebraic.Directed

open ComparisonRounding (Rule Operand)
open Posit.Model.RootRounding (compareRoot)

/-- The comparator of `-t` from a comparator of `t`. -/
def mirror (compare : ℚ → Ordering) (candidate : ℚ) : Ordering :=
  (compare (-candidate)).swap

/-- The rule of `1 / √x`: a pole of the operand's sign at a zero, the invalid operation at a
negative operand, `+0` at `+∞`, and the root of the reciprocal elsewhere. -/
def rSqrtRule : Operand → Rule
  | .finite negative value =>
      if value = 0 then .pole negative
      else if value < 0 then .invalid
      else .real (compareRoot value⁻¹ 2)
  | .infinite negative => if negative then .invalid else .zero false

/-- The rule of `√(x² + y²)`: `+∞` when an operand is infinite, `+0` at two zeros, and the root
of the exact sum of squares elsewhere. -/
def hypotRule : Operand → Operand → Rule
  | .finite _ x, .finite _ y =>
      if x = 0 ∧ y = 0 then .zero false else .real (compareRoot (x * x + y * y) 2)
  | _, _ => .infinity false

/--
The rule of the `degree`-th root, the reciprocal root for a negative degree. Degree zero and
a negative operand with an even degree are invalid. A zero gives a zero for a positive degree
and a pole for a negative one, an infinity gives an infinity for a positive degree and a zero
for a negative one, each negative exactly when the operand is negative and the degree is odd.
-/
def rootnRule (degree : ℤ) : Operand → Rule
  | .finite negative value =>
      if degree = 0 then .invalid
      else if value = 0 then
        if degree < 0 then .pole (negative && degree % 2 != 0)
        else .zero (negative && degree % 2 != 0)
      else if value < 0 then
        if degree % 2 = 0 then .invalid
        else .real (mirror (compareRoot (if degree < 0 then (-value)⁻¹ else -value) degree.natAbs))
      else .real (compareRoot (if degree < 0 then value⁻¹ else value) degree.natAbs)
  | .infinite negative =>
      if degree = 0 then .invalid
      else if negative ∧ degree % 2 = 0 then .invalid
      else if degree < 0 then .zero (negative && degree % 2 != 0)
      else .infinity (negative && degree % 2 != 0)

/--
The rule of the integer power `x ^ exponent`: one for the exponent zero, and the exact
rational power of a nonzero finite operand. A zero gives a zero for a positive exponent and a
pole for a negative one, an infinity gives an infinity for a positive exponent and a zero for a
negative one, each negative exactly when the operand is negative and the exponent is odd.
-/
def pownRule (exponent : ℤ) : Operand → Rule
  | .finite negative value =>
      if exponent = 0 then .rational 1
      else if value = 0 then
        if exponent < 0 then .pole (negative && exponent % 2 != 0)
        else .zero (negative && exponent % 2 != 0)
      else .rational (value ^ exponent)
  | .infinite negative =>
      if exponent = 0 then .rational 1
      else if exponent < 0 then .zero (negative && exponent % 2 != 0)
      else .infinity (negative && exponent % 2 != 0)

/--
IEEE 754-2019 §9.2 `rSqrt`: `1 / √x` with one rounding in `mode` (nearest-even by default),
the value with its flags. `rSqrt (±0)` is `±∞` with `divideByZero`, a negative operand is
invalid and `rSqrt (+∞)` is `+0`.
-/
def rSqrt {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.unary rSqrtRule x mode

/--
IEEE 754-2019 §9.2 `hypot`: `√(x² + y²)` with one rounding in `mode` (nearest-even by default),
the value with its flags. The sum of squares is exact, so no intermediate result overflows or
underflows. An infinite operand gives `+∞`, also beside a quiet NaN, and two zeros give `+0`.
-/
def hypot {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  if (isInfinite x = true ∨ isInfinite y = true) ∧ isSignaling x = false ∧
      isSignaling y = false then
    (Rule.infinity false).deliver fmt mode
  else ComparisonRounding.binary hypotRule x y mode

/--
IEEE 754-2019 §9.2 `rootn`: the `degree`-th root `x ^ (1 / degree)` with one rounding in `mode`
(nearest-even by default), the value with its flags. Degree zero is invalid, an even degree
needs a nonnegative operand, and an odd degree takes the real root of a negative operand.
`rootn (±0, degree)` is `±∞` with `divideByZero` for an odd negative degree, `+∞` with
`divideByZero` for an even negative degree, `±0` for an odd positive degree and `+0` for an
even positive degree.
-/
def rootn {fmt : FloatFormat} (x : Model fmt) (degree : ℤ)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome fmt :=
  ComparisonRounding.unary (rootnRule degree) x mode

/-- The cube root `rootn x 3`, with one rounding in `mode` and its flags. It is defined for
every finite operand, and `cbrt (±0)` is `±0`. -/
def cbrt {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  rootn x 3 mode

/--
IEEE 754-2019 §9.2 `pown`: the integer power `x ^ exponent` with one rounding in `mode`
(nearest-even by default), the value with its flags. `pown (x, 0)` is 1 for every operand that
is not a signaling NaN. `pown (±0, exponent)` is `±∞` with `divideByZero` for an odd negative
exponent, `+∞` with `divideByZero` for an even negative exponent, `±0` for an odd positive
exponent and `+0` for an even positive exponent.
-/
def pown {fmt : FloatFormat} (x : Model fmt) (exponent : ℤ)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome fmt :=
  if exponent = 0 ∧ isSignaling x = false then (Rule.rational 1).deliver fmt mode
  else ComparisonRounding.unary (pownRule exponent) x mode

end FloatLib.Floats.Formats.BinaryInterchange.Model.Algebraic.Directed
