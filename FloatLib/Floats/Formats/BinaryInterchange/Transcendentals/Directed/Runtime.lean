/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Runtime
public import FloatLib.Numerics.Exact.Elementary.Runtime

/-!
# `exp`, `expm1`, `log` and `logp1` in every rounding direction, with flags

`Transcendentals.CorrectlyRounded` has `exp`, `expm1`, `log` and `logp1` to nearest-even, as
values. This module gives the same four functions of IEEE 754-2019 §9.2 as the other
recommended functions are given in `Transcendentals.Recommended`: each returns an
`IEEEOutcome`, the value with its exception flags and ternary value, and takes the rounding
direction `mode` (nearest-even by default). The special cases are those of ISO/IEC 9899:2024
(C23, N3220) F.10.3.1, F.10.3.9, F.10.3.11 and F.10.3.14.

The rules are tables over `ComparisonRounding.Operand`, so they do not depend on the radix:
`expRule`, `expm1Rule` and `logRule` say what each function delivers at a finite operand and at
an infinity, and locate a real result by the exact comparators
`ElementaryComparison.prepareExp` and `prepareLog`. The decimal formats apply the same tables.
For a binary format the functions are these tables applied by `ComparisonRounding.unary`, and
to nearest-even an enclosure is tried first (`expHint`, `logHint`). Nothing limits the
comparisons, so every operand has a result. `Directed.Proof` proves the results correctly
rounded in every direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Directed

open FloatLib.Numerics
open ComparisonRounding (Rule Operand)
open CorrectlyRounded (nearest? exponentLimit)

/-- The rule of `exp x`: the exponential at a finite operand, `+0` at `-∞` and `+∞` at `+∞`. -/
def expRule (levels : Nat) : Operand → Rule
  | .finite _ argument => .real (ElementaryComparison.prepareExp argument levels).compare
  | .infinite negative => if negative then .zero false else .infinity false

/-- The rule of `exp x - 1`: `±0` at `±0`, -1 at `-∞` and `+∞` at `+∞`. -/
def expm1Rule (levels : Nat) : Operand → Rule
  | .finite negative argument =>
      .oddAt negative argument fun candidate =>
        (ElementaryComparison.prepareExp argument levels).compare (candidate + 1)
  | .infinite negative => if negative then .rational (-1) else .infinity false

/--
The rule of the natural logarithm of `x + offset`: a pole at `x + offset = 0`, invalid below it
and at `-∞`, `+∞` at `+∞`, and for a nonzero offset the zero of the operand's sign at `±0`.
-/
def logRule (levels : Nat) (offset : ℚ) : Operand → Rule
  | .finite negative argument =>
      if offset ≠ 0 ∧ argument = 0 then .zero negative
      else if hpositive : 0 < argument + offset then
        .real (ElementaryComparison.prepareLog (argument + offset) levels hpositive).compare
      else if argument + offset = 0 then .pole true
      else .invalid
  | .infinite negative => if negative then .invalid else .infinity false

/-- `exp q`, or `exp q - 1` with `minusOne`, as an expression of `Numerics.Interval`. -/
def expExpr (minusOne : Bool) (q : ℚ) : Interval.Expr :=
  if minusOne then .binary .sub (.unary .exp (.const q)) (.const 1) else .unary .exp (.const q)

/-- The hint of `exp` or `expm1` at a finite operand of magnitude at most `exponentLimit fmt`:
the enclosure search. -/
def expHint (fmt : FloatFormat) (minusOne : Bool) :
    Operand → Unit → Option (ComparisonRounding.Hint fmt)
  | .finite _ q, _ =>
      if |q| ≤ exponentLimit fmt then nearest? fmt (expExpr minusOne q) else none
  | .infinite _, _ => none

/-- The hint of the logarithm of `x + offset` at a finite operand inside the domain: the
enclosure search. -/
def logHint (fmt : FloatFormat) (offset : ℚ) :
    Operand → Unit → Option (ComparisonRounding.Hint fmt)
  | .finite _ q, _ =>
      if 0 < q + offset then nearest? fmt (.unary .log (.const (q + offset))) true else none
  | .infinite _, _ => none

/--
IEEE 754-2019 §9.2 `exp` (ISO/IEC 9899:2024 7.12.6.1, F.10.3.1): `e ^ x` with one rounding in
`mode` (nearest-even by default), the value with its flags. `exp (±0)` is 1, `exp (-∞)` is `+0`
and `exp (+∞)` is `+∞`.
-/
def exp {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.unary (expRule (CorrectlyRounded.Function.levels fmt)) x mode
    (expHint fmt false)

/--
IEEE 754-2019 §9.2 `expm1` (ISO/IEC 9899:2024 7.12.6.6, F.10.3.6): `e ^ x - 1` with one
rounding in `mode`, the value with its flags. `expm1 (±0)` is `±0`, `expm1 (-∞)` is -1 and
`expm1 (+∞)` is `+∞`.
-/
def expm1 {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.unary (expm1Rule (CorrectlyRounded.Function.levels fmt)) x mode
    (expHint fmt true)

/--
IEEE 754-2019 §9.2 `log` (ISO/IEC 9899:2024 7.12.6.11, F.10.3.11): the natural logarithm with
one rounding in `mode`, the value with its flags. `log (±0)` is `-∞` with `divideByZero`,
`log 1` is `+0`, a negative operand is invalid and `log (+∞)` is `+∞`.
-/
def log {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.unary (logRule (CorrectlyRounded.Function.levels fmt) 0) x mode
    (logHint fmt 0)

/--
IEEE 754-2019 §9.2 `logp1` (ISO/IEC 9899:2024 `log1p`, 7.12.6.14, F.10.3.14): the natural
logarithm of the exact `1 + x` with one rounding in `mode`, the value with its flags.
`logp1 (±0)` is `±0`, `logp1 (-1)` is `-∞` with `divideByZero`, an operand below -1 is invalid
and `logp1 (+∞)` is `+∞`.
-/
def logp1 {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.unary (logRule (CorrectlyRounded.Function.levels fmt) 1) x mode
    (logHint fmt 1)

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Directed
