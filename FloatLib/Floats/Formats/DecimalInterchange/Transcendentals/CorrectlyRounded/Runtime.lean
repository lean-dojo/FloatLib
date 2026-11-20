/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Directed.Runtime
public meta import FloatLib.Tactic.IEEENames

/-!
# The recommended functions of IEEE 754-2019 §9.2 for decimal formats

The mathematical functions that IEEE 754-2019 §9.2 recommends, on a decimal `Datum` of any
`Format`, as total functions: every operand has a result, delivered as an `Outcome`, the datum
with its exception flags, in each of the five rounding directions of §4.3.

* The 26 functions of one argument that are the members of the enumeration `Function` of the
  binary formats: `exp2`, `exp10`, `log2`, `log10` with their `m1` and `p1` forms, the
  trigonometric functions in radians and in half-turns with their inverses, the hyperbolic
  functions with their inverses.
* `exp`, `expm1`, `log`, `logp1`.
* `powr`, `pow`, `compound`, `atan2`, `atan2Pi`.

`rSqrt`, `hypot`, `pown` and `rootn` are in `Arithmetic`.

A function is the rule table of the binary formats (`Function.rule`, `powrRule`, `powRule`,
`compoundRule`, `angleRule`, `Directed.expRule`, `expm1Rule`, `logRule`), which says what it
delivers at a finite operand and at an infinity and does not depend on the radix, applied by
the decimal `ComparisonRounding.unary` and `binary`. A real result is located by an exact
comparator of `Numerics.Exact` and rounded once by `ComparisonRounding.round`. The special
cases are those of ISO/IEC 9899:2024 (C23, N3220) F.10.1 to F.10.4 and, for `pow`, of
IEEE 754-2019 §9.2.1. A NaN operand gives the first NaN quieted, with `invalid` when an
operand is a signaling NaN.

The quantum exponent of a result is the least possible one, so a coefficient has all the
digits of the precision unless the result is subnormal, for an exact result too: `exp 0` is 1
with a full coefficient. A zero operand of a function with `f (±0) = ±0` is returned with its
sign and its quantum exponent, brought into the range of the format (`keepZero`), and every
other exact zero has the least quantum exponent.

Nothing limits the comparisons. To make them cheap, the comparator is asked through an
enclosure of the result where one is available (`enclose`, `ComparisonRounding.within`): an
expression of `Numerics.Interval` is evaluated on a binary grid finer than the decimal
precision, on a finer grid again when the result is small against the first, and only a
comparison that the enclosure does not decide reaches the exact comparator. A result on a
rounding boundary takes one or two exact comparisons, and an argument beyond the bounds of
`Function.enclosable` takes them at every step.

`CorrectlyRounded.Proof` proves each function correctly rounded in every direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded

open FloatLib.Numerics
open BinaryInterchange.Model.ComparisonRounding (Rule Operand)
open BinaryInterchange.Model.Transcendentals.CorrectlyRounded (Function powrRule powRule
  compoundRule angleRule powerExpr powerEnclosable angleExpr)
open BinaryInterchange.Model.Transcendentals.Directed (expRule expm1Rule logRule expExpr)

/-- Number of cached enclosure depths of a prepared comparator, from the width of the format. -/
def levels (f : Format) : Nat :=
  f.bitWidth.log2 + 2

/--
An enclosure of the real number that `expression` denotes on the binary grid with `bits` bits
after the binary point, or `none` when the evaluation has none. The degree of the series is a
third of the precision, and two thirds for an expression with a logarithm (`slow`).
-/
def encloseAt (expression : Interval.Expr) (slow : Bool) (bits : Nat) :
    Option RationalInterval :=
  let config : Interval.Backend.Config :=
    { precision := bits, degree := (if slow then 2 * bits else bits) / 3 + 16 }
  (expression.eval? (Interval.Backend.binaryGrid config) fun _ => none).map
    (Enclosure.BinaryGrid.toRationalInterval config.precision)

/--
Whether an enclosure is narrow enough for the comparisons of a rounding: it excludes zero and
its width is at most `10 ^ -(precision + 3)` of its magnitude, or it lies within a tenth of the
least quantum of zero, where every comparison of a rounding but the one with zero is decided.
-/
def sharp (f : Format) (interval : RationalInterval) : Bool :=
  let scale : ℚ := 10 ^ (f.precision + 3)
  let least : ℚ := (10 : ℚ) ^ (f.minQuantum - 1)
  decide ((0 < interval.lo ∧ (interval.hi - interval.lo) * scale ≤ interval.lo) ∨
    (interval.hi < 0 ∧ (interval.hi - interval.lo) * scale ≤ -interval.hi) ∨
    (-least < interval.lo ∧ interval.hi < least))

/--
The first enclosure that is `sharp` among the grids of `bits`, `4 * bits`, `16 * bits`, ...
bits, and the enclosure of the last grid after `steps` refinements when none is.
-/
def refine (f : Format) (expression : Interval.Expr) (slow : Bool) :
    Nat → Nat → Option RationalInterval
  | 0, bits => encloseAt expression slow bits
  | steps + 1, bits =>
      match encloseAt expression slow bits with
      | some interval =>
          if sharp f interval then some interval else refine f expression slow steps (4 * bits)
      | none => none

/--
An enclosure of the real number that `expression` denotes, or `none` when the evaluation has
none. The first grid has 40 bits beyond the bits of the decimal precision (ten bits for three
digits), which is enough for a result of ordinary magnitude. A result that is small against
that grid is enclosed on a grid with four times the bits, up to twice.
-/
def enclose (f : Format) (expression : Interval.Expr) (slow : Bool := false) :
    Option RationalInterval :=
  refine f expression slow 2 (10 * f.precision / 3 + 40)

/--
An enclosure of the reciprocal of the positive real number that `expression` denotes: the
reciprocals of the ends of an enclosure with a positive lower end.
-/
def encloseInverse (f : Format) (expression : Interval.Expr) (slow : Bool := false) :
    Option RationalInterval :=
  (enclose f expression slow).bind fun interval =>
    if 0 < interval.lo then some ⟨1 / interval.hi, 1 / interval.lo⟩ else none

/-- An enclosure moved by a rational offset. -/
def shift (offset : ℚ) (interval : RationalInterval) : RationalInterval :=
  ⟨interval.lo + offset, interval.hi + offset⟩

/--
The enclosure of `base ^ exponent` for a positive base, when the power is `powerEnclosable`
within `2 ^ 16`. The exponent is split into the nearest integer `n` and a rest of magnitude at
most a half: the grid encloses `base ^ rest`, which is of moderate size, and the ends are
multiplied by the exact rational `base ^ n`. So a power of any magnitude is enclosed with a
small relative width, where the grid would hold a small power with a large one.
-/
def enclosePower (f : Format) (base exponent : ℚ) : Option RationalInterval :=
  if powerEnclosable (2 ^ 16) base exponent then
    let whole : ℤ := round exponent
    let scale : ℚ := base ^ whole
    (enclose f (powerExpr base (exponent - whole)) true).map fun interval =>
      ⟨interval.lo * scale, interval.hi * scale⟩
  else none

/--
The enclosure of `exp q`. The magnitude of the argument is split into the nearest integer and
a rest of magnitude at most a half, whose exponentials the grid encloses cheaply, and the
exponential of a negative argument is the reciprocal of the exponential of its magnitude.
-/
def encloseExp (f : Format) (q : ℚ) : Option RationalInterval :=
  let whole : ℤ := round |q|
  let magnitude : Interval.Expr :=
    .binary .mul (.unary .exp (.const whole)) (.unary .exp (.const (|q| - whole)))
  if q < 0 then encloseInverse f magnitude else enclose f magnitude

/-- `sinh`, `cosh` or `tanh` as a rational function of the exponential `e` of the argument:
`(e - 1 / e) / 2`, `(e + 1 / e) / 2` and `(e ^ 2 - 1) / (e ^ 2 + 1)`. -/
def hyperbolicOf (function : Function) (e : ℚ) : ℚ :=
  match function with
  | .sinh => (e - 1 / e) / 2
  | .cosh => (e + 1 / e) / 2
  | _ => (e ^ 2 - 1) / (e ^ 2 + 1)

/--
The enclosure of `sinh`, `cosh` or `tanh` from the enclosure of `exp |q|`: the three rational
functions of `hyperbolicOf` increase with the exponential from one on, so they map its ends to
the ends of an enclosure. `odd` says that the function is odd, and the ends are then negated
and exchanged for a negative operand.
-/
def encloseHyperbolic (f : Format) (function : Function) (odd : Bool) (q : ℚ) :
    Option RationalInterval :=
  (encloseExp f |q|).bind fun interval =>
    if 1 ≤ interval.lo then
      let lower := hyperbolicOf function interval.lo
      let upper := hyperbolicOf function interval.hi
      some (if odd = true ∧ q < 0 then ⟨-upper, -lower⟩ else ⟨lower, upper⟩)
    else none

/--
The zero operand of a function with `f (±0) = ±0` as its result: the zero of that sign with
the operand's quantum exponent, brought into the range of the format, and no flag.
-/
def keepZero (f : Format) (mode : RoundingMode) : Datum → Outcome
  | .finite negative _ quantum => projectMagnitude f mode negative 0 quantum
  | x => { value := x }

/--
The enclosure of a member of `Function` at a finite operand at which it is `enclosable` within
`2 ^ 16`. `exp2` and `exp10` are enclosed as powers (`enclosePower`), and so are `exp2m1` and
`exp10m1` at an operand of magnitude above one, with the one subtracted from the ends. `sinh`,
`cosh` and `tanh` of an operand of magnitude above one are enclosed from the exponential
(`encloseHyperbolic`).
-/
def enclosure (f : Format) (function : Function) : Operand → Unit → Option RationalInterval
  | .finite _ q, _ =>
      if function.enclosable (2 ^ 16) q then
        match function with
        | .exp2 => enclosePower f 2 q
        | .exp10 => enclosePower f 10 q
        | .exp2m1 =>
            if |q| ≤ 1 then enclose f (Function.exp2m1.expr q) true
            else (enclosePower f 2 q).map (shift (-1))
        | .exp10m1 =>
            if |q| ≤ 1 then enclose f (Function.exp10m1.expr q) true
            else (enclosePower f 10 q).map (shift (-1))
        | .sinh =>
            if |q| ≤ 1 then enclose f (Function.sinh.expr q)
            else encloseHyperbolic f .sinh true q
        | .cosh =>
            if |q| ≤ 1 then enclose f (Function.cosh.expr q)
            else encloseHyperbolic f .cosh false q
        | .tanh =>
            if |q| ≤ 1 then enclose f (Function.tanh.expr q)
            else encloseHyperbolic f .tanh true q
        | function => enclose f (function.expr q) function.hasLogarithm
      else none
  | .infinite _, _ => none

/--
A recommended function of one argument on a decimal datum, rounded once in `mode`: the datum
with its flags. A zero operand of a function that is zero at zero is returned with its sign and
quantum exponent, a NaN gives that NaN quieted, and every other operand the outcome of the rule
of the function.
-/
def apply (f : Format) (function : Function) (mode : RoundingMode) (x : Datum) : Outcome :=
  if x.isZero = true ∧ function.vanishesAtZero = true then keepZero f mode x
  else ComparisonRounding.unary f (function.rule (levels f)) mode x (enclosure f function)

ieee_recommended apply (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  fun function => apply f function mode x

/-! ## `exp`, `expm1`, `log` and `logp1` -/

/--
The enclosure of `exp` or `expm1` at a finite operand of magnitude at most `2 ^ 16`: `encloseExp`
for `exp`, and for `expm1` at an operand of magnitude above one, with the one subtracted from
the ends.
-/
def expEnclosure (f : Format) (minusOne : Bool) : Operand → Unit → Option RationalInterval
  | .finite _ q, _ =>
      if |q| ≤ 2 ^ 16 then
        if minusOne = false then encloseExp f q
        else if |q| ≤ 1 then enclose f (expExpr true q)
        else (encloseExp f q).map (shift (-1))
      else none
  | .infinite _, _ => none

/-- The enclosure of the logarithm of `x + offset` at a finite operand inside the domain. -/
def logEnclosure (f : Format) (offset : ℚ) : Operand → Unit → Option RationalInterval
  | .finite _ q, _ =>
      if 0 < q + offset then enclose f (.unary .log (.const (q + offset))) true else none
  | .infinite _, _ => none

/--
IEEE 754-2019 §9.2 `exp` (ISO/IEC 9899:2024 7.12.6.1, F.10.3.1) on a decimal datum: `e ^ x`
with one rounding in `mode`, the datum with its flags. `exp (±0)` is 1, `exp (-∞)` is `+0` and
`exp (+∞)` is `+∞`.
-/
def exp (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  ComparisonRounding.unary f (expRule (levels f)) mode x (expEnclosure f false)

/--
IEEE 754-2019 §9.2 `expm1` (ISO/IEC 9899:2024 7.12.6.6, F.10.3.6) on a decimal datum:
`e ^ x - 1` with one rounding in `mode`, the datum with its flags. A zero operand is returned
with its sign and quantum exponent, `expm1 (-∞)` is -1 and `expm1 (+∞)` is `+∞`.
-/
def expm1 (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  if x.isZero = true then keepZero f mode x
  else ComparisonRounding.unary f (expm1Rule (levels f)) mode x (expEnclosure f true)

/--
IEEE 754-2019 §9.2 `log` (ISO/IEC 9899:2024 7.12.6.11, F.10.3.11) on a decimal datum: the
natural logarithm with one rounding in `mode`, the datum with its flags. `log (±0)` is `-∞`
with `divideByZero`, `log 1` is `+0`, a negative operand is invalid and `log (+∞)` is `+∞`.
-/
def log (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  ComparisonRounding.unary f (logRule (levels f) 0) mode x (logEnclosure f 0)

/--
IEEE 754-2019 §9.2 `logp1` (ISO/IEC 9899:2024 `log1p`, 7.12.6.14, F.10.3.14) on a decimal
datum: the natural logarithm of the exact `1 + x` with one rounding in `mode`, the datum with
its flags. A zero operand is returned with its sign and quantum exponent, `logp1 (-1)` is `-∞`
with `divideByZero`, an operand below -1 is invalid and `logp1 (+∞)` is `+∞`.
-/
def logp1 (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  if x.isZero = true then keepZero f mode x
  else ComparisonRounding.unary f (logRule (levels f) 1) mode x (logEnclosure f 1)

/-! ## Functions of two arguments -/

/--
The enclosure of a power at finite operands: `enclosePower` for a positive base, and for a
negative base with an integral exponent the enclosure of the power of its magnitude, negated
for an odd exponent.
-/
def powerEnclosure (f : Format) : Operand → Operand → Unit → Option RationalInterval
  | .finite _ base, .finite _ exponent, _ =>
      if 0 < base then enclosePower f base exponent
      else if exponent.den = 1 then
        (enclosePower f (-base) exponent).map fun interval =>
          if exponent.num % 2 = 1 then ⟨-interval.hi, -interval.lo⟩ else interval
      else none
  | _, _, _ => none

/--
IEEE 754-2019 §9.2 `powr` (ISO/IEC 9899:2024 7.12.7.7, F.10.4.7) on decimal data: `x ^ y` as
`exp (y * log x)` with one rounding in `mode`, for `x ≥ 0`, the datum with its flags. The
special cases are those of the binary `powr`.
-/
def powr (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  ComparisonRounding.binary f powrRule mode x y (powerEnclosure f)

/--
IEEE 754-2019 §9.2 `pow` (ISO/IEC 9899:2024 7.12.7.5, F.10.4.5) on decimal data: `x ^ y` with
one rounding in `mode`, the datum with its flags, with the special cases of §9.2.1.
`pow x (±0)` is 1 for every `x`, a quiet NaN included, and `pow 1 y` is 1 for every `y`, a
quiet NaN included; a finite negative `x` with a finite `y` that is not an integer is invalid.
-/
def pow (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  if (y.isZero = true ∧ x.isSignaling = false) ∨
      (x.toRat? = some 1 ∧ y.isSignaling = false) then
    ComparisonRounding.deliver f mode (fun _ => none) (Rule.rational 1)
  else ComparisonRounding.binary f powRule mode x y (powerEnclosure f)

/-- The enclosure of `compound` at a finite operand above -1: the enclosure of the power
`(1 + x) ^ n`. -/
def compoundEnclosure (f : Format) (n : ℤ) : Operand → Unit → Option RationalInterval
  | .finite _ rate, _ => enclosePower f (1 + rate) n
  | .infinite _, _ => none

/--
IEEE 754-2019 §9.2 `compound` (ISO/IEC 9899:2024 `compoundn`, 7.12.7.2, F.10.4.2) on a decimal
datum: `(1 + x) ^ n` for an integer `n`, from the exact `1 + x`, with one rounding in `mode`,
the datum with its flags. `compound x 0` is 1 for `x ≥ -1` and for a quiet NaN.
-/
def compound (f : Format) (mode : RoundingMode) (x : Datum) (n : ℤ) : Outcome :=
  if n = 0 ∧ x.isNaN = true ∧ x.isSignaling = false then
    ComparisonRounding.deliver f mode (fun _ => none) (Rule.rational 1)
  else ComparisonRounding.unary f (compoundRule n) mode x (compoundEnclosure f n)

/-- The enclosure of an angle at finite operands with a nonzero `y`. -/
def angleEnclosure (f : Format) (halfTurns : Bool) :
    Operand → Operand → Unit → Option RationalInterval
  | .finite _ y, .finite _ x, _ =>
      if y ≠ 0 then enclose f (angleExpr halfTurns x y) else none
  | _, _, _ => none

/--
IEEE 754-2019 §9.2 `atan2` (ISO/IEC 9899:2024 7.12.4.4, F.10.1.4) on decimal data: the angle
of the point `(x, y)` in `[-π, π]`, with one rounding in `mode`, the datum with its flags. The
special cases are those of the binary `atan2`.
-/
def atan2 (f : Format) (mode : RoundingMode) (y x : Datum) : Outcome :=
  ComparisonRounding.binary f (angleRule false (levels f)) mode y x (angleEnclosure f false)

/--
IEEE 754-2019 §9.2 `atan2Pi` (ISO/IEC 9899:2024 7.12.4.11, F.10.1.11) on decimal data:
`atan2 y x / π`, the angle of the point `(x, y)` in half-turns, with one rounding in `mode`,
the datum with its flags.
-/
def atan2Pi (f : Format) (mode : RoundingMode) (y x : Datum) : Outcome :=
  ComparisonRounding.binary f (angleRule true (levels f)) mode y x (angleEnclosure f true)

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded
