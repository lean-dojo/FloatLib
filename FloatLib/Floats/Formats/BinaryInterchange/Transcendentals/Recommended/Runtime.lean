/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Floats.Formats.Posit.Logarithm.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Runtime
public import FloatLib.Numerics.Exact.Hyperbolic.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Runtime
public meta import FloatLib.Tactic.IEEENames

/-!
# The recommended functions of IEEE 754-2019 §9.2 for binary formats

IEEE 754-2019 §9.2 recommends a set of mathematical functions, correctly rounded. The names are
those of the standard as ISO/IEC 9899:2024 (C23, N3220) Annex F, Table F.2 (paragraph 20 of F.3)
lists them, and the special cases are those of F.10.1 to F.10.4 of that document. This module
provides, for every binary `FloatFormat`:

* `exp2`, `exp2m1`, `exp10`, `exp10m1`, `log2`, `log10`, `log2p1`, `log10p1`;
* `sin`, `cos`, `tan`, `sinPi`, `cosPi`, `tanPi`, `asin`, `acos`, `atan`, `asinPi`, `acosPi`,
  `atanPi`, and of two arguments `atan2`, `atan2Pi`;
* `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`;
* `powr`, `pow` and `compound`.

`pow` is here too, in every rounding direction and with flags. `exp`, `expm1`, `log`, `logp1`
are in `Transcendentals.CorrectlyRounded`, `hypot`, `rSqrt`, `rootn`, `pown` in `Algebraic`, and
`Operations.Power` has the nearest-even `Model.pow` that searches enclosures.

Each function returns an `IEEEOutcome`: the value with its exception flags and ternary value.
A finite operand in the domain is decoded to its exact rational value, and the real result is
rounded once by `ComparisonRounding.deliver`, in the rounding direction `mode` (nearest-even by
default), from an exact comparator of `Numerics.Exact` that orders the real result against
every rational: the comparators of rational powers, of the trigonometric and of the hyperbolic
functions. Nothing limits that search, so every finite operand has a result. To nearest-even
each finite result is proved correctly rounded on a conventional IEEE descriptor for finite
operands in the theorem’s domain, and in every other rounding direction the result is the
correctly rounded value of that direction, with the overflow result of IEEE 754-2019 clause 7.4
beyond the finite range (`Recommended.Proof`). The comparisons cost about
`fracWidth + expWidth` exact comparisons for one result.

To nearest-even an enclosure is tried first, for the functions of one argument, `atan2`,
`atan2Pi`, `powr` and `compound`. `Function.expr` writes the function at the operand as an
expression of
`Numerics.Interval`, `settle` evaluates an expression on a binary grid a little finer than the
format and accepts the value when both ends of the enclosure round to it, and `nearest?` tries
two grids. A value found this way is handed to `ComparisonRounding.deliver` as a hint, together
with the ordering of the value and the real result when the enclosure excludes the value, so
that the common case needs no comparison at all. An operand whose enclosures do not settle (a
result at a rounding boundary, an overflow), and an argument so large that the enclosure itself
would be huge (`Function.enclosable`, `powerEnclosable`), is rounded by the comparisons as
before.

The one-argument functions are the members of one enumeration, `Function`. `Function.rule` is
the table of their rules: what each delivers at a finite operand and at an infinity. The
functions are that table applied by `ComparisonRounding.unary`, which also gives the NaN rule.
The `Pi` functions take their argument in half-turns (`sinPi x` is `sin (π x)`) or return it in
half-turns (`asinPi x` is `asin x / π`), and decide their exact cases on the rational argument.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded

open FloatLib.Numerics
open FloatLib.Numerics.TrigonometricComparison FloatLib.Numerics.HyperbolicComparison
open ComparisonRounding (Rule Operand)

/-- π as an expression of `Numerics.Interval`: four times the arctangent of one. -/
def piExpr : Interval.Expr := .binary .mul (.const 4) (.unary .atan (.const 1))

/-- `base ^ q` as an expression: the exponential of `q` times the logarithm of `base`. -/
def powerExpr (base q : ℚ) : Interval.Expr :=
  .unary .exp (.binary .mul (.const q) (.unary .log (.const base)))

/-- The logarithm of `q` to `base` as an expression: a quotient of natural logarithms. -/
def logarithmExpr (base q : ℚ) : Interval.Expr :=
  .binary .div (.unary .log (.const q)) (.unary .log (.const base))

/--
The nearest-even rounding of the real number that `expression` denotes, when one enclosure
settles it: the expression is evaluated on the binary grid of `config`, and the value is
accepted when both ends of the enclosure round to it (`Enclosure.round?`). The hint also states
the ordering of the value and the real number when the value lies outside the enclosure.
-/
def settle (fmt : FloatFormat) (expression : Interval.Expr) (config : Interval.Backend.Config) :
    Option (ComparisonRounding.Hint fmt) :=
  match expression.eval? (Interval.Backend.binaryGrid config) fun _ => none with
  | none => none
  | some bounds =>
      let interval := Enclosure.BinaryGrid.toRationalInterval config.precision bounds
      match Enclosure.round? fmt interval with
      | none => none
      | some value =>
          some
            { value
              ternary :=
                match toRat? value with
                | none => none
                | some delivered =>
                    if delivered < interval.lo then some .lt
                    else if interval.hi < delivered then some .gt
                    else none }

/--
The two grids on which an enclosure is tried: 33 bits beyond the fraction, then twice that
precision. The degree of the series is a third of the precision, and two thirds for an
expression with a logarithm (`slow`), whose series gains about one and a half bits a term.
-/
def configs (fmt : FloatFormat) (slow : Bool) : List Interval.Backend.Config :=
  let bits := fmt.fracWidth + 33
  let degree (precision : Nat) : Nat := (if slow then 2 * precision else precision) / 3 + 16
  [{ precision := bits, degree := degree bits },
    { precision := 2 * bits, degree := degree (2 * bits) }]

/--
The largest exponent, in bits, of a number that is worth enclosing for the format: a finite
result has at most `emax + fracWidth + 2` bits before or after the binary point, and the bound
is at most `2 ^ 16` so that the enclosure of a layout with a wide exponent field stays small.
-/
def exponentLimit (fmt : FloatFormat) : ℕ :=
  min (2 ^ 16) (fmt.maxNormalExponent.toNat + fmt.fracWidth + 2)

/--
The result of the first grid of `configs` whose enclosure settles the rounding. `slow` says
that the expression has a logarithm.
-/
def nearest? (fmt : FloatFormat) (expression : Interval.Expr) (slow : Bool := false) :
    Option (ComparisonRounding.Hint fmt) :=
  (configs fmt slow).findSome? (settle fmt expression)

/--
The functions of one argument that IEEE 754-2019 §9.2 recommends and `Function.rule` specifies.
The names are those of ISO/IEC 9899:2024 Table F.2.
-/
inductive Function where
  /-- `2 ^ x`. -/
  | exp2
  /-- `2 ^ x - 1`. -/
  | exp2m1
  /-- `10 ^ x`. -/
  | exp10
  /-- `10 ^ x - 1`. -/
  | exp10m1
  /-- The logarithm to base 2. -/
  | log2
  /-- The logarithm to base 10. -/
  | log10
  /-- The logarithm to base 2 of `1 + x`. -/
  | log2p1
  /-- The logarithm to base 10 of `1 + x`. -/
  | log10p1
  /-- The sine of a radian argument. -/
  | sin
  /-- The cosine of a radian argument. -/
  | cos
  /-- The tangent of a radian argument. -/
  | tan
  /-- `sin (π x)`. -/
  | sinPi
  /-- `cos (π x)`. -/
  | cosPi
  /-- `tan (π x)`. -/
  | tanPi
  /-- The inverse sine. -/
  | asin
  /-- The inverse cosine. -/
  | acos
  /-- The inverse tangent. -/
  | atan
  /-- `asin x / π`. -/
  | asinPi
  /-- `acos x / π`. -/
  | acosPi
  /-- `atan x / π`. -/
  | atanPi
  /-- The hyperbolic sine. -/
  | sinh
  /-- The hyperbolic cosine. -/
  | cosh
  /-- The hyperbolic tangent. -/
  | tanh
  /-- The inverse hyperbolic sine. -/
  | asinh
  /-- The inverse hyperbolic cosine. -/
  | acosh
  /-- The inverse hyperbolic tangent. -/
  | atanh
  deriving Repr

namespace Function

/-- Number of cached enclosure depths of a prepared comparator, from the width of the format. -/
def levels (fmt : FloatFormat) : Nat :=
  fmt.bitWidth.log2 + 2

/-- `base ^ x` at a finite `x`, and `+0` and `+∞` at the infinities. -/
def exponential (base : ℚ) : Operand → Rule
  | .finite _ argument => .real (RationalPower.compare base argument)
  | .infinite negative => if negative then .zero false else .infinity false

/-- `base ^ x - 1`: `±0` at `±0`, `-1` at `-∞` and `+∞` at `+∞`. -/
def exponentialMinusOne (base : ℚ) : Operand → Rule
  | .finite negative argument =>
      .oddAt negative argument fun candidate => RationalPower.compare base argument (candidate + 1)
  | .infinite negative => if negative then .rational (-1) else .infinity false

/--
The logarithm to `base` of `x + offset`: a pole at `x + offset = 0`, invalid below it and at
`-∞`, `+∞` at `+∞`, and for the offset one the zero of the operand's sign at `±0`.
-/
def logarithm (base offset : ℚ) : Operand → Rule
  | .finite negative argument =>
      if offset ≠ 0 ∧ argument = 0 then .zero negative
      else if argument + offset = 0 then .pole true
      else if argument + offset < 0 then .invalid
      else .real (Posit.Model.Logarithm.compareTarget base (argument + offset))
  | .infinite negative => if negative then .invalid else .infinity false

/-- An inverse sine or cosine: invalid outside `[-1, 1]` and at the infinities. -/
def onUnitInterval (rule : Bool → ℚ → Rule) : Operand → Rule
  | .finite negative argument =>
      if -1 ≤ argument ∧ argument ≤ 1 then rule negative argument else .invalid
  | .infinite _ => .invalid

/-- The sign of `tanPi n` at a nonzero integer `n`: negative for positive odd and for negative
even `n`. -/
def tanPiZeroSign (n : ℤ) : Bool :=
  decide (0 < n) == decide (n % 2 = 1)

/--
The rules of the functions: what each delivers at a finite operand, given with its sign bit
and its exact value, and at an infinity. `levels` is the number of cached enclosure depths of
the prepared comparators. The special cases are those of ISO/IEC 9899:2024 F.10.1 to F.10.3.
-/
def rule (levels : Nat) : Function → Operand → Rule
  | .exp2 => exponential 2
  | .exp10 => exponential 10
  | .exp2m1 => exponentialMinusOne 2
  | .exp10m1 => exponentialMinusOne 10
  | .log2 => logarithm 2 0
  | .log10 => logarithm 10 0
  | .log2p1 => logarithm 2 1
  | .log10p1 => logarithm 10 1
  | .sin => fun
      | .finite negative argument => .oddAt negative argument (prepareSin argument levels).compare
      | .infinite _ => .invalid
  | .cos => fun
      | .finite _ argument => .real (prepareCos argument levels).compare
      | .infinite _ => .invalid
  | .tan => fun
      | .finite negative argument => .oddAt negative argument (prepareTan argument levels).compare
      | .infinite _ => .invalid
  | .sinPi => fun
      | .finite negative argument =>
          if argument.den = 1 then .zero negative
          else .real (prepareSinPi argument levels).compare
      | .infinite _ => .invalid
  | .cosPi => fun
      | .finite _ argument =>
          if argument.den = 2 then .zero false
          else .real (prepareCosPi argument levels).compare
      | .infinite _ => .invalid
  | .tanPi => fun
      | .finite negative argument =>
          if argument = 0 then .zero negative
          else if argument.den = 1 then .zero (tanPiZeroSign argument.num)
          else if argument.den = 2 then .pole (decide (argument.num % 4 = 3))
          else .real (prepareTanPi argument levels).compare
      | .infinite _ => .invalid
  | .asin => onUnitInterval fun negative argument =>
      .oddAt negative argument (prepareArcsin argument levels).compare
  | .acos => onUnitInterval fun _ argument => .real (prepareArccos argument levels).compare
  | .atan => fun
      | .finite negative argument =>
          .oddAt negative argument (prepareArctan argument levels).compare
      | .infinite negative => .real (compareAtan2 0 (if negative then -1 else 1))
  | .asinPi => onUnitInterval fun negative argument =>
      .oddAt negative argument (prepareArcsinPi argument levels).compare
  | .acosPi => onUnitInterval fun _ argument => .real (prepareArccosPi argument levels).compare
  | .atanPi => fun
      | .finite negative argument =>
          .oddAt negative argument (prepareArctanPi argument levels).compare
      | .infinite negative => .rational (if negative then -1 / 2 else 1 / 2)
  | .sinh => fun
      | .finite negative argument => .oddAt negative argument (compareSinh argument)
      | .infinite negative => .infinity negative
  | .cosh => fun
      | .finite _ argument => .real (compareCosh argument)
      | .infinite _ => .infinity false
  | .tanh => fun
      | .finite negative argument => .oddAt negative argument (compareTanh argument)
      | .infinite negative => .rational (if negative then -1 else 1)
  | .asinh => fun
      | .finite negative argument =>
          .oddAt negative argument (prepareArsinh argument levels).compare
      | .infinite negative => .infinity negative
  | .acosh => fun
      | .finite _ argument =>
          if 1 ≤ argument then .real (prepareArcosh argument levels).compare else .invalid
      | .infinite negative => if negative then .invalid else .infinity false
  | .atanh => fun
      | .finite negative argument =>
          if hlower : -1 < argument then
            if hupper : argument < 1 then
              .oddAt negative argument (prepareArtanh argument levels hlower hupper).compare
            else if argument = 1 then .pole false
            else .invalid
          else if argument = -1 then .pole true
          else .invalid
      | .infinite _ => .invalid

/--
An expression of `Numerics.Interval` without variables whose real value is the function at the
rational `q`, for `q` in the domain (`eval_expr`). Sums and quotients of `q` that are rational
are formed exactly and enter as constants.
-/
def expr (function : Function) (q : ℚ) : Interval.Expr :=
  match function with
  | .exp2 => powerExpr 2 q
  | .exp2m1 => .binary .sub (powerExpr 2 q) (.const 1)
  | .exp10 => powerExpr 10 q
  | .exp10m1 => .binary .sub (powerExpr 10 q) (.const 1)
  | .log2 => logarithmExpr 2 q
  | .log10 => logarithmExpr 10 q
  | .log2p1 => logarithmExpr 2 (q + 1)
  | .log10p1 => logarithmExpr 10 (q + 1)
  | .sin => .unary .sin (.const q)
  | .cos => .unary .cos (.const q)
  | .tan => .unary .tan (.const q)
  | .sinPi => .unary .sin (.binary .mul (.const q) piExpr)
  | .cosPi => .unary .cos (.binary .mul (.const q) piExpr)
  | .tanPi => .unary .tan (.binary .mul (.const q) piExpr)
  | .asin => .unary .asin (.const q)
  | .acos => .unary .acos (.const q)
  | .atan => .unary .atan (.const q)
  | .asinPi => .binary .div (.unary .asin (.const q)) piExpr
  | .acosPi => .binary .div (.unary .acos (.const q)) piExpr
  | .atanPi => .binary .div (.unary .atan (.const q)) piExpr
  | .sinh => .unary .sinh (.const q)
  | .cosh => .unary .cosh (.const q)
  | .tanh => .unary .tanh (.const q)
  | .asinh =>
      let magnitude : Interval.Expr :=
        .unary .log (.binary .add (.const |q|) (.unary .sqrt (.const (1 + q ^ 2))))
      if q < 0 then .unary .neg magnitude else magnitude
  | .acosh => .unary .log (.binary .add (.const q) (.unary .sqrt (.const (q ^ 2 - 1))))
  | .atanh => .binary .mul (.const (1 / 2)) (.unary .log (.const ((1 + q) / (1 - q))))

/--
The finite arguments at which a member of `Function` is a real number that its rule rounds:
the domain of the function, without the poles of the logarithms, of `tanPi` and of `atanh`, and
without the half-integers for `cosPi`, where the result is the exact `+0` by definition.
-/
def Domain : Function → ℚ → Prop
  | .log2, q | .log10, q => 0 < q
  | .log2p1, q | .log10p1, q => -1 < q
  | .asin, q | .acos, q | .asinPi, q | .acosPi, q => -1 ≤ q ∧ q ≤ 1
  | .cosPi, q | .tanPi, q => q.den ≠ 2
  | .acosh, q => 1 ≤ q
  | .atanh, q => -1 < q ∧ q < 1
  | _, _ => True

/-- Whether an argument is in the domain is decided by rational comparisons. -/
instance (function : Function) (q : ℚ) : Decidable (function.Domain q) := by
  cases function <;> unfold Domain <;> infer_instance

/-- Whether the function is zero at zero, where the result is the zero operand itself. -/
def vanishesAtZero : Function → Bool
  | .exp2m1 | .exp10m1 | .log2p1 | .log10p1 | .sin | .tan | .sinPi | .tanPi | .asin | .atan
  | .asinPi | .atanPi | .sinh | .tanh | .asinh | .atanh => true
  | _ => false

/-- Whether the expression of a function has a logarithm, which asks for a higher degree. -/
def hasLogarithm : Function → Bool
  | .exp2 | .exp2m1 | .exp10 | .exp10m1 | .log2 | .log10 | .log2p1 | .log10p1 | .asinh | .acosh
  | .atanh => true
  | _ => false

/--
Whether the function is enclosed at `q`. An exponential or a hyperbolic function of `q` has
about `|q|` bits before the binary point, so it is enclosed only for `|q| ≤ limit`, and the
reduction of a trigonometric argument needs about as many bits of π as the argument has, so
those are enclosed for `|q| ≤ 2 ^ 64`. Beyond these bounds the comparisons round the result.
-/
def enclosable (function : Function) (limit : ℕ) (q : ℚ) : Bool :=
  match function with
  | .exp2 | .exp2m1 | .exp10 | .exp10m1 | .sinh | .cosh | .tanh => decide (|q| ≤ limit)
  | .sin | .cos | .tan | .sinPi | .cosPi | .tanPi => decide (|q| ≤ 2 ^ 64)
  | _ => true

/-- The hint of a function at an operand: the enclosure search at a finite operand at which the
function is `enclosable` within `exponentLimit fmt`. -/
def hint (fmt : FloatFormat) (function : Function) :
    Operand → Unit → Option (ComparisonRounding.Hint fmt)
  | .finite _ q, _ =>
      if function.enclosable (exponentLimit fmt) q then
        nearest? fmt (function.expr q) function.hasLogarithm
      else none
  | .infinite _, _ => none

/--
The function applied to a value and rounded in `mode` (nearest-even by default): the value with
its flags and ternary value. A NaN gives that NaN quieted, with `invalid` when it was signaling.
To nearest-even a real result is taken from an enclosure when one settles it (`hint`).
-/
def apply {fmt : FloatFormat} (function : Function) (x : Model fmt)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome fmt :=
  ComparisonRounding.unary (function.rule (levels fmt)) x mode (function.hint fmt)

end Function

/-! ## The functions of one argument under their names -/

ieee_recommended Function.apply {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome fmt :=
  fun function => Function.apply function x mode

/-! ## Functions of two arguments -/

/--
The point `(x, y)` whose angle a pair of operands has: an infinity counts as `±1` beside a
finite operand, which then counts as zero, and two infinities as `(±1, ±1)`.
-/
def direction : Operand → Operand → ℚ × ℚ
  | .finite _ y, .finite _ x => (x, y)
  | .finite _ _, .infinite negative => (if negative then -1 else 1, 0)
  | .infinite negative, .finite _ _ => (0, if negative then -1 else 1)
  | .infinite negativeY, .infinite negativeX =>
      (if negativeX then -1 else 1, if negativeY then -1 else 1)

/--
The rule of `atan2 y x`, in radians or in half-turns: the angle of the point `direction y x`.
On the real axis the result has the sign of `y`: a zero for a positive `x` and for `+0`, and
`±π` (`±1` in half-turns) for a negative `x` and for `-0`.
-/
def angleRule (halfTurns : Bool) (levels : Nat) (y x : Operand) : Rule :=
  let point := direction y x
  if point.2 = 0 then
    if 0 < point.1 ∨ (point.1 = 0 ∧ x.negative = false) then .zero y.negative
    else if halfTurns then .rational (if y.negative then -1 else 1)
    else if y.negative then .real fun candidate => (compareAtan2 (-1) 0 (-candidate)).swap
    else .real (compareAtan2 (-1) 0)
  else if halfTurns then .real (prepareAtan2Pi point.1 point.2 levels).compare
  else .real (prepareAtan2 point.1 point.2 levels).compare

/--
The angle of the point `(x, y)` as an expression, for `y ≠ 0`: the arcsine of
`y / sqrt (x ^ 2 + y ^ 2)` in the right half-plane, and the arcsine of `-y / sqrt (x ^ 2 + y ^ 2)`
moved by π in the left one. With `halfTurns` the angle is divided by π.
-/
def angleExpr (halfTurns : Bool) (x y : ℚ) : Interval.Expr :=
  let radius : Interval.Expr := .unary .sqrt (.const (x ^ 2 + y ^ 2))
  let angle : Interval.Expr :=
    if 0 ≤ x then .unary .asin (.binary .div (.const y) radius)
    else if 0 ≤ y then .binary .add (.unary .asin (.binary .div (.const (-y)) radius)) piExpr
    else .binary .sub (.unary .asin (.binary .div (.const (-y)) radius)) piExpr
  if halfTurns then .binary .div angle piExpr else angle

/-- The hint of an angle at finite operands with a nonzero `y`: the enclosure search. -/
def angleHint (fmt : FloatFormat) (halfTurns : Bool) :
    Operand → Operand → Unit → Option (ComparisonRounding.Hint fmt)
  | .finite _ y, .finite _ x, _ =>
      if y ≠ 0 then nearest? fmt (angleExpr halfTurns x y) else none
  | _, _, _ => none

/--
IEEE 754-2019 §9.2 `atan2` (ISO/IEC 9899:2024 7.12.4.4, F.10.1.4): the angle of the
point `(x, y)` in `[-π, π]`, with one rounding in `mode` (nearest-even by default).
`atan2 (±0) x` is `±0`
for a positive `x` and for `+0`, and `±π` for a negative `x` and for `-0`; `atan2 y (±0)` is
`±π/2` with the sign of a nonzero `y`; `atan2 (±y) (-∞)` is `±π` and `atan2 (±y) (+∞)` is `±0`
for a finite `y`; `atan2 (±∞) x` is `±π/2` for a finite `x`, `±3π/4` for `-∞` and `±π/4` for
`+∞`. No operand pair is invalid, and none raises `divideByZero`.
-/
def atan2 {fmt : FloatFormat} (y x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.binary (angleRule false (Function.levels fmt)) y x mode (angleHint fmt false)

/--
IEEE 754-2019 §9.2 `atan2Pi` (ISO/IEC 9899:2024 7.12.4.11, F.10.1.11): `atan2 y x / π`, the
angle of the point `(x, y)` in half-turns, in `[-1, 1]`, with one rounding in `mode`. The
special cases are those of `atan2` divided by π: `±1`, `±1/2`, `±3/4` and `±1/4` exactly.
-/
def atan2Pi {fmt : FloatFormat} (y x : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.binary (angleRule true (Function.levels fmt)) y x mode (angleHint fmt true)

/--
Whether `base ^ exponent` is enclosed: for a positive base and a result of at most about
`limit` bits before or after the binary point. The binary logarithm of the base is below the
difference of the bit lengths of its numerator and denominator plus one in magnitude.
-/
def powerEnclosable (limit : ℕ) (base exponent : ℚ) : Bool :=
  decide (0 < base ∧
    |exponent| * (((base.num.natAbs.log2 : ℤ) - base.den.log2).natAbs + 1 : ℕ) ≤ limit)

/-- The hint of `powr` at a finite positive base and a finite exponent: the enclosure search
when the power is `powerEnclosable`. -/
def powrHint (fmt : FloatFormat) :
    Operand → Operand → Unit → Option (ComparisonRounding.Hint fmt)
  | .finite _ base, .finite _ exponent, _ =>
      if powerEnclosable (exponentLimit fmt) base exponent then
        nearest? fmt (powerExpr base exponent) true
      else none
  | _, _, _ => none

/-- The rule of `powr x y`, which is `exp (y * log x)` with the special cases of that formula. -/
def powrRule : Operand → Operand → Rule
  | .finite _ base, .finite _ exponent =>
      if base < 0 then .invalid
      else if base = 0 then
        if exponent = 0 then .invalid else if exponent < 0 then .pole false else .zero false
      else .real (RationalPower.compare base exponent)
  | .finite _ base, .infinite negative =>
      if base < 0 then .invalid
      else if base = 0 then (if negative then .infinity false else .zero false)
      else if base = 1 then .invalid
      else if decide (1 < base) == negative then .zero false
      else .infinity false
  | .infinite negativeBase, .finite _ exponent =>
      if negativeBase then .invalid
      else if exponent = 0 then .invalid
      else if exponent < 0 then .zero false
      else .infinity false
  | .infinite negativeBase, .infinite negative =>
      if negativeBase then .invalid else if negative then .zero false else .infinity false

/--
IEEE 754-2019 §9.2 `powr` (ISO/IEC 9899:2024 7.12.7.7, F.10.4.7): `x ^ y` as `exp (y * log x)`,
with one rounding in `mode` (nearest-even by default), for `x ≥ 0`. `powr x (±0)` is 1 for a
finite positive `x`, and `powr 1 y` is 1 for a finite `y`; `powr (±0) y` is `+∞` with
`divideByZero` for a finite negative `y`, `+∞` for `-∞` and `+0` for a positive `y`; a negative
`x`, `powr (±0) (±0)`, `powr (+∞) (±0)` and `powr 1 (±∞)` are invalid. The remaining infinite
operands give the limit of the formula: `+0` or `+∞` without a flag.
-/
def powr {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  ComparisonRounding.binary powrRule x y mode (powrHint fmt)

/-- Whether a rational is an odd integer. -/
def oddInteger (q : ℚ) : Bool :=
  decide (q.den = 1 ∧ q.num % 2 = 1)

/--
The rule of `pow x y` at operands that are not NaNs, with the special cases of IEEE 754-2019
§9.2.1. A positive base is located by the comparator of rational powers, and a negative base
with an integral exponent by the same comparator on its magnitude, mirrored for an odd
exponent.
-/
def powRule : Operand → Operand → Rule
  | .finite negative base, .finite _ exponent =>
      if exponent = 0 then .rational 1
      else if base = 0 then
        if exponent < 0 then .pole (negative && oddInteger exponent)
        else .zero (negative && oddInteger exponent)
      else if 0 < base then .real (RationalPower.compare base exponent)
      else if exponent.den = 1 then
        if exponent.num % 2 = 1 then
          .real fun candidate => (RationalPower.compare (-base) exponent (-candidate)).swap
        else .real (RationalPower.compare (-base) exponent)
      else .invalid
  | .finite _ base, .infinite negative =>
      if base = 0 then (if negative then .infinity false else .zero false)
      else if |base| = 1 then .rational 1
      else if decide (1 < |base|) == negative then .zero false
      else .infinity false
  | .infinite negativeBase, .finite _ exponent =>
      if exponent = 0 then .rational 1
      else if exponent < 0 then .zero (negativeBase && oddInteger exponent)
      else .infinity (negativeBase && oddInteger exponent)
  | .infinite _, .infinite negative => if negative then .zero false else .infinity false

/--
IEEE 754-2019 §9.2 `pow` (ISO/IEC 9899:2024 7.12.7.5, F.10.4.5): `x ^ y` with one rounding in
`mode` (nearest-even by default), the value with its flags and ternary value. The special
cases are those of §9.2.1: `pow x (±0)` is 1 for every `x`, a quiet NaN included, and
`pow 1 y` is 1 for every `y`, a quiet NaN included; `pow (±0) y` is `±∞` with `divideByZero`
for a negative odd integer `y`, `+∞` with `divideByZero` for every other finite negative `y`,
`±0` for a positive odd integer and `+0` for every other positive `y`; `pow (-1) (±∞)` is 1; a
finite negative `x` with a finite `y` that is not an integer is invalid; the remaining
infinite operands give the limit, with the sign of `x` when `y` is an odd integer. Every finite
operand pair has a result: nothing limits the comparisons.
-/
def pow {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome fmt :=
  if (isZero y = true ∧ isSignaling x = false) ∨ (toRat? x = some 1 ∧ isSignaling y = false) then
    (Rule.rational 1).deliver fmt mode
  else ComparisonRounding.binary powRule x y mode (powrHint fmt)

/-- The hint of `compound` at a finite operand above -1: the enclosure search when the power is
`powerEnclosable`. -/
def compoundHint (fmt : FloatFormat) (n : ℤ) :
    Operand → Unit → Option (ComparisonRounding.Hint fmt)
  | .finite _ rate, _ =>
      if powerEnclosable (exponentLimit fmt) (1 + rate) n then
        nearest? fmt (powerExpr (1 + rate) n) true
      else none
  | .infinite _, _ => none

/-- The rule of `compound x n`, which is `(1 + x) ^ n` for an integer `n`. -/
def compoundRule (n : ℤ) : Operand → Rule
  | .finite _ rate =>
      if rate < -1 then .invalid
      else if rate = -1 then
        if n = 0 then .rational 1 else if n < 0 then .pole false else .zero false
      else .real (RationalPower.compare (1 + rate) n)
  | .infinite negative =>
      if negative then .invalid
      else if n = 0 then .rational 1
      else if n < 0 then .zero false
      else .infinity false

/--
IEEE 754-2019 §9.2 `compound` (ISO/IEC 9899:2024 `compoundn`, 7.12.7.2, F.10.4.2): `(1 + x) ^ n`
for an integer `n`, from the exact `1 + x`, with one rounding in `mode`. `compound x 0` is 1 for
`x ≥ -1` and for a quiet NaN; an operand below -1 is invalid; `compound (-1) n` is `+∞` with
`divideByZero` for a negative `n` and `+0` for a positive `n`; `compound (+∞) n` is `+∞` for a
positive `n` and `+0` for a negative `n`.
-/
def compound {fmt : FloatFormat} (x : Model fmt) (n : ℤ)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome fmt :=
  if n = 0 ∧ isNaN x ∧ isSignaling x = false then (Rule.rational 1).deliver fmt mode
  else ComparisonRounding.unary (compoundRule n) x mode (compoundHint fmt n)

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded
