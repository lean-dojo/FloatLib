/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
public import FloatLib.Numerics.Enclosure.Expression.Basic
public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic
public import FloatLib.Numerics.Enclosure.Interval.InverseTrig
public import FloatLib.Numerics.Enclosure.Interval.SharpTrig
public import FloatLib.Numerics.Enclosure.Interval.Total

/-!
# One table of elementary enclosures, chosen by settings

`Backend.elementaryWith s` encloses the elementary functions of `UnaryOp` on rational intervals,
and its settings `s` say which enclosure each function gets and how accurate it is. They hold a
degree for each family of functions, a precision for square roots, and three switches:

- `sharpTrig := some bits` gives sine and cosine the enclosures `sharpSinBounds` and
  `sharpCosBounds`: the midpoint bounds on a grid of `2 ^ (-bits)`, narrowed by the values at the
  two ends of the interval where the function is monotone on it. On a coarse grid the result can
  be wider than the unrounded midpoint bound. Tangent tries the quotient of those two enclosures,
  then `tanBounds?` if the rounded cosine enclosure contains zero.
- `total := true` follows Mathlib's total functions outside the usual domains with `Total.sqrt`,
  `Total.log?`, `Total.asin` and `Total.acos`: `√x = 0` for `x ≤ 0`, `log x = log |x|` with
  `log 0 = 0`, and `arcsin` and `arccos` are constant beyond `[-1, 1]`. The logarithm still
  refuses an interval that contains zero and another point, since it's unbounded there.
- `gridExpLog := some bits` encloses the exponential and the logarithm at the two ends of the
  interval with the binary-grid kernels `Enclosure.BinaryGrid.exp` and `Enclosure.BinaryGrid.log`,
  on the grid of `bits` fractional bits (`gridExpBounds`, `gridLogBounds?`). That logarithm needs a
  positive interval, whatever `total` says.

`ElementarySettings.legacy config` turns the three switches off and takes every degree and the
precision from `config`. At those settings the table is `Backend.elementaryBounds? config`, the
table of `Backend.ofRounding` and `Backend.binaryGrid` and so of the `interval` tactic
(`Backend.elementaryWith_legacy`). `ElementaryTableProof` proves that equation, and that every
enclosure of the table contains the real value at every setting.

## Main definitions

* `ElementarySettings`: the degrees, the square-root precision and the three switches.
* `ElementarySettings.legacy config`: the settings of the `interval` tactic.
* `Backend.elementaryWith s`: the table at the settings `s`.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/--
Accuracy and domain settings of the elementary table `Backend.elementaryWith`.

The defaults are the settings of `Backend.elementaryBounds?` at the default `Backend.Config`.
-/
structure ElementarySettings where
  /-- Taylor degree of the exponential. -/
  expDegree : Nat := 16
  /-- Series degree of the logarithm. -/
  logDegree : Nat := 16
  /-- Taylor degree of sine, cosine and tangent. -/
  trigDegree : Nat := 16
  /-- Series degree of the arctangent. -/
  atanDegree : Nat := 16
  /-- Degree of the arctangent and `π` series inside the inverse sine and cosine. -/
  inverseTrigDegree : Nat := 16
  /-- Taylor degree of the exponentials inside the hyperbolic sine, cosine and tangent. -/
  hyperbolicDegree : Nat := 16
  /-- Bits of the square-root grid, also inside the inverse sine and cosine without `total`. -/
  precision : Nat := 64
  /-- With `some bits`, endpoint values narrow the rounded midpoint bounds of sine and cosine on
  monotone panels, not necessarily the unrounded bounds. Tangent tries their quotient first. -/
  sharpTrig : Option Nat := none
  /-- Use the total square root, logarithm, inverse sine and inverse cosine. Logarithm accepts
  `[0, 0]` and strictly negative intervals only when `gridExpLog := none`. -/
  total : Bool := false
  /-- With `some bits`, the exponential and the logarithm use the binary-grid kernels at the ends
  of the interval, on the grid of `bits` fractional bits. -/
  gridExpLog : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/--
The settings of `Backend.elementaryBounds? config`: every degree is `config.degree`, square roots
have `config.precision` fractional bits, and `sharpTrig`, `total` and `gridExpLog` are off.
-/
def ElementarySettings.legacy (config : Backend.Config) : ElementarySettings where
  expDegree := config.degree
  logDegree := config.degree
  trigDegree := config.degree
  atanDegree := config.degree
  inverseTrigDegree := config.degree
  hyperbolicDegree := config.degree
  precision := config.precision

/--
Enclose the exponential on an interval by the binary-grid kernel `Enclosure.BinaryGrid.exp` at its
two ends, with Taylor degree `degree` on the grid of `bits` fractional bits.
-/
def gridExpBounds (I : Interval ℚ) (degree bits : Nat) : Interval ℚ :=
  monotoneBounds (fun x =>
    let J := Enclosure.BinaryGrid.exp x degree bits
    ⟨J.lo, J.hi⟩) I

/--
Enclose the logarithm on a positive interval by the binary-grid kernel `Enclosure.BinaryGrid.log`
at its two ends, with series degree `degree` on the grid of `bits` fractional bits. An interval
whose lower end is not positive gets `none`.
-/
def gridLogBounds? (I : Interval ℚ) (degree bits : Nat) : Option (Interval ℚ) :=
  if 0 < I.lo then
    some (monotoneBounds (fun x =>
      let J := Enclosure.BinaryGrid.log x degree bits
      ⟨J.lo, J.hi⟩) I)
  else none

namespace Backend

/--
Rational enclosures of the elementary operations at the settings `s`.

Arithmetic operations get `none`, because each backend sends them to its own arithmetic. An
enclosure also gets `none` on these intervals:
- for the logarithm, an interval whose lower end isn't positive, or, with `total` and without
  `gridExpLog`, only an interval that contains zero and another point.
- without `total`, for the square root an interval with a negative lower end, and for the inverse
  sine and cosine one that leaves `[-1, 1]` or has an end `x` inside where `√(1 - x²)` rounds down
  to zero at `s.precision` bits.
- for the tangent, an interval whose cosine enclosure contains zero.
-/
def elementaryWith (s : ElementarySettings) : UnaryOp → Interval ℚ → Option (Interval ℚ)
  | .exp, I =>
    some (match s.gridExpLog with
      | some bits => gridExpBounds I s.expDegree bits
      | none => expBounds I s.expDegree)
  | .log, I =>
    match s.gridExpLog with
    | some bits => gridLogBounds? I s.logDegree bits
    | none => if s.total then Total.log? I s.logDegree else logBounds? I s.logDegree
  | .sin, I =>
    some (match s.sharpTrig with
      | some bits => sharpSinBounds I s.trigDegree bits
      | none => sinBounds I s.trigDegree)
  | .cos, I =>
    some (match s.sharpTrig with
      | some bits => sharpCosBounds I s.trigDegree bits
      | none => cosBounds I s.trigDegree)
  | .tan, I =>
    match s.sharpTrig with
    | some bits =>
      match Internal.divRational? (sharpSinBounds I s.trigDegree bits)
          (sharpCosBounds I s.trigDegree bits) with
      | some J => some J
      | none => tanBounds? I s.trigDegree
    | none => tanBounds? I s.trigDegree
  | .asin, I =>
    if s.total then some (Total.asin I s.inverseTrigDegree)
    else asinBounds? I s.inverseTrigDegree s.precision
  | .acos, I =>
    if s.total then some (Total.acos I s.inverseTrigDegree)
    else acosBounds? I s.inverseTrigDegree s.precision
  | .atan, I => some (atanBounds I s.atanDegree)
  | .sinh, I => some (sinhBounds I s.hyperbolicDegree)
  | .cosh, I => some (coshBounds I s.hyperbolicDegree)
  | .tanh, I => some (tanhBounds I s.hyperbolicDegree)
  | .sqrt, I =>
    if s.total then some (Total.sqrt I s.precision) else sqrtBounds? I s.precision
  | _, _ => none

end Backend

end FloatLib.Numerics.Interval
