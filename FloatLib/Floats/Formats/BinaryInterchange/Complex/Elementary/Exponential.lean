/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Logarithm
public import FloatLib.Numerics.Exact.Product.Prepared
public import FloatLib.Numerics.Exact.Product.Angle
public import FloatLib.Numerics.Exact.Trigonometric.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Product
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime

/-!
# Correctly rounded complex exponential, hyperbolic and trigonometric functions

`ExecComplex.exp` is C's `cexp` (C23 7.3.7.1 and G.6.4.1), `sinh` and `cosh` are `csinh` and
`ccosh` (7.3.6.5, 7.3.6.4, G.6.3.5, G.6.3.4), and `sin` and `cos` are `csin` and `ccos` (7.3.5.5,
7.3.5.4), defined as C defines them by `csin z = -i csinh (i z)` and `ccos z = ccosh (i z)`
(G.6.1). `expm1` is `cexp z - 1` rounded once. Each part of a finite result is the exact part
rounded once, in any rounding direction and for every binary format.

Each part is a product of an unbounded and a bounded factor:

* `exp (a + i b) = exp a * cos b + i exp a * sin b`;
* `sinh (a + i b) = sinh a * cos b + i cosh a * sin b`;
* `cosh (a + i b) = cosh a * cos b + i sinh a * sin b`.

`ProductComparison.prepare` compares such a product with any rational without forming the
unbounded factor, so `exp (a + i b)` is finite whenever its parts round to finite values, however
large `exp a` alone is, and an overflowing part is decided as cheaply as an ordinary one. The
products are irrational except at the exact values `0` and `1`, which the code returns directly.

One enclosure of each product answers the comparisons away from it. At a small argument, where
a part of `sinh`, `sin` or `expm1` lies next to a part of the argument and a part of `cosh`,
`cos` or `exp` next to one, it is the Taylor enclosure `smallProduct?` of `Small`, which
separates the two.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ProductComparison (Growth Trig Admissible)

variable {fmt : FloatFormat}

/-- The part with the exact rational value `q`. A zero is delivered with the sign `zeroSign`. -/
def Part.ofRat (q : Rat) (zeroSign : Bool := false) : Part fmt :=
  .real (fun boundary => cmp q boundary) zeroSign

/--
Subtract one from a part before rounding. A real moves its comparisons by one. Among the
encodings, a zero stands for the limit `exp (-∞) * cis y`, so it becomes `-1`, and an infinity or
a NaN is unchanged.
-/
def Part.subOne : Part fmt → Part fmt
  | .exact value => if Model.isZero value then .exact (Model.negOne fmt) else .exact value
  | .real compare zeroSign => .real (fun boundary => compare (boundary + 1)) zeroSign

/--
Enclose the exponential of a real known by the rational interval `exponent`: the grid exponential
at both endpoints, with `precision` fractional bits.
-/
def expBounds (exponent : RationalInterval) (degree precision : Nat) : RationalInterval :=
  ⟨(Enclosure.BinaryGrid.exp exponent.lo degree precision).lo,
    (Enclosure.BinaryGrid.exp exponent.hi degree precision).hi⟩

/--
Enclose `growth a` from the grid exponentials of `a` and `-a`, with `precision` fractional bits,
and for the hyperbolic sine as many more as `|a|` lies below one: `sinh a` is of the size of `a`.
-/
def growthBounds (growth : Growth) (a : Rat) (precision : Nat) : RationalInterval :=
  match growth with
  | .exp => expBounds ⟨a, a⟩ (precision.sqrt + 8) precision
  | .sinh =>
      ((expBounds ⟨a, a⟩ ((precision + bitsBelowOne |a|).sqrt + 8)
          (precision + bitsBelowOne |a|)).sub
        (expBounds ⟨-a, -a⟩ ((precision + bitsBelowOne |a|).sqrt + 8)
          (precision + bitsBelowOne |a|))).scale (1 / 2)
  | .cosh =>
      ((expBounds ⟨a, a⟩ (precision.sqrt + 8) precision).add
        (expBounds ⟨-a, -a⟩ (precision.sqrt + 8) precision)).scale (1 / 2)

/--
The largest `|a|` at which `productEnclosure?` encloses the unbounded factor. Beyond it the
exponential is far outside the range of the format, and the exact comparator decides overflow and
underflow through the logarithm of the boundary.
-/
def growthCap (fmt : FloatFormat) : Nat :=
  4 * ((Model.AlgebraicRounding.upperExponent fmt).toNat + fmt.fracWidth + 64)

/--
One enclosure of `growth a * trig b` for `|a| ≤ growthCap fmt`. At a small argument it is the
Taylor enclosure `smallProduct?`. Elsewhere the unbounded factor comes from the grid
exponential, on a grid finer by the number of bits that `exp (-|a|)` lies below one, so that a
small result keeps its relative accuracy, and the bounded factor from
`ProductComparison.trigBounds?`, which keeps its relative accuracy at an angle of any size.
-/
def productEnclosure? (fmt : FloatFormat) (growth : Growth) (trig : Trig) (a b : Rat) :
    Option RationalInterval :=
  smallProduct? fmt growth trig a b <|>
    if |a| ≤ growthCap fmt then
      refineTwice fmt fun precision =>
        (ProductComparison.trigBounds? trig ⟨b, b⟩ precision).map
          (growthBounds growth a (precision + ⌈|a| * 3 / 2⌉₊)).mul
    else none

/--
The part `growth a * trig b`, as an exact comparator. Where the product is rational it is
`exactValue`, which the caller supplies with the sign of an exact zero.

One enclosure of the product (`productEnclosure?`) answers the comparisons away from it. Where
there is none, for an `|a|` beyond `growthCap fmt`, the exact comparator alone decides, through
the logarithm of the boundary.
-/
def productPart (fmt : FloatFormat) (growth : Growth) (trig : Trig) (a b exactValue : Rat)
    (zeroSign : Bool := false) : Part fmt :=
  if h : Admissible growth trig a b then
    (Part.real (ProductComparison.prepare growth trig a b (cacheLevels fmt) h) zeroSign).within
      (productEnclosure? fmt growth trig a b)
  else Part.ofRat exactValue zeroSign

/--
The sign that an enclosure of `cos y` or `sin y` settles: whether the value is negative, or
`none` when the enclosure reaches zero.
-/
def enclosedNegative? (trig : Trig) (y : Rat) : Option Bool :=
  (ProductComparison.trigBounds? trig ⟨y, y⟩ 64).bind fun bounds =>
    if bounds.hi < 0 then some true else if 0 < bounds.lo then some false else none

/-- Whether `cos y` is negative: by an enclosure, and by exact comparison where it reaches zero. -/
def cosNegative (y : Rat) : Bool :=
  match enclosedNegative? .cos y with
  | some negative => negative
  | none => (TrigonometricComparison.prepareCos y 0).compare 0 == .lt

/-- Whether `sin y` is negative: by an enclosure, and by exact comparison where it reaches zero. -/
def sinNegative (y : Rat) : Bool :=
  match enclosedNegative? .sin y with
  | some negative => negative
  | none => (TrigonometricComparison.prepareSin y 0).compare 0 == .lt

/--
`value * cis y` for a positive infinity or zero `value` and a finite `y`: each part is `value`
with the sign of `cos y` or of `sin y` (C23 G.6.1, paragraph 10).
-/
def cisParts (value : Model fmt) (y : Rat) : Parts fmt :=
  ⟨.exact (if cosNegative y then Model.neg value else value),
    .exact (if sinNegative y then Model.neg value else value)⟩

/-- `cexp` where the imaginary sign bit is clear, before rounding (C23 G.6.4.1). -/
def expCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let zero := Model.zero fmt false
  let inf := Model.posInf fmt
  match Model.toRat? z.re, Model.toRat? z.im with
  | some a, some b => ⟨productPart fmt .exp .cos a b 1, productPart fmt .exp .sin a b 0⟩
  | none, some y =>
      if Model.isNaN z.re then
        if y = 0 then ⟨.exact nan, .exact zero⟩ else ⟨.exact nan, .exact nan⟩
      else if Model.signBit z.re then cisParts zero y
      else if y = 0 then ⟨.exact inf, .exact zero⟩
      else cisParts inf y
  | some _, none => ⟨.exact nan, .exact nan⟩
  | none, none =>
      if Model.isNaN z.re then ⟨.exact nan, .exact nan⟩
      else if Model.signBit z.re then ⟨.exact zero, .exact zero⟩
      else ⟨.exact inf, .exact nan⟩

/-- `cexp` before rounding, on every input: `cexp (conj z) = conj (cexp z)`. -/
def expParts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf expCore

/--
The complex exponential `cexp` (C23 7.3.7.1 and G.6.4.1).

For a finite argument `a + i b` each part is the exact part, `exp a * cos b` or `exp a * sin b`,
rounded once in the direction `mode` (`exp_eq`). The exponential `exp a` is never formed or
rounded on its own, so a part is finite whenever its rounding is. Special values follow G.6.4.1:
`exp (±0 + 0 i) = 1 + 0 i`, `exp (∞ + 0 i) = ∞ + 0 i`, `exp (-∞ + i y) = +0 cis y`,
`exp (∞ + i y) = ∞ cis y` for finite nonzero `y`, and `exp (x + ∞ i) = NaN + NaN i`.
-/
def exp (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (expParts z).round mode

/--
`cexp z - 1` where the imaginary sign bit is clear, before rounding. A zero argument is returned
unchanged.
-/
def expm1Core (z : ExecComplex fmt) : Parts fmt :=
  if Model.isZero z.re && Model.isZero z.im then ⟨.exact z.re, .exact z.im⟩
  else
    let w := expCore z
    ⟨w.re.subOne, w.im⟩

/-- `cexp z - 1` before rounding, on every input, by conjugation. -/
def expm1Parts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf expm1Core

/--
`exp z - 1` for a complex `z`: each part of a finite result is the exact part of `exp z - 1`
rounded once in the direction `mode` (`expm1_eq`), however small `z` is. A zero argument is
returned unchanged, `expm1 (-∞ + i y) = -1 ± 0 i` for finite `y`, and the other special values
are those of `cexp` (C23 G.6.4.1).
-/
def expm1 (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (expm1Parts z).round mode

/-- `csinh` where both sign bits are clear, before rounding (C23 G.6.3.5). -/
def sinhCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let zero := Model.zero fmt false
  let inf := Model.posInf fmt
  match Model.toRat? z.re, Model.toRat? z.im with
  | some a, some b =>
      ⟨productPart fmt .sinh .cos a b 0 (cosNegative b), productPart fmt .cosh .sin a b 0⟩
  | none, some y =>
      if Model.isNaN z.re then
        if y = 0 then ⟨.exact nan, .exact zero⟩ else ⟨.exact nan, .exact nan⟩
      else if y = 0 then ⟨.exact inf, .exact zero⟩
      else cisParts inf y
  | some x, none =>
      if x = 0 then ⟨.exact zero, .exact nan⟩ else ⟨.exact nan, .exact nan⟩
  | none, none =>
      if Model.isNaN z.re then ⟨.exact nan, .exact nan⟩ else ⟨.exact inf, .exact nan⟩

/-- `csinh` before rounding, on every input: odd, and `csinh (conj z) = conj (csinh z)`. -/
def sinhParts : ExecComplex fmt → Parts fmt := Parts.ofQuadrant true sinhCore

/--
The complex hyperbolic sine `csinh` (C23 7.3.6.5 and G.6.3.5).

For a finite argument `a + i b` each part is the exact part, `sinh a * cos b` or
`cosh a * sin b`, rounded once in the direction `mode` (`sinh_eq`), with no intermediate overflow.
Special values follow G.6.3.5: `sinh (+0 + 0 i) = +0 + 0 i`, `sinh (∞ + 0 i) = ∞ + 0 i`,
`sinh (∞ + i y) = ∞ cis y` for positive finite `y`, `sinh (+0 + ∞ i) = ±0 + NaN i`.
-/
def sinh (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (sinhParts z).round mode

/-- `ccosh` where both sign bits are clear, before rounding (C23 G.6.3.4). -/
def coshCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let zero := Model.zero fmt false
  let inf := Model.posInf fmt
  match Model.toRat? z.re, Model.toRat? z.im with
  | some a, some b =>
      ⟨productPart fmt .cosh .cos a b 1,
        productPart fmt .sinh .sin a b 0 (decide (a = 0) && sinNegative b)⟩
  | none, some y =>
      if Model.isNaN z.re then
        if y = 0 then ⟨.exact nan, .exact zero⟩ else ⟨.exact nan, .exact nan⟩
      else if y = 0 then ⟨.exact inf, .exact zero⟩
      else cisParts inf y
  | some x, none =>
      if x = 0 then ⟨.exact nan, .exact zero⟩ else ⟨.exact nan, .exact nan⟩
  | none, none =>
      if Model.isNaN z.re then ⟨.exact nan, .exact nan⟩ else ⟨.exact inf, .exact nan⟩

/-- `ccosh` before rounding, on every input: even, and `ccosh (conj z) = conj (ccosh z)`. -/
def coshParts : ExecComplex fmt → Parts fmt := Parts.ofQuadrant false coshCore

/--
The complex hyperbolic cosine `ccosh` (C23 7.3.6.4 and G.6.3.4).

For a finite argument `a + i b` each part is the exact part, `cosh a * cos b` or
`sinh a * sin b`, rounded once in the direction `mode` (`cosh_eq`), with no intermediate overflow.
Special values follow G.6.3.4: `cosh (+0 + 0 i) = 1 + 0 i`, `cosh (∞ + 0 i) = ∞ + 0 i`,
`cosh (∞ + i y) = ∞ cis y` for finite nonzero `y`, `cosh (+0 + ∞ i) = NaN ± 0 i`.
-/
def cosh (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (coshParts z).round mode

/-- `csin` before rounding: `csin z = -i csinh (i z)` (C23 G.6.1). -/
def sinParts (z : ExecComplex fmt) : Parts fmt := (sinhParts (mulI z)).mulNegI

/--
The complex sine `csin` (C23 7.3.5.5). It is `-i csinh (i z)`, as C23 G.6.1 specifies, with both
multiplications by `i` exact: each part of a finite result is the exact part,
`sin a * cosh b` or `cos a * sinh b`, rounded once in the direction `mode` (`sin_eq`), and the
special values are those of `csinh`.
-/
def sin (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (sinParts z).round mode

/-- `ccos` before rounding: `ccos z = ccosh (i z)` (C23 G.6.1). -/
def cosParts (z : ExecComplex fmt) : Parts fmt := coshParts (mulI z)

/--
The complex cosine `ccos` (C23 7.3.5.4). It is `ccosh (i z)`, as C23 G.6.1 specifies, with the
multiplication by `i` exact: each part of a finite result is the exact part, `cos a * cosh b` or
`-sin a * sinh b`, rounded once in the direction `mode` (`cos_eq`), and the special values are
those of `ccosh`.
-/
def cos (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (cosParts z).round mode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
