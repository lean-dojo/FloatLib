/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Parts
public import FloatLib.Numerics.Enclosure.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime
public import FloatLib.Numerics.Exact.Product.Angle
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor

/-!
# Enclosures of the parts of a complex function at a small argument

Where a function is the identity to first order, as `sin`, `sinh`, `tan`, `tanh`, `atan`,
`atanh`, `expm1` and `log1p` are, the result at a small argument `z` is `z` up to a correction
that is small against `|z|`: of relative order `|z|²` for the six odd functions, whose next
term is cubic, and of relative order `|z|` for `expm1` and `log1p`, whose next term is
`z² / 2`. A part of the result can then lie so close to a representable number, a part of the
argument, that an enclosure at the working precision of the format contains that number, and
the rounding would compare the part with it exactly, at a cost that grows with the exponent of
the argument. The bound is on the complex value against `|z|`. One part alone need not be near
the same part of the argument: the real part of `expm1 (i t)` is `cos t - 1`, and the real
part of `i t` is zero.

The enclosures of this module are Taylor polynomials in exact rational arithmetic with their
remainder bounds (`Enclosure.expSmall`, `Enclosure.sin`, `Enclosure.cos`, `Enclosure.logOneSub`
and `Enclosure.atanSmall`). Their width relative to the part is a power of the argument, four
orders beyond the working precision of the format. An enclosure that is tight for the format
(`isTight`) separates the part from the representable numbers next to it, and the rounding
needs no exact comparison. The degree falls as the argument gets smaller: a subnormal argument
takes a polynomial of degree four.

* `smallDegree`: the degree for an argument of a given size;
* `smallProduct?`: `growth a * trig b` for `|a| ≤ 1 / 16` and `|b| ≤ 1 / 16`, the parts of
  `exp`, `expm1`, `sinh`, `cosh`, `sin` and `cos`;
* `smallLog?`: `log q` for `|q - 1| ≤ 1 / 16`, the real part of `log1p` and `atanh`;
* `smallArg?`: `arg (x + i y)` for `|y| ≤ x / 16`, their imaginary part.

Each returns `none` outside its range and when its enclosure is not tight for the format
(`isTight`), where the general enclosure of the part takes over. `SmallProof` proves that every
returned enclosure contains the part.

`dyadicAround` serves the general enclosures at an argument with one small part: it replaces
a rational that is written with thousands of bits (`isLong`) by a short interval around it.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ProductComparison (Growth Trig)

/--
The degree of a Taylor enclosure at an argument of magnitude `size`, for `size ≤ 1 / 16`: the
terms that the working precision of `fmt` needs at that size, and four more. The remainder is
then below the argument to the power of four, relatively, at every size.
-/
def smallDegree (fmt : FloatFormat) (size : Rat) : Nat :=
  (fmt.fracWidth + 16) / bitsBelowOne size + 4

/-- An enclosure, when it determines the rounding in `fmt` away from the rounding boundaries. -/
def tightOnly (fmt : FloatFormat) (interval : RationalInterval) : Option RationalInterval :=
  if isTight fmt interval then some interval else none

/--
A rational interval around `q` whose endpoints are multiples of a power of two with about
`bits` significant bits. For `q ≠ 0` its width is at most `|q| * 2 ^ (1 - bits)`, and around
zero it is `[0, 2 ^ (-bits)]`.

A series evaluated in exact rational arithmetic costs as much as its argument is long. A part of
an argument that is subnormal makes the argument of a logarithm or of an arctangent thousands
of bits long, whatever its size, and a monotone function is enclosed as well from the two ends
of this interval.
-/
def dyadicAround (q : Rat) (bits : Nat) : RationalInterval :=
  ⟨(⌊q * (2 : Rat) ^ ((bits : Int) + (q.den.log2 : Int) - (q.num.natAbs.log2 : Int))⌋ : Rat) /
      (2 : Rat) ^ ((bits : Int) + (q.den.log2 : Int) - (q.num.natAbs.log2 : Int)),
    ((⌊q * (2 : Rat) ^ ((bits : Int) + (q.den.log2 : Int) - (q.num.natAbs.log2 : Int))⌋ + 1 :
        Int) : Rat) /
      (2 : Rat) ^ ((bits : Int) + (q.den.log2 : Int) - (q.num.natAbs.log2 : Int))⟩

/-- Whether `q` is written with more than eight times `bits` bits: long enough for the two
series at the ends of `dyadicAround q bits` to cost less than one series at `q`. -/
def isLong (q : Rat) (bits : Nat) : Bool :=
  decide (8 * bits < q.num.natAbs.log2 + q.den.log2)

/--
Enclose `growth a` for `|a| ≤ 1` from the Taylor polynomial of the exponential at `a` and at
`-a`, with its remainder. The hyperbolic sine keeps the relative accuracy of `a`: the constant
terms of the two polynomials cancel exactly.
-/
def smallGrowth (growth : Growth) (a : Rat) (degree : Nat) : RationalInterval :=
  match growth with
  | .exp => Enclosure.expSmall a degree
  | .sinh =>
      ((Enclosure.expSmall a degree).sub (Enclosure.expSmall (-a) degree)).scale (1 / 2)
  | .cosh =>
      ((Enclosure.expSmall a degree).add (Enclosure.expSmall (-a) degree)).scale (1 / 2)

/-- Enclose `cos b` or `sin b` by its Taylor polynomial with the Lagrange remainder. -/
def smallTrig (trig : Trig) (b : Rat) (degree : Nat) : RationalInterval :=
  match trig with
  | .cos => Enclosure.cos b degree
  | .sin => Enclosure.sin b degree

/--
One enclosure of `growth a * trig b` for `|a| ≤ 1 / 16` and `|b| ≤ 1 / 16`, from Taylor
polynomials of the two factors, when it is tight for `fmt`.
-/
def smallProduct? (fmt : FloatFormat) (growth : Growth) (trig : Trig) (a b : Rat) :
    Option RationalInterval :=
  if |a| ≤ 1 / 16 ∧ |b| ≤ 1 / 16 then
    tightOnly fmt
      ((smallGrowth growth a (smallDegree fmt (max |a| |b|))).mul
        (smallTrig trig b (smallDegree fmt (max |a| |b|))))
  else none

/--
One enclosure of `log q` for `|q - 1| ≤ 1 / 16`, from the Taylor polynomial of
`log (1 - (1 - q))`, when it is tight for `fmt`. It keeps the relative accuracy of `q - 1`.
-/
def smallLog? (fmt : FloatFormat) (q : Rat) : Option RationalInterval :=
  if |1 - q| ≤ 1 / 16 then
    tightOnly fmt (Enclosure.logOneSub (1 - q) (smallDegree fmt |1 - q|))
  else none

/--
One enclosure of `arg (x + i y)` for a positive `x` and `|y| ≤ x / 16`, from the Taylor
polynomial of `arctan (y / x)`, when it is tight for `fmt`.
-/
def smallArg? (fmt : FloatFormat) (x y : Rat) : Option RationalInterval :=
  if 0 < x ∧ |y| ≤ x / 16 then
    tightOnly fmt (Enclosure.atanSmall (y / x) (smallDegree fmt |y / x|))
  else none

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
