/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Exponential
public import FloatLib.Numerics.Exact.Tanh.Prepared

/-!
# Correctly rounded complex tangents

`ExecComplex.tanh` is C's `ctanh` (C23 7.3.6.6 and G.6.3.6), and `ExecComplex.tan` is `ctan`
(7.3.5.6), defined as C defines it by `ctan z = -i ctanh (i z)` (G.6.1). Each part of a finite
result is the exact part rounded once, in any rounding direction and for every binary format.

In the first quadrant,

`tanh (a + i b) = sinh 2a / (cosh 2a + cos 2b) + i sin 2b / (cosh 2a + cos 2b)`.

`TanhComparison.compareRe` and `compareIm` compare the two quotients with any rational through
`exp (-2a)` and `exp (-4a)`, and the enclosures that answer most comparisons use `exp (-2a)`,
`cos b` and `sin b` in a form without cancellation (`tanhBounds?`). So a large `a`, where the
real part is within `8 exp (-2a)` of one and the imaginary part is of that size or underflows, a
small `a` or `b`, where a part is of that size, and an argument near a pole cost no more than an
ordinary one. On the imaginary axis `tanh (i b) = i tan b`, which the exact tangent comparator
handles behind the quotient of the enclosures of `sin b` and `cos b` (`tanBounds?`).

At a small argument each part lies next to a part of the argument, a representable number. The
same formulas on Taylor enclosures of `exp (-2a)`, `cos b` and `sin b` (`smallTanh?`,
`smallTan?`) separate the two, so the rounding compares nothing exactly there.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics

variable {fmt : FloatFormat}

/--
Enclose `exp (-2a)` for a positive `a`. Up to `2a = growthCap fmt` it is the grid exponential,
on a grid finer than `precision` by the bits that `exp (-2a)` and `a` lie below one, so that
`exp (-2a)` and `1 - exp (-2a)` keep their relative accuracy. Beyond, it is the interval from
zero to an upper bound of `exp (-growthCap fmt)`.
-/
def decayBounds (fmt : FloatFormat) (a : Rat) (precision : Nat) : RationalInterval :=
  if 2 * a ≤ growthCap fmt then
    expBounds ⟨-(2 * a), -(2 * a)⟩ ((precision + ⌈a * 3⌉₊ + bitsBelowOne a).sqrt + 8)
      (precision + ⌈a * 3⌉₊ + bitsBelowOne a)
  else
    ⟨0, (expBounds ⟨-(growthCap fmt : Rat), -(growthCap fmt : Rat)⟩
      ((precision + 2 * growthCap fmt).sqrt + 8) (precision + 2 * growthCap fmt)).hi⟩

/--
The real or the imaginary part of `tanh (a + i b)` in interval arithmetic on enclosures `u` of
`exp (-2a)`, `cosine` of `cos b` and `sine` of `sin b`, by the formulas of `tanhBounds?`. `none`
when the enclosure of the denominator reaches zero.
-/
def tanhFrom (imaginary : Bool) (u cosine sine : RationalInterval) : Option RationalInterval :=
  let v := (RationalInterval.point 1).sub u
  let denominator := (v.mul v).add ((u.scale 4).mul (cosine.mul cosine))
  if 0 < denominator.lo then
    some ((if imaginary then (u.scale 4).mul (sine.mul cosine)
      else v.mul ((RationalInterval.point 1).add u)).divPositive denominator)
  else none

/--
One enclosure of the real or the imaginary part of `tanh (a + i b)` for a positive `a`, in
interval arithmetic on an enclosure `u` of `exp (-2a)` and on `cos b` and `sin b`:

`(1 - u) (1 + u) / ((1 - u)² + 4 u cos² b)` and `4 u sin b cos b / ((1 - u)² + 4 u cos² b)`.

No term cancels, so each part keeps the relative accuracy of `1 - u`, `u`, `cos b` and `sin b`,
which come from `decayBounds` and `ProductComparison.trigBounds?`. `none` when the enclosure of
the denominator reaches zero.
-/
def tanhBounds? (imaginary : Bool) (u : RationalInterval) (b : Rat) (precision : Nat) :
    Option RationalInterval :=
  (ProductComparison.trigBounds? .cos ⟨b, b⟩ precision).bind fun cosine =>
    (ProductComparison.trigBounds? .sin ⟨b, b⟩ precision).bind fun sine =>
      tanhFrom imaginary u cosine sine

/--
One enclosure of the real or the imaginary part of `tanh (a + i b)` for `0 < a ≤ 1 / 32` and
`|b| ≤ 1 / 16`, by the formulas of `tanhFrom` on Taylor enclosures of `exp (-2a)`, `cos b` and
`sin b`, when it is tight for `fmt`. It keeps the relative accuracy of `a` and of `b`.
-/
def smallTanh? (fmt : FloatFormat) (imaginary : Bool) (a b : Rat) : Option RationalInterval :=
  if a ≤ 1 / 32 ∧ |b| ≤ 1 / 16 then
    (tanhFrom imaginary (Enclosure.expSmall (-(2 * a)) (smallDegree fmt (max (2 * a) |b|)))
      (Enclosure.cos b (smallDegree fmt (max (2 * a) |b|)))
      (Enclosure.sin b (smallDegree fmt (max (2 * a) |b|)))).bind (tightOnly fmt)
  else none

/--
One enclosure of the real or the imaginary part of `tanh (a + i b)` for a positive `a`: the
Taylor enclosure `smallTanh?` at a small argument, and `tanhBounds?` elsewhere. Beyond
`2a = growthCap fmt` it only tells that the real part is within a few `exp (-growthCap fmt)` of
one and the imaginary part of zero, which leaves the comparison with one or with zero to the
exact comparator.
-/
def tanhEnclosure? (fmt : FloatFormat) (imaginary : Bool) (a b : Rat) :
    Option RationalInterval :=
  if 0 < a then
    smallTanh? fmt imaginary a b <|>
      refineTwice fmt fun precision =>
        tanhBounds? imaginary (decayBounds fmt a precision) b precision
  else none

/--
One enclosure of `tan b` for `|b| ≤ 1 / 16`: the quotient of the Taylor enclosures of `sin b`
and `cos b`, when it is tight for `fmt`.
-/
def smallTan? (fmt : FloatFormat) (b : Rat) : Option RationalInterval :=
  if |b| ≤ 1 / 16 ∧ 0 < (Enclosure.cos b (smallDegree fmt |b|)).lo then
    tightOnly fmt
      ((Enclosure.sin b (smallDegree fmt |b|)).divPositive (Enclosure.cos b (smallDegree fmt |b|)))
  else none

/--
One enclosure of `tan b`: the quotient of the enclosures of `sin b` and `cos b`, where the
enclosure of the cosine does not reach zero.
-/
def tanBounds? (b : Rat) (precision : Nat) : Option RationalInterval :=
  (ProductComparison.trigBounds? .sin ⟨b, b⟩ precision).bind fun sine =>
    (ProductComparison.trigBounds? .cos ⟨b, b⟩ precision).bind fun cosine =>
      if 0 < cosine.lo then some (sine.divPositive cosine)
      else if cosine.hi < 0 then some (sine.neg.divPositive cosine.neg)
      else none

/-- `ctanh` where both sign bits are clear, before rounding (C23 G.6.3.6). -/
def tanhCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let zero := Model.zero fmt false
  match Model.toRat? z.re, Model.toRat? z.im with
  | some a, some b =>
      if ha : a = 0 then
        let exact := Thunk.mk fun _ => TrigonometricComparison.prepareTan b (cacheLevels fmt)
        ⟨Part.ofRat 0,
          (Part.real (fun boundary => exact.get.compare boundary) false).within
            (smallTan? fmt b <|> refineTwice fmt (tanBounds? b))⟩
      else
        ⟨(Part.real (TanhComparison.compareRe a b (cacheLevels fmt) ha) false).within
            (tanhEnclosure? fmt false a b),
          (Part.real (TanhComparison.compareIm a b (cacheLevels fmt) ha) false).within
            (tanhEnclosure? fmt true a b)⟩
  | none, some y =>
      if Model.isNaN z.re then
        if y = 0 then ⟨.exact nan, .exact zero⟩ else ⟨.exact nan, .exact nan⟩
      else ⟨.exact (Model.posOne fmt), .exact (Model.zero fmt (sinNegative (2 * y)))⟩
  | some x, none =>
      if x = 0 then ⟨.exact zero, .exact nan⟩ else ⟨.exact nan, .exact nan⟩
  | none, none =>
      if Model.isNaN z.re then ⟨.exact nan, .exact nan⟩
      else ⟨.exact (Model.posOne fmt), .exact zero⟩

/-- `ctanh` before rounding, on every input: odd, and `ctanh (conj z) = conj (ctanh z)`. -/
def tanhParts : ExecComplex fmt → Parts fmt := Parts.ofQuadrant true tanhCore

/--
The complex hyperbolic tangent `ctanh` (C23 7.3.6.6 and G.6.3.6).

For a finite argument each part is the exact part rounded once in the direction `mode`
(`tanh_eq`), also where `cosh 2a` is beyond the range of the format. Special values follow
G.6.3.6: `tanh (+0 + 0 i) = +0 + 0 i`, `tanh (∞ + i y) = 1 + i 0 sin 2y` for finite
positive-signed `y`, `tanh (∞ + ∞ i) = 1 ± 0 i`, `tanh (0 + ∞ i) = 0 + NaN i`.
-/
def tanh (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (tanhParts z).round mode

/-- `ctan` before rounding: `ctan z = -i ctanh (i z)` (C23 G.6.1). -/
def tanParts (z : ExecComplex fmt) : Parts fmt := (tanhParts (mulI z)).mulNegI

/--
The complex tangent `ctan` (C23 7.3.5.6). It is `-i ctanh (i z)`, as C23 G.6.1 specifies, with
both multiplications by `i` exact: each part of a finite result is the exact part rounded once in
the direction `mode` (`tan_eq`), and the special values are those of `ctanh`.
-/
def tan (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (tanParts z).round mode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
