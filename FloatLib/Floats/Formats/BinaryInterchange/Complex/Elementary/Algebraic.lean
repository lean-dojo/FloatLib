/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Parts

/-!
# Correctly rounded complex square root and reciprocal square root

`ExecComplex.sqrt` is C's `csqrt` (C23 7.3.8.3, with the special values of Annex G, G.6.5.2), and
`ExecComplex.rsqrt` is `1 / csqrt z`. Each part of a finite result is the exact part rounded once,
in any rounding direction and for every binary format.

For `z = x + i y` with `y ≥ 0` and `N = |z|`, the principal root is
`√((N + x) / 2) + i √((N - x) / 2)` and its reciprocal is
`√((N + x) / (2 N²)) - i √((N - x) / (2 N²))`. Each part is a nested square root of rationals, so
exact rational arithmetic compares it with any rational (`compareHalfRoot`), also when it is
representable or halfway between two representable values. No intermediate is rounded, so nothing
overflows or underflows before the final rounding.

The lower half-plane is the conjugate (`Parts.ofUpperHalf`), which makes the root continuous onto
both sides of the cut along the negative real axis: `sqrt (-4 ± 0 i) = 0 ± 2 i` (C23 7.3.3).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open Posit.Model.RootRounding (compareRoot)

variable {fmt : FloatFormat}

/--
Compare `√((√normSq + x) / (2 * scale))` with a rational `boundary`, for `x² ≤ normSq` and a
positive `scale`.

A negative boundary is below the root. Otherwise squaring twice reduces the comparison to
`normSq` against `(2 * scale * boundary² - x)²`, through `compareRoot`.
-/
def compareHalfRoot (x normSq scale boundary : Rat) : Ordering :=
  if boundary < 0 then .gt
  else compareRoot normSq 2 (2 * scale * boundary * boundary - x)

/--
`csqrt` where the imaginary sign bit is clear, before rounding: the special values of C23
G.6.5.2 and the two nested roots of a finite argument.
-/
def sqrtCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  if Model.isInfinite z.im then ⟨.exact (Model.posInf fmt), .exact (Model.posInf fmt)⟩
  else if Model.isNaN z.re then ⟨.exact nan, .exact nan⟩
  else if Model.isInfinite z.re then
    if Model.isNaN z.im then
      if Model.signBit z.re then ⟨.exact nan, .exact (Model.posInf fmt)⟩
      else ⟨.exact (Model.posInf fmt), .exact nan⟩
    else if Model.signBit z.re then ⟨.exact (Model.zero fmt false), .exact (Model.posInf fmt)⟩
    else ⟨.exact (Model.posInf fmt), .exact (Model.zero fmt false)⟩
  else
    match Model.toRat? z.re, Model.toRat? z.im with
    | some x, some y =>
        let normSq := x * x + y * y
        ⟨.real (compareHalfRoot x normSq 1) false, .real (compareHalfRoot (-x) normSq 1) false⟩
    | _, _ => ⟨.exact nan, .exact nan⟩

/-- `csqrt` before rounding, on every input: `csqrt (conj z) = conj (csqrt z)`. -/
def sqrtParts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf sqrtCore

/--
The complex square root `csqrt` (C23 7.3.8.3 and G.6.5.2): the principal root, in the right
half-plane, with the branch cut along the negative real axis.

For a finite argument each part is the exact part rounded once in the direction `mode`
(`sqrt_eq`). The sign of a zero imaginary part selects the side of the cut, so
`sqrt (-4 ± 0 i) = 0 ± 2 i`. Special values follow G.6.5.2: `sqrt (x + i ∞) = ∞ + i ∞` for every
`x`, a NaN included, `sqrt (-∞ + i y) = 0 + i ∞` and `sqrt (∞ + i y) = ∞ + i 0` for finite
positive-signed `y`, and `sqrt (±0 + i 0) = 0 + i 0`.
-/
def sqrt (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (sqrtParts z).round mode

/--
`1 / csqrt z` where the imaginary sign bit is clear, before rounding.

A zero argument is a pole, an infinite argument gives a zero, and a finite nonzero one the two
nested roots over the squared modulus. The imaginary part is not positive.
-/
def rsqrtCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  if Model.isInfinite z.re || Model.isInfinite z.im then
    ⟨.exact (Model.zero fmt false), .exact (Model.zero fmt true)⟩
  else if Model.isNaN z.re || Model.isNaN z.im then ⟨.exact nan, .exact nan⟩
  else if Model.isZero z.re && Model.isZero z.im then ⟨.exact (Model.posInf fmt), .exact nan⟩
  else
    match Model.toRat? z.re, Model.toRat? z.im with
    | some x, some y =>
        let normSq := x * x + y * y
        ⟨.real (compareHalfRoot x normSq normSq) false,
          (Part.real (compareHalfRoot (-x) normSq normSq) false).neg⟩
    | _, _ => ⟨.exact nan, .exact nan⟩

/-- `1 / csqrt z` before rounding, on every input, by conjugation. -/
def rsqrtParts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf rsqrtCore

/--
The reciprocal square root `1 / csqrt z`, with `csqrt` the principal root of C23 7.3.8.3.

For a finite nonzero argument each part is the exact part of `1 / √z` rounded once in the
direction `mode` (`rsqrt_eq`), on the side of the cut that the sign of a zero imaginary part
selects: `rsqrt (-4 ± 0 i) = 0 ∓ 0.5 i`, and `rsqrt (4 ± 0 i) = 0.5 ∓ 0 i`. An infinite argument
gives `0 ∓ 0 i`, also beside a NaN, and a zero argument gives `∞ + i NaN`, the quotient
`(1 + 0 i) / (0 + 0 i)` of C23 G.5.2.
-/
def rsqrt (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (rsqrtParts z).round mode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
