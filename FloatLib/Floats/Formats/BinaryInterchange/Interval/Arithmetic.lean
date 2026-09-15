/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Core

/-!
# Outward-rounded arithmetic for `Model.Interval`

Each endpoint operation uses the corresponding directed `Model` kernel. Multiplication and
division use the classical four-corner construction. Division returns the whole interval when the
denominator contains zero because a single closed interval cannot represent the resulting
disconnected quotient set. Addition, subtraction, multiplication, and division pass computed
endpoints through `ofBounds`, replacing NaN or reversed endpoints with the format's whole range.
For formats without infinity, enclosure of real results still requires the relevant range bounds.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

/-- Outward-rounded interval addition. -/
@[inline] def add {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  ofBounds (Model.addDown A.lo B.lo) (Model.addUp A.hi B.hi)

/-- Interval negation, reversing and negating the endpoints. -/
@[inline] def neg {fmt : FloatFormat} (A : Interval fmt) : Interval fmt :=
  ⟨Model.neg A.hi, Model.neg A.lo⟩

/-- Outward-rounded interval subtraction. -/
@[inline] def sub {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  ofBounds (Model.subDown A.lo B.hi) (Model.subUp A.hi B.lo)

/-- Outward-rounded interval multiplication using all four endpoint products. -/
def mul {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  let p00 := Model.mulDown A.lo B.lo
  let p01 := Model.mulDown A.lo B.hi
  let p10 := Model.mulDown A.hi B.lo
  let p11 := Model.mulDown A.hi B.hi
  let q00 := Model.mulUp A.lo B.lo
  let q01 := Model.mulUp A.lo B.hi
  let q10 := Model.mulUp A.hi B.lo
  let q11 := Model.mulUp A.hi B.hi
  ofBounds (minOfFour p00 p01 p10 p11) (maxOfFour q00 q01 q10 q11)

/--
Outward-rounded interval division.

When the denominator contains zero, the result is `whole fmt`; otherwise all four directed
quotients determine the endpoint enclosure.
-/
def div {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  if containsZero B then
    whole fmt
  else
    let p00 := Model.divDown A.lo B.lo
    let p01 := Model.divDown A.lo B.hi
    let p10 := Model.divDown A.hi B.lo
    let p11 := Model.divDown A.hi B.hi
    let q00 := Model.divUp A.lo B.lo
    let q01 := Model.divUp A.lo B.hi
    let q10 := Model.divUp A.hi B.lo
    let q11 := Model.divUp A.hi B.hi
    ofBounds (minOfFour p00 p01 p10 p11) (maxOfFour q00 q01 q10 q11)

/-- Interval reciprocal, conservatively returning `whole fmt` when zero is included. -/
@[inline] def inv {fmt : FloatFormat} (B : Interval fmt) : Interval fmt :=
  div (point (Model.posOne fmt)) B

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
