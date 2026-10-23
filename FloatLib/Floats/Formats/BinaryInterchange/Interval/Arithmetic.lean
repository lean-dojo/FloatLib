/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Core

/-!
# Outward-rounded arithmetic for `Model.Interval`

Each endpoint operation uses the corresponding directed `Model` kernel. Multiplication and
division use the classical four-corner construction. Division returns the whole interval when the
denominator contains zero, covering quotient sets that may be disconnected or unbounded.
Addition, subtraction, multiplication, and division pass computed endpoints through `ofBounds`,
replacing NaN or reversed endpoints with the format's whole range. For formats without infinity,
enclosing real results needs the relevant range bounds.

The finite endpoint formulas and outward rounding are described in Rump's
[Verification methods](https://doi.org/10.1017/S096249291000005X), §§5.1 and 5.3.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

/-- Outward-rounded interval addition. -/
@[inline] def add {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  ofBounds (Model.add A.lo B.lo (mode := .down)) (Model.add A.hi B.hi (mode := .up))

/-- Interval negation, reversing and negating the endpoints. -/
@[inline] def neg {fmt : FloatFormat} (A : Interval fmt) : Interval fmt :=
  ⟨Model.neg A.hi, Model.neg A.lo⟩

/-- Outward-rounded interval subtraction. -/
@[inline] def sub {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  ofBounds (Model.sub A.lo B.hi (mode := .down)) (Model.sub A.hi B.lo (mode := .up))

/-- Outward-rounded interval multiplication using all four endpoint products. -/
def mul {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  let p00 := Model.mul A.lo B.lo (mode := .down)
  let p01 := Model.mul A.lo B.hi (mode := .down)
  let p10 := Model.mul A.hi B.lo (mode := .down)
  let p11 := Model.mul A.hi B.hi (mode := .down)
  let q00 := Model.mul A.lo B.lo (mode := .up)
  let q01 := Model.mul A.lo B.hi (mode := .up)
  let q10 := Model.mul A.hi B.lo (mode := .up)
  let q11 := Model.mul A.hi B.hi (mode := .up)
  ofBounds (minOfFour p00 p01 p10 p11) (maxOfFour q00 q01 q10 q11)

/--
Outward-rounded interval division.

When the denominator contains zero, the result is `whole fmt`. Otherwise all four directed
quotients determine the endpoint enclosure.
-/
def div {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  if containsZero B then
    whole fmt
  else
    let p00 := Model.div A.lo B.lo (mode := .down)
    let p01 := Model.div A.lo B.hi (mode := .down)
    let p10 := Model.div A.hi B.lo (mode := .down)
    let p11 := Model.div A.hi B.hi (mode := .down)
    let q00 := Model.div A.lo B.lo (mode := .up)
    let q01 := Model.div A.lo B.hi (mode := .up)
    let q10 := Model.div A.hi B.lo (mode := .up)
    let q11 := Model.div A.hi B.hi (mode := .up)
    ofBounds (minOfFour p00 p01 p10 p11) (maxOfFour q00 q01 q10 q11)

/-- Interval reciprocal, conservatively returning `whole fmt` when zero is included. -/
@[inline] def inv {fmt : FloatFormat} (B : Interval fmt) : Interval fmt :=
  div (point (Model.posOne fmt)) B

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
