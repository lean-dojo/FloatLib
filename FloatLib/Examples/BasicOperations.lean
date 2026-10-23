/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats

/-!
# Basic operations

What does `0.1 + 0.2` give in binary32, and how do we prove something about it? This file answers
that question with ordinary Lean code. A value's type chooses its format, the same value can be
computed with `+` and used in a theorem, and rounding directions and status flags are available
through named operations when we need them.

To try any definition, start a scratch file with `import FloatLib`, copy the namespace openings and
definitions you need, and add `#eval` followed by the value's name. The comment after a computed
example shows what `#eval` prints.
-/

@[expose] public section

namespace FloatLib.Examples.BasicOperations

open FloatLib.Floats
open FloatLib.Rounding

/-! ## The famous sum -/

private def tenthPlusFifth : Binary32 :=
  0.1 + 0.2
-- 0.3

/-
The stored value is 0.300000011920928955078125. Binary values print a decimal that reads
back as the same value, normally the shortest one, and `ExecFloat.Binary.format` with
`(style := .exact)` prints every digit. Neither 0.1 nor 0.2 is a binary fraction, so each literal is
rounded once when it is read, and the sum is rounded once more.
-/

private def sameAsLiteral : Bool :=
  tenthPlusFifth == 0.3
-- true

private def sameAsLiteral64 : Bool :=
  ((0.1 : Binary64) + 0.2) == 0.3
-- false

/-
In binary32 the rounded sum happens to land on the same value as the rounded literal `0.3`. In
binary64 it doesn't, and that's the `0.30000000000000004` most programmers have met. Nothing here
is special to FloatLib, but we can now say exactly what happened and prove it.
-/

/-! ## Compute with a format, then reason about the same operation -/

private def x : Binary32 := 6

private def y : Binary32 := 4

private def sum : Binary32 := x + y
-- 10

private def product : Binary32 := x * y
-- 24

/-
Both results are exact because 10 and 24 are representable. The theorem below is not about these
particular inputs: for every pair of binary32 values, the `+` we just ran is the format's reference
addition, including its rounding and exceptional-value rules. Real-valued error bounds build on
this equation together with the format's rounding theorems.
-/
example (a b : Binary32) :
    a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b

/-! ## Choose a rounding direction and inspect the status -/

private def thirdUp : Binary32 :=
  ExecFloat.Binary.div 1 3 (mode := up)
-- 0.33333334

private def thirdDownOutcome :=
  ExecFloat.Binary.div (1 : Binary32) 3 (mode := down) (status := true)
-- { value := 0.3333333,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false,
--     inexact := true },
--   ternary := Ordering.lt }

private def divisionWasRounded : Bool :=
  thirdDownOutcome.status.inexact
-- true

private def roundedBelow : Bool :=
  thirdDownOutcome.ternary == .lt
-- true

/-
One third is not a binary fraction, so the two directed roundings return the neighbours above and
below it, printed as 0.33333334 and 0.3333333. `up` and `down` are the rounding directions toward
positive and negative infinity, available without a leading dot after `open FloatLib.Rounding`.
Plain `/` rounds to nearest, ties to even, and picks the upper neighbour for this input. With
`status := true` the division also returns the IEEE flags and the ternary value. `inexact` tells us
that rounding changed the value, and the ternary value `.lt` that the delivered value is below the
exact quotient, as in MPFR.
-/

/-! ## Use collections and round a reduction only once -/

private def values : List Binary32 :=
  [1.5, 2, 4]

private def squares : List Binary32 :=
  values.map fun value => value * value
-- [2.25, 4, 16]

private def exactSum : Binary32 :=
  ExecFloat.Binary.sumList [16777216, 1, -16777216]
-- 1

/-
A left-to-right fold would return 0: binary32 has 24 significant bits, so `16777216 + 1` rounds
back to `16777216`, and subtracting `16777216` then leaves nothing.
`sumList` accumulates the exact sum and rounds once at the end, so the middle term survives.
-/

private def exactDot :
    Except Numerics.ReductionError Binary32 :=
  ExecFloat.Binary.dotList values [2, 3, 4]
-- Except.ok 25

private def mismatchedDot :
    Except Numerics.ReductionError Binary32 :=
  ExecFloat.Binary.dotList values [2, 3]
-- Except.error (ReductionError.lengthMismatch 3 2)

/-
`1.5 * 2 + 2 * 3 + 4 * 4 = 25`, again with one rounding at the end. The dot product checks that
both lists have the same length and reports a mismatch instead of silently truncating.
-/

/-! ## Convert explicitly and inspect the stored value -/

private def positValue : Posit16 :=
  1.5
-- 1.5

private def asPosit : ExecFloat.ConversionOutcome Posit16 :=
  x.cast (target := Posit16)
-- ConversionOutcome.success 6 { inexact := false, overflow := false, ... }

/-
There is no implicit promotion between formats. A cast names its destination and returns an
outcome that carries the converted value with its conversion status, or a failure with its reason.
Here 6 is representable in Posit16 and every flag is false.
-/

private def exactMeaning : Option Rat :=
  ExecFloat.Binary.toRat? sum
-- some 10

private def storedPositBits : Nat :=
  ExecFloat.Posit.toNatBits positValue
-- 17408

/-
Ordinary display needs no conversion: `#eval sum` prints `10`, and `s!"sum = {sum}"` uses the same
formatter. `toRat?` gives the exact rational for a calculation or proof. It forgets signed zero and
returns `none` for every nonfinite value. The packed word from `toNatBits` is for serialisation,
and arithmetic works on `positValue` itself.
-/

end FloatLib.Examples.BasicOperations
