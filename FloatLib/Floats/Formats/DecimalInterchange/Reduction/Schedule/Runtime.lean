/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Sign.Runtime
public import FloatLib.Numerics.Reduction.Tree

/-!
# The decimal reductions of IEEE 754-2019 §9.4 in a chosen order and accumulator format

IEEE 754-2019 §9.4 leaves the evaluation of its reductions free. In the words of ISO/IEC TS
18661-4 (WG14 N1797, Introduction), which binds them to C: "These operations, which compute sums
and products, may associate in any order and may evaluate in any wider format. Hence, unlike
other IEC 60559 operations, they do not have unique specified results."

`Arithmetic.sum`, `dot`, `sumSquare` and `sumAbs` are one member of that family: they accumulate
without error and round once. This module defines the family over the freedom, for the four
reductions that add terms, in every decimal format and rounding direction:

* `reduceAlong acc out mode term schedule` forms the term of every input in the accumulator
  format `acc`, adds the terms in the association order `schedule` (a `Numerics.ReductionTree`,
  so every parenthesization of a nonempty reduction), with one rounding in `mode` at each
  addition, and converts the result to the destination format `out`.
* `reduceInOrder acc out mode term values` is the left-to-right member that a loop computes,
  for a list of any length. The empty reduction is `+0`, as for `sum`.
  `Reduction.Schedule.Proof` proves it equal to `reduceAlong` along the left chain.
* `Reduction.sumTerm`, `sumAbsTerm`, `sumSquareTerm` and `dotTerm` are the terms of the four
  reductions: the element, its absolute value, its square, and the product of a pair, each
  formed in the accumulator format.

The result carries the flags of every step: the formation of each term, each addition, and the
final conversion. So a result without `overflow` had no overflow on the way, and a result
without `inexact` is the exact sum of its inputs. The quantum of the result is the one that the
chain of additions gives, by the preferred quantum of each addition.

The source data may be of any decimal formats, since a `Datum` carries none. The standard's
"wider format" is an accumulator whose precision and quantum range contain those of the data.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

open FloatLib.Numerics
open Conversion (convertFormat)

namespace Reduction

/--
Apply an operation of two decimal operands to the values of two outcomes. The flags of the two
outcomes and of the operation accumulate.
-/
def lift₂ (operation : Datum → Datum → Outcome) (left right : Outcome) : Outcome :=
  let result := operation left.value right.value
  { value := result.value, status := (left.status.union right.status).union result.status }

/-- Convert the value of an outcome into the format `out`. The flags of the outcome and of the
conversion accumulate. -/
def finish (out : Format) (mode : RoundingMode) (total : Outcome) : Outcome :=
  let result := convertFormat out mode total.value
  { value := result.value, status := total.status.union result.status }

/-- The term of `sum`: the element, converted to the accumulator format. -/
def sumTerm (acc : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  convertFormat acc mode x

/-- The term of `sumAbs`: the absolute value of the element, converted to the accumulator
format. -/
def sumAbsTerm (acc : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  convertFormat acc mode x.abs

/-- The term of `sumSquare`: the element, converted to the accumulator format and squared there
with one rounding. -/
def sumSquareTerm (acc : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  lift₂ (mul acc mode) (convertFormat acc mode x) (convertFormat acc mode x)

/-- The term of `dot`: the two members of a pair, converted to the accumulator format and
multiplied there with one rounding. -/
def dotTerm (acc : Format) (mode : RoundingMode) (pair : Datum × Datum) : Outcome :=
  lift₂ (mul acc mode) (convertFormat acc mode pair.1) (convertFormat acc mode pair.2)

end Reduction

/--
A reduction of IEEE 754-2019 §9.4 in the association order `schedule`, evaluated in the
accumulator format `acc`: `term` gives the term of each input, every addition of the schedule
rounds once in `mode` in `acc`, and the result is converted to `out`. The flags of all steps
accumulate.
-/
def reduceAlong {α : Type} (acc out : Format) (mode : RoundingMode) (term : α → Outcome)
    (schedule : ReductionTree α) : Outcome :=
  Reduction.finish out mode (schedule.eval (Reduction.lift₂ (add acc mode)) term)

/--
A reduction of IEEE 754-2019 §9.4 from left to right, evaluated in the accumulator format
`acc`: the terms are added in list order, with one rounding in `mode` at each addition, and the
result is converted to `out`. The flags of all steps accumulate. An empty list gives `+0`.
-/
def reduceInOrder {α : Type} (acc out : Format) (mode : RoundingMode) (term : α → Outcome) :
    List α → Outcome
  | [] => project out mode 0 0
  | first :: rest =>
      Reduction.finish out mode
        (rest.foldl (fun total value => Reduction.lift₂ (add acc mode) total (term value))
          (term first))

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
