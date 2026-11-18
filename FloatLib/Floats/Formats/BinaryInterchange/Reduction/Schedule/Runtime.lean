/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.ScheduledReduction

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Numerics.Reduction.Tree

/-!
# The reductions of IEEE 754-2019 §9.4 in a chosen order and accumulator format

IEEE 754-2019 §9.4 leaves the evaluation of its reductions free. In the words of ISO/IEC TS
18661-4 (WG14 N1797, Introduction), which binds them to C: "These operations, which compute sums
and products, may associate in any order and may evaluate in any wider format. Hence, unlike
other IEC 60559 operations, they do not have unique specified results."

`Model.sum`, `dot`, `sumSquare` and `sumAbs` are one member of that family: they accumulate
without error and round once. This module defines the family over the freedom, for the four
reductions that add terms:

* `reduceAlong acc out term schedule` converts every input to a term in the accumulator format
  `acc`, adds the terms in the association order `schedule` (a `Numerics.ReductionTree`, so
  every parenthesization of a nonempty reduction), with one rounding to nearest-even at each
  addition, and converts the result to the destination format `out`.
* `reduceInOrder acc out term values` is the left-to-right member that a loop computes, from
  `+0`, for a list of any length. `Reduction.Schedule.Proof` proves it equal to `reduceAlong`
  along the left-leaning schedule.
* `sumAlong`, `sumAbsAlong`, `sumSquareAlong`, `dotAlong` and `sumInOrder`, `sumAbsInOrder`,
  `sumSquareInOrder`, `dotInOrder` are the four reductions at their terms: the element, its
  absolute value, its square, and the product of a pair, each formed in the accumulator format.

The source, accumulator and destination formats are arbitrary descriptors. The standard's
"wider format" is an accumulator whose grid contains the source grid; the error bounds of
`Reduction.Schedule.Proof` state that as two hypotheses on the descriptors.
-/

@[expose] public section

namespace FloatLib.Numerics.ReductionTree

/--
The schedule that adds the values of a list, in order, to the right of `start`:
`((start + v₁) + v₂) + …`.
-/
def extend {α : Type*} (start : ReductionTree α) : List α → ReductionTree α
  | [] => start
  | value :: rest => extend (.node start (.leaf value)) rest

end FloatLib.Numerics.ReductionTree

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/--
A reduction of IEEE 754-2019 §9.4 in the association order `schedule`, evaluated in the
accumulator format `acc`: `term` gives the term of each input, every addition of the schedule
rounds once to nearest-even in `acc`, and the result is converted to `out`.
-/
def reduceAlong {α : Type} (acc out : FloatFormat) (term : α → Model acc)
    (schedule : ReductionTree α) : Model out :=
  cast acc out (schedule.eval (fun x y => add x y) term)

/--
A reduction of IEEE 754-2019 §9.4 from left to right, evaluated in the accumulator format
`acc`: the terms are added in list order to `+0`, with one rounding to nearest-even at each
addition, and the result is converted to `out`. An empty list gives `+0`.
-/
def reduceInOrder {α : Type} (acc out : FloatFormat) (term : α → Model acc) (values : List α) :
    Model out :=
  cast acc out (values.foldl (fun s v => add s (term v)) (zero acc false))

variable {src : FloatFormat}


/--
IEEE 754-2019 §9.4 `sum` (C `reduc_sum`, N1797 7.12.13a.1) in the association order `schedule`:
the elements are converted to the accumulator format `acc` and added there with one rounding
at each addition, and the result is converted to `out`.
-/
/--
IEEE 754-2019 §9.4 `sum` (C `reduc_sum`, N1797 7.12.13a.1) from left to right: the elements are
converted to the accumulator format `acc` and added in order to `+0`, with one rounding at each
addition, and the result is converted to `out`.
-/
scheduled_reduction sum (Model src) := (fun x => cast src acc x)

/--
IEEE 754-2019 §9.4 `sumAbs` (C `reduc_sumabs`, N1797 7.12.13a.2) in the association order
`schedule`: the absolute values of the elements, converted to the accumulator format `acc`, are
added there with one rounding at each addition, and the result is converted to `out`.
-/
/--
IEEE 754-2019 §9.4 `sumAbs` (C `reduc_sumabs`, N1797 7.12.13a.2) from left to right: the
absolute values of the elements, converted to the accumulator format `acc`, are added in order
to `+0`, with one rounding at each addition, and the result is converted to `out`.
-/
scheduled_reduction sumAbs (Model src) := (fun x => abs (cast src acc x))

/--
IEEE 754-2019 §9.4 `sumSquare` (C `reduc_sumsq`, N1797 7.12.13a.3) in the association order
`schedule`: every element is converted to the accumulator format `acc` and squared there with
one rounding, the squares are added with one rounding at each addition, and the result is
converted to `out`.
-/
/--
IEEE 754-2019 §9.4 `sumSquare` (C `reduc_sumsq`, N1797 7.12.13a.3) from left to right: every
element is converted to the accumulator format `acc` and squared there with one rounding, the
squares are added in order to `+0`, with one rounding at each addition, and the result is
converted to `out`.
-/
scheduled_reduction sumSquare (Model src) :=
  (fun x => mul (cast src acc x) (cast src acc x))

/--
IEEE 754-2019 §9.4 `dot` (C `reduc_sumprod`, N1797 7.12.13a.4) in the association order
`schedule` of the pairs: the two members of a pair are converted to the accumulator format
`acc` and multiplied there with one rounding, the products are added with one rounding at each
addition, and the result is converted to `out`.
-/
/--
IEEE 754-2019 §9.4 `dot` (C `reduc_sumprod`, N1797 7.12.13a.4) from left to right over the
pairs: the two members of a pair are converted to the accumulator format `acc` and multiplied
there with one rounding, the products are added in order to `+0`, with one rounding at each
addition, and the result is converted to `out`.
-/
scheduled_reduction dot (Model src × Model src) :=
  (fun (pair : Model src × Model src) => mul (cast src acc pair.1) (cast src acc pair.2))

end FloatLib.Floats.Formats.BinaryInterchange.Model
