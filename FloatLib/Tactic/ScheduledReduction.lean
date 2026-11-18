/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Mathlib.Util.TermReduce

/-!
# Scheduled IEEE reductions

The command declares the two evaluation orders of a reduction from one term map.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

set_option hygiene false in
/--
`scheduled_reduction name (input) := term` declares the reduction `name` of IEEE 754-2019 §9.4
in the two evaluation forms: `nameAlong acc out schedule` for an association order and
`nameInOrder acc out values` from left to right, both with the term `term` of an input of type
`input` in the accumulator format `acc`. The two are reducible, so the theorems and the
`roundoff` rule of `reduceAlong` and `reduceInOrder` apply to them as they are.
-/
macro alongDoc:docComment orderDoc:docComment "scheduled_reduction " name:ident
    " (" input:term ")" " := " term:term : command => do
  let along := Lean.mkIdent (name.getId.appendAfter "Along")
  let inOrder := Lean.mkIdent (name.getId.appendAfter "InOrder")
  `($alongDoc:docComment@[reducible] def $along (acc out : FloatFormat)
      (schedule : ReductionTree $input) :
        Model out :=
      reduceAlong acc out $term schedule
    $orderDoc:docComment
    @[reducible] def $inOrder (acc out : FloatFormat) (values : List $input) : Model out :=
      reduceInOrder acc out $term values)

set_option hygiene false in
/--
`in_order_rule name (input)` registers that a scheduled reduction's value is the value of
`reduceInOrder`. The generated equality unfolds the reducible operation once.
-/
macro "in_order_rule " name:ident " (" input:term ")" : command => do
  let member := Lean.mkIdent (name.getId.appendAfter "InOrder")
  let ruleName := Lean.mkIdent
    (Lean.Name.mkSimple ("toReal_" ++ name.getId.toString ++ "InOrder"))
  `(/--
    The value of the reduction from left to right is the value of `reduceInOrder` at its term.
    Registered with `roundoff`.
    -/
    @[roundoff_rule] theorem $ruleName (values : List $input) :
        toReal ($member acc out values) = toReal (delta% ($member acc out values)) :=
      rfl)

end FloatLib.Floats.Formats.BinaryInterchange.Model
