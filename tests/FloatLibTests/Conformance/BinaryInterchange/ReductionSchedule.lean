/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Proof

/-!
# The reductions of IEEE 754-2019 §9.4 over association order and accumulator format

A reduction of §9.4 may associate in any order and evaluate in any wider format, so it has no
unique result. The first part shows that on three binary16 values: the left-to-right sum in
binary16, the same sum along another association order, the left-to-right sum in a binary32
accumulator and the correctly rounded `Model.sum` are evaluated by Lean's kernel, and the first
differs from the other three, and two association orders of three binary32 values give `+0` and
one. The second part applies the error bounds of
`Reduction.Schedule.Proof` to concrete formats: the bound for an association order with its
finiteness premise proved, and the four bounds that `roundoff` generates for the left-to-right
loop, at every list length.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.ReductionSchedule

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Binary16 one. -/
def one : Model FloatFormat.binary16 := Model.ofNatBits 0x3c00

/-- Binary16 `2 ^ (-11)`, half a unit in the last place of one. -/
def half : Model FloatFormat.binary16 := Model.ofNatBits 0x1000

/-! ## Four members of the family on the same inputs -/

/-- From left to right in binary16 each `1 + 2 ^ (-11)` is a tie that rounds to one. -/
example : Model.toNatBits (Model.sumInOrder .binary16 .binary16 [one, half, half]) = 0x3c00 := by
  decide +kernel

/-- In a binary32 accumulator the sum is exact, and the result is `1 + 2 ^ (-10)`. -/
example : Model.toNatBits (Model.sumInOrder .binary32 .binary16 [one, half, half]) = 0x3c01 := by
  decide +kernel

/-- Another association order in binary16 adds the two small terms first and loses nothing. -/
def regrouped : ReductionTree (Model FloatFormat.binary16) :=
  .node (.leaf one) (.node (.leaf half) (.leaf half))

example : Model.toNatBits (Model.sumAlong .binary16 .binary16 regrouped) = 0x3c01 := by
  decide +kernel

/-- The correctly rounded member of the family. -/
example : Model.toNatBits (Model.sum FloatFormat.binary16 #[one, half, half] .nearest) =
    0x3c01 := by
  decide +kernel

/-- Binary32 one, `2 ^ 24` and `-2 ^ 24`. -/
def wide : Fin 3 → Model FloatFormat.binary32 :=
  ![Model.ofNatBits 0x3f800000, Model.ofNatBits 0x4b800000, Model.ofNatBits 0xcb800000]

/-- The same in binary32, where `1 + 2 ^ 24` is a tie that rounds to `2 ^ 24`: adding one first
gives `+0`, and cancelling the two large terms first gives one. -/
example :
    Model.toNatBits (Model.reduceAlong .binary32 .binary32 wide
        (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))) = 0 ∧
      Model.toNatBits (Model.reduceAlong .binary32 .binary32 wide
        (.node (.node (.leaf 1) (.leaf 2)) (.leaf 0))) = 0x3f800000 := by
  decide +kernel

/-- A reduction of length zero is `+0` (ISO/IEC TS 18661-4 draft N1797 §7.12.13a). -/
example : Model.toNatBits (Model.sumInOrder (src := .binary16) .binary32 .binary16 []) = 0 ∧
    Model.toNatBits (Model.dotInOrder (src := .binary16) .binary32 .binary16 []) = 0 := by
  decide +kernel

/-- `dot`, `sumAbs` and `sumSquare` from left to right in a binary32 accumulator. -/
example :
    Model.toNatBits (Model.dotInOrder .binary32 .binary16 [(one, half), (half, one)]) = 0x1400 ∧
      Model.toNatBits (Model.sumAbsInOrder .binary32 .binary16 [Model.neg one, half, half]) =
        0x3c01 ∧
      Model.toNatBits (Model.sumSquareInOrder .binary32 .binary16 [one, Model.neg one, half]) =
        0x4000 := by
  decide +kernel

/-! ## The error bounds at concrete formats -/

/-- Every intermediate result of the regrouped schedule in a binary32 accumulator is finite. -/
theorem regrouped_finite : Model.ReductionTree.FiniteEval
    (regrouped.map fun x => Model.cast .binary16 .binary32 x) := by
  simp only [regrouped, ReductionTree.map, Model.ReductionTree.FiniteEval, ReductionTree.eval]
  decide +kernel

/-- The bound for an association order, with its premises proved for this schedule. -/
example :=
  Model.abs_toReal_reduceAlong_sub_le (fun x => Model.cast .binary16 .binary32 x) regrouped
    (out := .binary16) (by decide) (by decide) regrouped_finite (by decide +kernel)

/-- The same bound in the depth of the order, which is two for the regrouped schedule. -/
example :=
  Model.abs_toReal_reduceAlong_sub_le_depth (fun x => Model.cast .binary16 .binary32 x) regrouped
    (out := .binary16) (by decide) (by decide) regrouped_finite (by decide +kernel)

/-- The loop is the member of the family along the left-leaning schedule from `+0`. -/
example (values : List (Model FloatFormat.binary16)) :
    Model.sumInOrder .binary32 .binary64 values =
      Model.reduceAlong .binary32 .binary64
        (fun v : Option (Model FloatFormat.binary16) =>
          v.elim (Model.zero .binary32 false) fun x => Model.cast .binary16 .binary32 x)
        ((ReductionTree.leaf none).extend (values.map some)) :=
  Model.reduceInOrder_eq_reduceAlong _ values

/--
The bound that `roundoff` generates for `sum`: binary16 inputs of any number, a binary32
accumulator and a binary64 result, against the exact real sum of the inputs.
-/
example (values : List (Model FloatFormat.binary16)) :=
  show _ → MixedError (Model.toReal (Model.sumInOrder .binary32 .binary64 values))
      (values.foldl (fun reference value => reference + value.toReal) 0) _ _ from
    Model.sumInOrder_mixedError .binary16 .binary32 .binary64 (by decide) (by decide) values

/-- The same for `sumAbs`, against the exact sum of the absolute values. -/
example (values : List (Model FloatFormat.binary16)) :=
  show _ → MixedError (Model.toReal (Model.sumAbsInOrder .binary32 .binary16 values))
      (values.foldl (fun reference value => reference + |value.toReal|) 0) _ _ from
    Model.sumAbsInOrder_mixedError .binary16 .binary32 .binary16 (by decide) (by decide) values

/-- The same for `sumSquare`, against the exact sum of the squares. -/
example (values : List (Model FloatFormat.bfloat16)) :=
  show _ → MixedError (Model.toReal (Model.sumSquareInOrder .binary64 .binary32 values))
      (values.foldl (fun reference value => reference + value.toReal * value.toReal) 0) _ _ from
    Model.sumSquareInOrder_mixedError .bfloat16 .binary64 .binary32 (by decide) (by decide) values

/-- The same for `dot`, against the exact dot product of the pairs. -/
example (values : List (Model FloatFormat.binary32 × Model FloatFormat.binary32)) :=
  show _ → MixedError (Model.toReal (Model.dotInOrder .binary64 .binary32 values))
      (values.foldl (fun reference value => reference + value.1.toReal * value.2.toReal) 0)
      _ _ from
    Model.dotInOrder_mixedError .binary32 .binary64 .binary32 (by decide) (by decide) values

/-- info: 'FloatLib.Floats.Formats.BinaryInterchange.Model.dotInOrder_mixedError' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Model.dotInOrder_mixedError

end FloatLibTests.Conformance.BinaryInterchange.ReductionSchedule
