/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Runtime

/-!
# Kernel rules for the reductions in a chosen order

`Model.reduceInOrder` and `Model.reduceAlong` are the reductions of IEEE 754-2019 §9.4 with one
rounding at each addition: from left to right, or along a tree. `sumInOrder`, `sumAbsInOrder`,
`sumSquareInOrder`, `dotInOrder` and their `…Along` forms are these two at the term of each
reduction, and unfold to them.

On encodings a reduction is a chain of the kernel additions of the accumulator format:

* `foldAdd acc term state values` is the encoding of the left-to-right sum of the terms of
  `values`, started at the encoding `state` (`foldAdd_eq`), and `evalWord acc term schedule`
  the encoding of the sum along a tree (`evalWord_eq`). `toNatBits_reduceInOrder` and
  `toNatBits_reduceAlong` rewrite the encoding of a reduction with them and with the kernel
  cast into the destination format.
* `foldAdd_cons`, `foldAdd_nil`, `evalWord_node` and `evalWord_leaf` unroll a reduction over a
  literal list or tree into the chain of additions, so that the term of every element is a
  closed term.
* `toNatBits_cast_toModel`, `toNatBits_abs`, `toNatBits_mul` and `toNatBits_add` rewrite the
  encoding of a term to the kernel operation on encodings: the cast of a decoded configured
  value, and the absolute value, product and sum of descriptor-model values.

Every statement holds for every source, accumulator and destination descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

variable {α : Type} {acc out : FloatFormat}

/--
Encoding in `acc` of the sum, from left to right and with one rounding to nearest-even at each
addition, of the value that `state` encodes and the terms of `values` (`foldAdd_eq`).
-/
noncomputable def foldAdd (acc : FloatFormat) (term : α → Model acc) (state : Nat) :
    List α → Nat
  | [] => state
  | value :: rest =>
      foldAdd acc term (Flat.add acc .nearest state (term value).toNatBits) rest

/--
Encoding in `acc` of the sum of the terms of a tree in its association order, with one
rounding to nearest-even at each addition (`evalWord_eq`).
-/
noncomputable def evalWord (acc : FloatFormat) (term : α → Model acc) :
    ReductionTree α → Nat
  | .leaf value => (term value).toNatBits
  | .node left right =>
      Flat.add acc .nearest (evalWord acc term left) (evalWord acc term right)

/-- A reduction of no further element is the state. -/
@[kernel_optimize] theorem foldAdd_nil (term : α → Model acc) (state : Nat) :
    foldAdd acc term state [] = state :=
  Flat.rewrite_rule rfl

/-- A reduction adds its first element to the state and goes on with the rest. -/
@[kernel_optimize] theorem foldAdd_cons (term : α → Model acc) (state : Nat) (value : α)
    (rest : List α) :
    foldAdd acc term state (value :: rest) =
      foldAdd acc term (Flat.add acc .nearest state (term value).toNatBits) rest :=
  Flat.rewrite_rule rfl

/-- A leaf of a schedule is the encoding of its term. -/
@[kernel_optimize] theorem evalWord_leaf (term : α → Model acc) (value : α) :
    evalWord acc term (.leaf value) = (term value).toNatBits :=
  Flat.rewrite_rule rfl

/-- A node of a schedule adds the encodings of its two subtrees. -/
@[kernel_optimize] theorem evalWord_node (term : α → Model acc) (left right : ReductionTree α) :
    evalWord acc term (.node left right) =
      Flat.add acc .nearest (evalWord acc term left) (evalWord acc term right) :=
  Flat.rewrite_rule rfl

/-- `foldAdd` computes the encoding of the left-to-right sum of the reference. -/
theorem foldAdd_eq (term : α → Model acc) (state : Model acc) (values : List α) :
    foldAdd acc term state.toNatBits values =
      (values.foldl (fun s v => Model.add s (term v)) state).toNatBits := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
      rw [foldAdd_cons, Flat.add_eq, addShort_eq_spec, ih]
      rfl

/-- `evalWord` computes the encoding of the sum of the reference along a tree. -/
theorem evalWord_eq (term : α → Model acc) (schedule : ReductionTree α) :
    evalWord acc term schedule =
      (schedule.eval (fun x y => Model.add x y) term).toNatBits := by
  induction schedule with
  | leaf value => rfl
  | node left right ihLeft ihRight =>
      rw [evalWord_node, ihLeft, ihRight, Flat.add_eq, addShort_eq_spec]
      rfl

/--
The encoding of a reduction from left to right is the kernel cast of the chain of kernel
additions, started at the encoding of `+0`.
-/
@[kernel_optimize] theorem toNatBits_reduceInOrder (term : α → Model acc) (values : List α) :
    (Model.reduceInOrder acc out term values).toNatBits =
      Flat.cast acc out .nearest (foldAdd acc term 0 values) := by
  have hzero : (Model.zero acc false).toNatBits = 0 := toNatBits_posZero acc
  unfold Model.reduceInOrder
  rw [Flat.cast_eq, ← hzero, foldAdd_eq, cast_eq_spec]

/--
The encoding of a reduction along a tree is the kernel cast of the kernel additions along the
tree.
-/
@[kernel_optimize] theorem toNatBits_reduceAlong (term : α → Model acc)
    (schedule : ReductionTree α) :
    (Model.reduceAlong acc out term schedule).toNatBits =
      Flat.cast acc out .nearest (evalWord acc term schedule) := by
  unfold Model.reduceAlong
  rw [Flat.cast_eq, evalWord_eq, cast_eq_spec]

/-- The encoding of an absolute value is the kernel absolute value of the encoding. -/
@[kernel_optimize] theorem toNatBits_abs {fmt : FloatFormat} (x : Model fmt) :
    (Model.abs x).toNatBits = KernelPath.abs fmt x.toNatBits :=
  (abs_eq_spec x).symm

/-- The encoding of a product is the kernel product of the encodings, in every direction. -/
@[kernel_optimize] theorem toNatBits_mul {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x y : Model fmt) :
    (Model.mul x y (mode := mode)).toNatBits = Flat.mul fmt mode x.toNatBits y.toNatBits := by
  rw [Flat.mul_eq, mulFast_eq_spec]

/-- The encoding of a sum is the kernel sum of the encodings, in every direction. -/
@[kernel_optimize] theorem toNatBits_add {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x y : Model fmt) :
    (Model.add x y (mode := mode)).toNatBits = Flat.add fmt mode x.toNatBits y.toNatBits := by
  rw [Flat.add_eq, addShort_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

variable {format : FloatFormat}

/--
The encoding of the cast of a decoded configured value into any descriptor is the kernel cast
of its encoding, in every rounding direction.
-/
@[kernel_optimize] theorem toNatBits_cast_toModel {target : FloatFormat}
    {plan : StoragePlan format} (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    (Model.cast format target (FloatLib.Floats.ExecFloat.Binary.toModel x) mode).toNatBits =
      KernelPath.Flat.cast format target mode (toNat x) := by
  rw [KernelPath.Flat.cast_eq, KernelPath.toNat_eq, ← toModel_eq_natView, cast_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.Configured

/-
A literal list of pairs written as a zip is unrolled, so that the reduction over it sees the
pairs.
-/
attribute [kernel_optimize] List.zip_cons_cons List.zip_nil_left List.zip_nil_right
