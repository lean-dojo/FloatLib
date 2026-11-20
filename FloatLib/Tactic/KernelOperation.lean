/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop -- shake: keep
public import FloatLib.Kernels.Execution.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.CastStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.ShortAddition
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.IntegerStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lift
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.LiteralStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.SqrtStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.ToRat
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.TotalOrder
public import FloatLib.Tactic.FloatDecide -- shake: keep
public import FloatLib.Tactic.KernelInline

/-!
# The `kernel_operation` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath
namespace Value

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat (Capability)

set_option hygiene false in
/--
`kernel_operation name := lift, lift_eq, toNat_lift, liftSpec, liftCongr (op, staged, model, h,
spec, specEq) for pub [args]` declares the kernel operation `name` on stored values in a rounding
direction: the definition (the operation `staged` lifted by `lift`, which Lean compiles, where
the flat `op` it equals by unfolding is for the kernel only), `name_eq_lift` (it is the reference
operation `model` in that direction carried through the family's conversions), `toNat_name` (its
encoding is `op` on the encodings of the operands, by the equation `op_eq : @op = @staged`, so
that the elaborator does not unfold the flat form) and `name_eq` (the public operation
`ExecFloat.pub` equals it in the nearest-even direction, where `specEq` says that `model` is
`spec`). `cost n` is the declared kernel cost of that rule in microseconds: the measured time of
one binary32 operation on normal operands.
-/
macro doc:docComment "kernel_operation " name:ident " := " lift:ident ", " liftEq:ident
    ", " toNatLift:ident ", " specLift:ident ", " liftCongr:ident
    " (" op:ident ", " staged:ident ", " model:ident ", " h:ident ", " spec:ident ", " specEq:ident
    ")"
    " for " pub:ident " [" args:ident* "]" " cost " cost:num : command => do
  let eqLift := Lean.mkIdent (name.getId.appendAfter "_eq_lift")
  let eqPub := Lean.mkIdent (name.getId.appendAfter "_eq")
  let toNatName := Lean.mkIdent (Lean.Name.mkSimple ("toNat_" ++ name.getId.toString))
  let opEq := Lean.mkIdent (op.getId.appendAfter "_eq")
  let pubName := Lean.mkIdent (`FloatLib.Floats.ExecFloat ++ pub.getId)
  let capName := Lean.mkIdent (`FloatLib.Floats.ExecFloat ++
    Lean.Name.mkSimple pub.getId.toString.capitalize)
  let natArgs ← args.mapM fun arg => `(toNat $arg)
  `($doc:docComment
    def $name (mode : Model.IEEERoundingMode) ($args* : FloatLib.Floats.ExecFloat F) :
        FloatLib.Floats.ExecFloat F :=
      $lift ($staged format mode) (fun $args* => $model $args* (mode := mode)) ($h mode) $args*

    /--
    The kernel operation is the reference operation in that direction, carried through the
    family's conversions.
    -/
    theorem $eqLift (mode : Model.IEEERoundingMode) ($args* : FloatLib.Floats.ExecFloat F) :
        $name mode $args* = $specLift (fun $args* => $model $args* (mode := mode)) $args* :=
      $liftEq _ _ _ $args*

    /-- The encoding of the result is the flat operation on the encodings of the operands. -/
    @[kernel_optimize] theorem $toNatName (mode : Model.IEEERoundingMode)
        ($args* : FloatLib.Floats.ExecFloat F) :
        toNat ($name mode $args*) = $op format mode $natArgs* := by
      rw [$opEq:ident]
      exact $toNatLift _ _ _ $args*

    /--
    The public operation equals the kernel operation in the nearest-even direction, for every
    family whose capability has the lifted nearest-even specification as its reference.
    -/
    @[kernel_optimize (cost := $cost)] theorem $eqPub
        [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
        [cap : $capName F] [Capability.HasSpec cap ($specLift (F := F) $spec)]
        ($args* : FloatLib.Floats.ExecFloat F) :
        $pubName $args* = $name Model.IEEERoundingMode.nearest $args* := by
      rw [$eqLift:ident, $liftCongr:ident $specEq, ← Capability.HasSpec.spec_eq (cap := cap),
        ← Capability.run_eq_spec]
      rfl)

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
