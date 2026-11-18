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
# The `status_operation` command

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
`status_operation name := flat, model, h, flatEq [args]` declares `name_status_eq_lift` and
`name_ternary_eq_lift`: the flags and the ternary value of the reference operation `model` with
`status := true` on the decoded operands are decoded from the flat status number `flat` of the
encodings, where `h` is the theorem for the staged status number and `flatEq` says that `flat`
is the staged one.
-/
macro "status_operation " name:ident " := " flat:ident ", " model:ident ", " h:ident
    ", " flatEq:ident " [" args:ident* "]" : command => do
  let statusName := Lean.mkIdent (name.getId.appendAfter "_status_eq_lift")
  let ternaryName := Lean.mkIdent (name.getId.appendAfter "_ternary_eq_lift")
  let models ← args.mapM fun arg => `(view.toModel (FloatLib.Floats.ExecFloat.raw $arg))
  let nats ← args.mapM fun arg => `(toNat $arg)
  `(/--
    The exception flags of the reference operation with `status := true` are decoded from the
    flat status number of the encodings of the operands.
    -/
    theorem $statusName (mode : Model.IEEERoundingMode)
        ($args* : FloatLib.Floats.ExecFloat F) :
        ($model $models* (mode := mode) (status := true)).status =
          decodeStatus ($flat format mode $nats*) := by
      simp only [toNat_eq, $flatEq:ident]
      exact ($h mode ..).1.symm

    /--
    The ternary value of the reference operation with `status := true` is decoded from the flat
    status number of the encodings of the operands.
    -/
    theorem $ternaryName (mode : Model.IEEERoundingMode)
        ($args* : FloatLib.Floats.ExecFloat F) :
        ($model $models* (mode := mode) (status := true)).ternary =
          decodeTernary ($flat format mode $nats*) := by
      simp only [toNat_eq, $flatEq:ident]
      exact ($h mode ..).2.symm)

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
