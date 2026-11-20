/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value -- shake: keep

/-!
# The `outcome_rule` and `outcome_with_rule` commands

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath (NatView)

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
`outcome_rule name for format [args]` declares `name_outcome_eq`: the configured operation's outcome
`name` with `status := true` is the kernel value with the flags and the ternary value decoded
from the flat status number of the encodings of the operands.
-/
macro "outcome_rule " name:ident " for " format:term:max " [" args:ident* "]" : command => do
  let ruleName := Lean.mkIdent (name.getId.appendAfter "_outcome_eq")
  let model := Lean.mkIdent (`Model ++ name.getId)
  let value := Lean.mkIdent (`KernelPath.Value ++ name.getId)
  let valueLift := Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_eq_lift")
  let statusLift := Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_status_eq_lift")
  let ternaryLift :=
    Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_ternary_eq_lift")
  let valueOf := Lean.mkIdent (`Model ++ (Lean.Name.mkSimple ("value_" ++ name.getId.toString)))
  let flat := Lean.mkIdent (`KernelPath.Flat ++ name.getId.appendAfter "Status")
  let ofModel := Lean.mkIdent
    `FloatLib.Floats.Formats.BinaryInterchange.Configured.ofModel_eq_natView
  let toModel := Lean.mkIdent
    `FloatLib.Floats.Formats.BinaryInterchange.Configured.toModel_eq_natView
  let models ← args.mapM fun arg => `(FloatLib.Floats.ExecFloat.Binary.toModel $arg)
  let nats ← args.mapM fun arg => `(KernelPath.toNat $arg)
  `(/--
    The outcome of the configured operation with `status := true`: the kernel value, with the
    exception flags and the ternary value decoded from one status number.
    -/
    @[kernel_optimize] theorem $ruleName {plan : StoragePlan $format}
        (mode : Model.IEEERoundingMode)
        ($args* : FloatLib.Floats.ExecFloat (Family $format (Code plan) plan)) :
        FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
            ($model $models* (mode := mode) (status := true)) =
          { value := $value mode $args*
            status := KernelPath.decodeStatus ($flat $format mode $nats*)
            ternary := KernelPath.decodeTernary ($flat $format mode $nats*) } := by
      unfold FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel
      simp only [$valueOf:ident, $ofModel:ident, $toModel:ident, $statusLift:ident,
        $ternaryLift:ident, $valueLift:ident]
      rfl)

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
`outcome_with_rule name for format [args] cost n` declares `name_outcome_eq_with`: the rule of
`outcome_rule` with the status number taken as a function of the word of the kernel value
(`Flat.nameStatusWith`), so that Lean's kernel computes the value once for the value, the flags
and the ternary value. `n` is its declared kernel cost in microseconds, which puts it in front of
`name_outcome_eq`.
-/
macro "outcome_with_rule " name:ident " for " format:term:max " [" args:ident* "]"
    &" cost " microseconds:num : command => do
  let ruleName := Lean.mkIdent (name.getId.appendAfter "_outcome_eq_with")
  let withoutWord := Lean.mkIdent (name.getId.appendAfter "_outcome_eq")
  let model := Lean.mkIdent (`Model ++ name.getId)
  let value := Lean.mkIdent (`KernelPath.Value ++ name.getId)
  let statusWith :=
    Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_status_eq_with")
  let flat := Lean.mkIdent (`KernelPath.Flat ++ name.getId.appendAfter "StatusWith")
  let models ← args.mapM fun arg => `(FloatLib.Floats.ExecFloat.Binary.toModel $arg)
  let nats ← args.mapM fun arg => `(KernelPath.toNat $arg)
  `(/--
    The outcome of the configured operation with `status := true`: the kernel value, with the
    exception flags and the ternary value decoded from the status number at the word of that
    value.
    -/
    @[kernel_optimize (cost := $microseconds)] theorem $ruleName {plan : StoragePlan $format}
        (mode : Model.IEEERoundingMode)
        ($args* : FloatLib.Floats.ExecFloat (Family $format (Code plan) plan)) :
        FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
            ($model $models* (mode := mode) (status := true)) =
          { value := $value mode $args*
            status := KernelPath.decodeStatus
              ($flat $format mode $nats* (KernelPath.toNat ($value mode $args*)))
            ternary := KernelPath.decodeTernary
              ($flat $format mode $nats* (KernelPath.toNat ($value mode $args*))) } := by
      rw [$withoutWord:ident, $statusWith:ident])

end FloatLib.Floats.Formats.BinaryInterchange.Configured
