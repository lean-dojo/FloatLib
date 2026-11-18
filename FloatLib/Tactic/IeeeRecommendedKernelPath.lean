/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Classification.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.LogB
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Payload
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Magnitude
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# IeeeRecommendedKernelPath generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

set_option hygiene false in
/--
`code_rule name := code, proof` declares `name_eq`: the classification `ExecFloat.Binary.name`
of a configured value `x` is the test `code` on its encoding, where `proof` proves that test
equal to the model classification of the decoded value.
-/
macro (name := codeRule) doc:docComment "code_rule " name:ident " := " code:term ", " proof:ident :
    command => do
  let ruleName := Lean.mkIdent (name.getId.appendAfter "_eq")
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Binary ++ name.getId)
  `($doc:docComment
    @[kernel_optimize] theorem $ruleName {plan : StoragePlan format}
        (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
        $operation x = $code := by
      rw [KernelPath.toNat_eq, $proof:ident, ← toModel_eq_natView]
      rfl)


set_option hygiene false in
/--
`selection_rule name := model` declares `liftBinary_name_eq`: the codec lift of the model
selection `model`, which is what the configured operation `name` runs, equals the kernel
selection `KernelPath.Value.name` between the two encodings.
-/
macro (name := selectionRule) "selection_rule " name:ident " := " model:term : command => do
  let ruleName := Lean.mkIdent
    (Lean.Name.mkSimple ("liftBinary_" ++ name.getId.toString ++ "_eq"))
  let value := Lean.mkIdent (`KernelPath.Value ++ name.getId)
  let valueLift := Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_eq_lift")
  `(/--
    The selection of configured values, as the configured operation runs it through the model,
    equals the kernel selection between the two encodings.
    -/
    @[kernel_optimize] theorem $ruleName {plan : StoragePlan format}
        (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
        FloatLib.Floats.ExecFloat.ModelCodec.liftBinary (Model := Model format) (plan := plan)
            $model left right = $value left right := by
      rw [liftBinary_eq_natView, $valueLift:ident])


set_option hygiene false in
/--
`signaling_rule name := head args` declares `name_outcome_eq`: the outcome of the configured
selection `name` with `status := true`, which runs the model selection `head args` with its
`invalid` signal, is the kernel selection `KernelPath.Value.name` with the flag computed on
the two encodings.
-/
macro (name := signalingRule) "signaling_rule " name:ident " := " head:ident args:(ppSpace colGt
    term:max)* :
    command => do
  let ruleName := Lean.mkIdent (name.getId.appendAfter "_outcome_eq")
  let value := Lean.mkIdent (`KernelPath.Value ++ name.getId)
  let valueLift := Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_eq_lift")
  `(/--
    The outcome of the configured selection with `status := true`: the kernel selection between
    the two encodings, with `invalid` exactly when an encoding is a signaling NaN.
    -/
    @[kernel_optimize] theorem $ruleName {plan : StoragePlan format}
        (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
        FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
            ($head $args* (FloatLib.Floats.ExecFloat.Binary.toModel left)
              (FloatLib.Floats.ExecFloat.Binary.toModel right) (status := true)) =
          { value := $value left right
            status :=
              { invalid := Nat.beq (signalingCode format (toNat left)) 1 ||
                  Nat.beq (signalingCode format (toNat right)) 1 }
            ternary := .eq } := by
      rw [$valueLift:ident]
      exact ofModel_outcomeWithInvalid (fun x y => $head $args* x y) left right)


end FloatLib.Floats.Formats.BinaryInterchange.Configured
