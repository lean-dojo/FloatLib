/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word16.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word32.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word64.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch.Proof

/-!
# The `planned_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

set_option hygiene false in
/--
`planned_capability op for Spec.op` declares the static capability of one operation on a
    built-in storage
plan: the capability that `Plan.⟨op⟩CapabilityForPlan` builds for the plan.
-/
macro "planned_capability " lower:ident " for " specification:ident : command => do
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := specification
  let text := s!"The static `{lower.getId}` capability of a built-in storage plan, built by \
    `Plan.{lower.getId}CapabilityForPlan`."
  `($(ExecFloat.generatedDoc text):docComment
    @[always_inline] instance (priority := 1100)
        $(Lean.mkIdent (lower.getId.appendAfter "PlannedCapability"))
        (format : Format) (plan : StoragePlan format)
        [FloatLib.Floats.ExecFloat.Backend.PolicyFor
          (Family format (Code plan) plan)] :
        FloatLib.Floats.ExecFloat.Capability.Static (F := Family format (Code plan) plan)
          $operation (@$spec format plan (Code plan) inferInstance) where
      spec_eq := by cases plan <;> rfl
      capability :=
        $(Lean.mkIdent (`Plan ++ lower.getId.appendAfter "CapabilityForPlan")) format plan)

end FloatLib.Floats.Formats.Posit.Configured
