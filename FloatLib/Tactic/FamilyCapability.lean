/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Proof

/-!
# The `family_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

set_option hygiene false in
/--
`family_capability op "label" shape` declares, for the static-byte operation `op`, the tagged
baseline `Backend.opCertified` (the family's certified byte kernel, refining `Spec.op`, built
with `Certified.shape`) and the default instance `opCapability`, which a `TablePlan` instance
outranks.
-/
macro "family_capability " op:ident label:str shape:ident : command => do
  let spec := Lean.mkIdent (`Spec ++ op.getId)
  let kernel := Lean.mkIdent (`Backend ++ op.getId)
  let proof := Lean.mkIdent (`Backend ++ op.getId.appendAfter "_eq_spec")
  let certified := Lean.mkIdent (`Backend ++ op.getId.appendAfter "Certified")
  let instanceName := Lean.mkIdent (op.getId.appendAfter "Capability")
  let build := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Certified ++ shape.getId)
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ op.getId)
  `(/-- The family's certified byte kernel for this operation: the family's baseline. -/
    @[compiler_optimize baseline]
    def $certified (F : Type u) [Family F] :
        FloatLib.Floats.ExecFloat.Backend.Certified ($spec (F := F)) :=
      $build (Backend.familyEstimate $label) $spec $kernel $proof

    /--
    The default capability of this operation for a static-byte family: the family's certified
    byte kernel, called directly where no tagged alternative applies, and the planner's choice
    among the kernel and the tagged alternatives otherwise.
    -/
    instance (priority := 100) $instanceName
        (F : Type u) [Family F]
        [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
        @FloatLib.Floats.ExecFloat.Capability.Static F (familyEncodedFormat F) planning
          $operation ($spec (F := F)) where
      spec_eq := rfl
      capability := FloatLib.Floats.ExecFloat.Capability.ofCertified $operation ($certified F))

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
